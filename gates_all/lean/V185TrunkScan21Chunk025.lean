import V185TrunkScan21Chunk024

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_300473 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 5]
def baseStart_300473 : Nat := 118140960795 + 300473 * 2 ^ 59
def prefixEnd_300473 : Nat := 4983230072969 + 3 ^ 40 * 300473 * 2
def baseEnd_300473 : Nat := 68572032310448058535847

theorem tailTrace_300473 : CollatzResearch.WordTrace tailWord_300473 prefixEnd_300473 68572032310448058535847 := by
  unfold tailWord_300473
  simp only [CollatzResearch.WordTrace]
  refine ⟨10959150640445112547978073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7306100426963408365318715 10959150640445112547978073)
  ·
    refine ⟨8219362980333834410983555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10959150640445112547978073 8219362980333834410983555)
    ·
      refine ⟨12329044470500751616475333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8219362980333834410983555 12329044470500751616475333)
      ·
        refine ⟨2311695838218890928089125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12329044470500751616475333 2311695838218890928089125)
        ·
          refine ⟨433442969666042049016711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2311695838218890928089125 433442969666042049016711)
          ·
            refine ⟨650164454499063073525067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433442969666042049016711 650164454499063073525067)
            ·
              refine ⟨975246681748594610287601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650164454499063073525067 975246681748594610287601)
              ·
                refine ⟨731435011311445957715701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975246681748594610287601 731435011311445957715701)
                ·
                  refine ⟨68572032310448058535847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 731435011311445957715701 68572032310448058535847)
                  ·
                    rfl

theorem cell21_300473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_300473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300473 prefixEnd_300473 := by exact prefixLift 300473
  have htrace : WordTrace (prefixWord ++ tailWord_300473) baseStart_300473 baseEnd_300473 := by
    simpa [prefixWord, tailWord_300473, baseEnd_300473] using wordTrace_append hprefix tailTrace_300473
  have hstable : (prefixWord ++ tailWord_300473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300473).length < 2 ^ (prefixWord ++ tailWord_300473).sum := by decide
  have hdescent : baseEnd_300473 < baseStart_300473 := by decide
  rcases family_descends (prefixWord ++ tailWord_300473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300482 : List Nat := [3, 5, 2, 1, 1, 1, 2, 3, 3]
def baseStart_300482 : Nat := 118140960795 + 300482 * 2 ^ 59
def prefixEnd_300482 : Nat := 4983230072969 + 3 ^ 40 * 300482 * 2
def baseEnd_300482 : Nat := 68574086233066042885829

theorem tailTrace_300482 : CollatzResearch.WordTrace tailWord_300482 prefixEnd_300482 68574086233066042885829 := by
  unfold tailWord_300482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739869724353126771263925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7306319264941671390037133 2739869724353126771263925)
  ·
    refine ⟨256862786658105634805993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2739869724353126771263925 256862786658105634805993)
    ·
      refine ⟨192647089993579226104495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256862786658105634805993 192647089993579226104495)
      ·
        refine ⟨288970634990368839156743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192647089993579226104495 288970634990368839156743)
        ·
          refine ⟨433455952485553258735115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288970634990368839156743 433455952485553258735115)
          ·
            refine ⟨650183928728329888102673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433455952485553258735115 650183928728329888102673)
            ·
              refine ⟨487637946546247416077005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650183928728329888102673 487637946546247416077005)
              ·
                refine ⟨182864229954842781028877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487637946546247416077005 182864229954842781028877)
                ·
                  refine ⟨68574086233066042885829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182864229954842781028877 68574086233066042885829)
                  ·
                    rfl

theorem cell21_300482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_300482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300482 prefixEnd_300482 := by exact prefixLift 300482
  have htrace : WordTrace (prefixWord ++ tailWord_300482) baseStart_300482 baseEnd_300482 := by
    simpa [prefixWord, tailWord_300482, baseEnd_300482] using wordTrace_append hprefix tailTrace_300482
  have hstable : (prefixWord ++ tailWord_300482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300482).length < 2 ^ (prefixWord ++ tailWord_300482).sum := by decide
  have hdescent : baseEnd_300482 < baseStart_300482 := by decide
  rcases family_descends (prefixWord ++ tailWord_300482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300490 : List Nat := [3, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_300490 : Nat := 118140960795 + 300490 * 2 ^ 59
def prefixEnd_300490 : Nat := 4983230072969 + 3 ^ 40 * 300490 * 2
def baseEnd_300490 : Nat := 68575911942059806752479

theorem tailTrace_300490 : CollatzResearch.WordTrace tailWord_300490 prefixEnd_300490 68575911942059806752479 := by
  unfold tailWord_300490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739942670345881112836731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7306513787589016300897949 2739942670345881112836731)
  ·
    refine ⟨4109914005518821669255097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739942670345881112836731 4109914005518821669255097)
    ·
      refine ⟨3082435504139116251941323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4109914005518821669255097 3082435504139116251941323)
      ·
        refine ⟨4623653256208674377911985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082435504139116251941323 4623653256208674377911985)
        ·
          refine ⟨3467739942156505783433989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4623653256208674377911985 3467739942156505783433989)
          ·
            refine ⟨650201239154344834393873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3467739942156505783433989 650201239154344834393873)
            ·
              refine ⟨487650929365758625795405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650201239154344834393873 487650929365758625795405)
              ·
                refine ⟨182869098512159484673277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487650929365758625795405 182869098512159484673277)
                ·
                  refine ⟨68575911942059806752479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182869098512159484673277 68575911942059806752479)
                  ·
                    rfl

theorem cell21_300490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_300490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300490 prefixEnd_300490 := by exact prefixLift 300490
  have htrace : WordTrace (prefixWord ++ tailWord_300490) baseStart_300490 baseEnd_300490 := by
    simpa [prefixWord, tailWord_300490, baseEnd_300490] using wordTrace_append hprefix tailTrace_300490
  have hstable : (prefixWord ++ tailWord_300490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300490).length < 2 ^ (prefixWord ++ tailWord_300490).sum := by decide
  have hdescent : baseEnd_300490 < baseStart_300490 := by decide
  rcases family_descends (prefixWord ++ tailWord_300490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300501 : List Nat := [1, 3, 2, 3, 1, 1, 10]
def baseStart_300501 : Nat := 118140960795 + 300501 * 2 ^ 59
def prefixEnd_300501 : Nat := 4983230072969 + 3 ^ 40 * 300501 * 2
def baseEnd_300501 : Nat := 7619824699102914674347

theorem tailTrace_300501 : CollatzResearch.WordTrace tailWord_300501 prefixEnd_300501 7619824699102914674347 := by
  unfold tailWord_300501
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960171884343673329997357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7306781256229115553331571 10960171884343673329997357)
  ·
    refine ⟨4110064456628877498749009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10960171884343673329997357 4110064456628877498749009)
    ·
      refine ⟨3082548342471658124061757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4110064456628877498749009 3082548342471658124061757)
      ·
        refine ⟨1155955628426871796523159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3082548342471658124061757 1155955628426871796523159)
        ·
          refine ⟨1733933442640307694784739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155955628426871796523159 1733933442640307694784739)
          ·
            refine ⟨2600900163960461542177109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733933442640307694784739 2600900163960461542177109)
            ·
              refine ⟨7619824699102914674347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2600900163960461542177109 7619824699102914674347)
              ·
                rfl

theorem cell21_300501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 10].length) (baseStart_300501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300501 prefixEnd_300501 := by exact prefixLift 300501
  have htrace : WordTrace (prefixWord ++ tailWord_300501) baseStart_300501 baseEnd_300501 := by
    simpa [prefixWord, tailWord_300501, baseEnd_300501] using wordTrace_append hprefix tailTrace_300501
  have hstable : (prefixWord ++ tailWord_300501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300501).length < 2 ^ (prefixWord ++ tailWord_300501).sum := by decide
  have hdescent : baseEnd_300501 < baseStart_300501 := by decide
  rcases family_descends (prefixWord ++ tailWord_300501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300577 : List Nat := [1, 2, 3, 2, 2, 2, 1, 8]
def baseStart_300577 : Nat := 118140960795 + 300577 * 2 ^ 59
def prefixEnd_300577 : Nat := 4983230072969 + 3 ^ 40 * 300577 * 2
def baseEnd_300577 : Nat := 22865255509122329600767

theorem tailTrace_300577 : CollatzResearch.WordTrace tailWord_300577 prefixEnd_300577 22865255509122329600767 := by
  unfold tailWord_300577
  simp only [CollatzResearch.WordTrace]
  refine ⟨10962943832068338309763985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7308629221378892206509323 10962943832068338309763985)
  ·
    refine ⟨8222207874051253732322989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10962943832068338309763985 8222207874051253732322989)
    ·
      refine ⟨3083327952769220149621121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8222207874051253732322989 3083327952769220149621121)
      ·
        refine ⟨2312495964576915112215841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3083327952769220149621121 2312495964576915112215841)
        ·
          refine ⟨1734371973432686334161881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2312495964576915112215841 1734371973432686334161881)
          ·
            refine ⟨1300778980074514750621411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734371973432686334161881 1300778980074514750621411)
            ·
              refine ⟨1951168470111772125932117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300778980074514750621411 1951168470111772125932117)
              ·
                refine ⟨22865255509122329600767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1951168470111772125932117 22865255509122329600767)
                ·
                  rfl

theorem cell21_300577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 8].length) (baseStart_300577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300577 prefixEnd_300577 := by exact prefixLift 300577
  have htrace : WordTrace (prefixWord ++ tailWord_300577) baseStart_300577 baseEnd_300577 := by
    simpa [prefixWord, tailWord_300577, baseEnd_300577] using wordTrace_append hprefix tailTrace_300577
  have hstable : (prefixWord ++ tailWord_300577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300577).length < 2 ^ (prefixWord ++ tailWord_300577).sum := by decide
  have hdescent : baseEnd_300577 < baseStart_300577 := by decide
  rcases family_descends (prefixWord ++ tailWord_300577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300614 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_300614 : Nat := 118140960795 + 300614 * 2 ^ 59
def prefixEnd_300614 : Nat := 4983230072969 + 3 ^ 40 * 300614 * 2
def baseEnd_300614 : Nat := 68604210431463146685559

theorem tailTrace_300614 : CollatzResearch.WordTrace tailWord_300614 prefixEnd_300614 68604210431463146685559 := by
  unfold tailWord_300614
  simp only [CollatzResearch.WordTrace]
  refine ⟨342634166654196675901903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7309528888622862419240597 342634166654196675901903)
  ·
    refine ⟨513951249981295013852855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342634166654196675901903 513951249981295013852855)
    ·
      refine ⟨770926874971942520779283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513951249981295013852855 770926874971942520779283)
      ·
        refine ⟨1156390312457913781168925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770926874971942520779283 1156390312457913781168925)
        ·
          refine ⟨433646367171717667938347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1156390312457913781168925 433646367171717667938347)
          ·
            refine ⟨650469550757576501907521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433646367171717667938347 650469550757576501907521)
            ·
              refine ⟨487852163068182376430641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650469550757576501907521 487852163068182376430641)
              ·
                refine ⟨365889122301136782322981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487852163068182376430641 365889122301136782322981)
                ·
                  refine ⟨68604210431463146685559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 365889122301136782322981 68604210431463146685559)
                  ·
                    rfl

theorem cell21_300614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_300614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300614 prefixEnd_300614 := by exact prefixLift 300614
  have htrace : WordTrace (prefixWord ++ tailWord_300614) baseStart_300614 baseEnd_300614 := by
    simpa [prefixWord, tailWord_300614, baseEnd_300614] using wordTrace_append hprefix tailTrace_300614
  have hstable : (prefixWord ++ tailWord_300614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300614).length < 2 ^ (prefixWord ++ tailWord_300614).sum := by decide
  have hdescent : baseEnd_300614 < baseStart_300614 := by decide
  rcases family_descends (prefixWord ++ tailWord_300614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300625 : List Nat := [1, 2, 2, 1, 3, 2, 3, 4, 3]
def baseStart_300625 : Nat := 118140960795 + 300625 * 2 ^ 59
def prefixEnd_300625 : Nat := 4983230072969 + 3 ^ 40 * 300625 * 2
def baseEnd_300625 : Nat := 68606720781329572002203

theorem tailTrace_300625 : CollatzResearch.WordTrace tailWord_300625 prefixEnd_300625 68606720781329572002203 := by
  unfold tailWord_300625
  simp only [CollatzResearch.WordTrace]
  refine ⟨10964694535894442507511329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7309796357262961671674219 10964694535894442507511329)
  ·
    refine ⟨8223520901920831880633497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10964694535894442507511329 8223520901920831880633497)
    ·
      refine ⟨6167640676440623910475123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8223520901920831880633497 6167640676440623910475123)
      ·
        refine ⟨9251461014660935865712685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6167640676440623910475123 9251461014660935865712685)
        ·
          refine ⟨3469297880497850949642257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9251461014660935865712685 3469297880497850949642257)
          ·
            refine ⟨2601973410373388212231693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3469297880497850949642257 2601973410373388212231693)
            ·
              refine ⟨975740028890020579586885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2601973410373388212231693 975740028890020579586885)
              ·
                refine ⟨182951255416878858672541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 975740028890020579586885 182951255416878858672541)
                ·
                  refine ⟨68606720781329572002203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 182951255416878858672541 68606720781329572002203)
                  ·
                    rfl

theorem cell21_300625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_300625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300625 prefixEnd_300625 := by exact prefixLift 300625
  have htrace : WordTrace (prefixWord ++ tailWord_300625) baseStart_300625 baseEnd_300625 := by
    simpa [prefixWord, tailWord_300625, baseEnd_300625] using wordTrace_append hprefix tailTrace_300625
  have hstable : (prefixWord ++ tailWord_300625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300625).length < 2 ^ (prefixWord ++ tailWord_300625).sum := by decide
  have hdescent : baseEnd_300625 < baseStart_300625 := by decide
  rcases family_descends (prefixWord ++ tailWord_300625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300667 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 7]
def baseStart_300667 : Nat := 118140960795 + 300667 * 2 ^ 59
def prefixEnd_300667 : Nat := 4983230072969 + 3 ^ 40 * 300667 * 2
def baseEnd_300667 : Nat := 68616305753546832302117

theorem tailTrace_300667 : CollatzResearch.WordTrace tailWord_300667 prefixEnd_300667 68616305753546832302117 := by
  unfold tailWord_300667
  simp only [CollatzResearch.WordTrace]
  refine ⟨10966226401742283680540255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7310817601161522453693503 10966226401742283680540255)
  ·
    refine ⟨16449339602613425520810383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10966226401742283680540255 16449339602613425520810383)
    ·
      refine ⟨24674009403920138281215575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16449339602613425520810383 24674009403920138281215575)
      ·
        refine ⟨37011014105880207421823363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24674009403920138281215575 37011014105880207421823363)
        ·
          refine ⟨55516521158820311132735045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37011014105880207421823363 55516521158820311132735045)
          ·
            refine ⟨10409347717278808337387821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55516521158820311132735045 10409347717278808337387821)
            ·
              refine ⟨3903505393979553126520433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10409347717278808337387821 3903505393979553126520433)
              ·
                refine ⟨2927629045484664844890325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3903505393979553126520433 2927629045484664844890325)
                ·
                  refine ⟨68616305753546832302117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2927629045484664844890325 68616305753546832302117)
                  ·
                    rfl

theorem cell21_300667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_300667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300667 prefixEnd_300667 := by exact prefixLift 300667
  have htrace : WordTrace (prefixWord ++ tailWord_300667) baseStart_300667 baseEnd_300667 := by
    simpa [prefixWord, tailWord_300667, baseEnd_300667] using wordTrace_append hprefix tailTrace_300667
  have hstable : (prefixWord ++ tailWord_300667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300667).length < 2 ^ (prefixWord ++ tailWord_300667).sum := by decide
  have hdescent : baseEnd_300667 < baseStart_300667 := by decide
  rcases family_descends (prefixWord ++ tailWord_300667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300684 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_300684 : Nat := 118140960795 + 300684 * 2 ^ 59
def prefixEnd_300684 : Nat := 4983230072969 + 3 ^ 40 * 300684 * 2
def baseEnd_300684 : Nat := 68620185385158580518749

theorem tailTrace_300684 : CollatzResearch.WordTrace tailWord_300684 prefixEnd_300684 68620185385158580518749 := by
  unfold tailWord_300684
  simp only [CollatzResearch.WordTrace]
  refine ⟨5483423221340347791954553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7311230961787130389272737 5483423221340347791954553)
  ·
    refine ⟨4112567416005260843965915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5483423221340347791954553 4112567416005260843965915)
    ·
      refine ⟨6168851124007891265948873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4112567416005260843965915 6168851124007891265948873)
      ·
        refine ⟨4626638343005918449461655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6168851124007891265948873 4626638343005918449461655)
        ·
          refine ⟨6939957514508877674192483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4626638343005918449461655 6939957514508877674192483)
          ·
            refine ⟨10409936271763316511288725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939957514508877674192483 10409936271763316511288725)
            ·
              refine ⟨487965762738905461466659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10409936271763316511288725 487965762738905461466659)
              ·
                refine ⟨731948644108358192199989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487965762738905461466659 731948644108358192199989)
                ·
                  refine ⟨68620185385158580518749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 731948644108358192199989 68620185385158580518749)
                  ·
                    rfl

theorem cell21_300684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_300684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300684 prefixEnd_300684 := by exact prefixLift 300684
  have htrace : WordTrace (prefixWord ++ tailWord_300684) baseStart_300684 baseEnd_300684 := by
    simpa [prefixWord, tailWord_300684, baseEnd_300684] using wordTrace_append hprefix tailTrace_300684
  have hstable : (prefixWord ++ tailWord_300684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300684).length < 2 ^ (prefixWord ++ tailWord_300684).sum := by decide
  have hdescent : baseEnd_300684 < baseStart_300684 := by decide
  rcases family_descends (prefixWord ++ tailWord_300684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300746 : List Nat := [3, 1, 2, 1, 5, 1, 2, 6]
def baseStart_300746 : Nat := 118140960795 + 300746 * 2 ^ 59
def prefixEnd_300746 : Nat := 4983230072969 + 3 ^ 40 * 300746 * 2
def baseEnd_300746 : Nat := 22878111543286750161763

theorem tailTrace_300746 : CollatzResearch.WordTrace tailWord_300746 prefixEnd_300746 22878111543286750161763 := by
  unfold tailWord_300746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742276942114020043166523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7312738512304053448444061 2742276942114020043166523)
  ·
    refine ⟨4113415413171030064749785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2742276942114020043166523 4113415413171030064749785)
    ·
      refine ⟨3085061559878272548562339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4113415413171030064749785 3085061559878272548562339)
      ·
        refine ⟨4627592339817408822843509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3085061559878272548562339 4627592339817408822843509)
        ·
          refine ⟨433836781857882077141579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4627592339817408822843509 433836781857882077141579)
          ·
            refine ⟨650755172786823115712369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433836781857882077141579 650755172786823115712369)
            ·
              refine ⟨488066379590117336784277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650755172786823115712369 488066379590117336784277)
              ·
                refine ⟨22878111543286750161763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 488066379590117336784277 22878111543286750161763)
                ·
                  rfl

theorem cell21_300746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_300746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300746 prefixEnd_300746 := by exact prefixLift 300746
  have htrace : WordTrace (prefixWord ++ tailWord_300746) baseStart_300746 baseEnd_300746 := by
    simpa [prefixWord, tailWord_300746, baseEnd_300746] using wordTrace_append hprefix tailTrace_300746
  have hstable : (prefixWord ++ tailWord_300746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300746).length < 2 ^ (prefixWord ++ tailWord_300746).sum := by decide
  have hdescent : baseEnd_300746 < baseStart_300746 := by decide
  rcases family_descends (prefixWord ++ tailWord_300746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300749 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 4]
def baseStart_300749 : Nat := 118140960795 + 300749 * 2 ^ 59
def prefixEnd_300749 : Nat := 4983230072969 + 3 ^ 40 * 300749 * 2
def baseEnd_300749 : Nat := 68635019270732911935283

theorem tailTrace_300749 : CollatzResearch.WordTrace tailWord_300749 prefixEnd_300749 68635019270732911935283 := by
  unfold tailWord_300749
  simp only [CollatzResearch.WordTrace]
  refine ⟨10969217187445211685025301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7312811458296807790016867 10969217187445211685025301)
  ·
    refine ⟨514182055661494297735561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10969217187445211685025301 514182055661494297735561)
    ·
      refine ⟨385636541746120723301671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 514182055661494297735561 385636541746120723301671)
      ·
        refine ⟨578454812619181084952507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385636541746120723301671 578454812619181084952507)
        ·
          refine ⟨867682218928771627428761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578454812619181084952507 867682218928771627428761)
          ·
            refine ⟨650761664196578720571571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 867682218928771627428761 650761664196578720571571)
            ·
              refine ⟨976142496294868080857357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650761664196578720571571 976142496294868080857357)
              ·
                refine ⟨366053436110575530321509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 976142496294868080857357 366053436110575530321509)
                ·
                  refine ⟨68635019270732911935283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366053436110575530321509 68635019270732911935283)
                  ·
                    rfl

theorem cell21_300749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_300749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300749 prefixEnd_300749 := by exact prefixLift 300749
  have htrace : WordTrace (prefixWord ++ tailWord_300749) baseStart_300749 baseEnd_300749 := by
    simpa [prefixWord, tailWord_300749, baseEnd_300749] using wordTrace_append hprefix tailTrace_300749
  have hstable : (prefixWord ++ tailWord_300749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300749).length < 2 ^ (prefixWord ++ tailWord_300749).sum := by decide
  have hdescent : baseEnd_300749 < baseStart_300749 := by decide
  rcases family_descends (prefixWord ++ tailWord_300749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300853 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 5]
def baseStart_300853 : Nat := 118140960795 + 300853 * 2 ^ 59
def prefixEnd_300853 : Nat := 4983230072969 + 3 ^ 40 * 300853 * 2
def baseEnd_300853 : Nat := 68658753487651842201737

theorem tailTrace_300853 : CollatzResearch.WordTrace tailWord_300853 prefixEnd_300853 68658753487651842201737 := by
  unfold tailWord_300853
  simp only [CollatzResearch.WordTrace]
  refine ⟨10973010379068437446811213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7315340252712291631207475 10973010379068437446811213)
  ·
    refine ⟨4114878892150664042554205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10973010379068437446811213 4114878892150664042554205)
    ·
      refine ⟨1543079584556499015957827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4114878892150664042554205 1543079584556499015957827)
      ·
        refine ⟨2314619376834748523936741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543079584556499015957827 2314619376834748523936741)
        ·
          refine ⟨433991133156515348238139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2314619376834748523936741 433991133156515348238139)
          ·
            refine ⟨650986699734773022357209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433991133156515348238139 650986699734773022357209)
            ·
              refine ⟨488240024801079766767907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650986699734773022357209 488240024801079766767907)
              ·
                refine ⟨732360037201619650151861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488240024801079766767907 732360037201619650151861)
                ·
                  refine ⟨68658753487651842201737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 732360037201619650151861 68658753487651842201737)
                  ·
                    rfl

theorem cell21_300853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_300853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300853 prefixEnd_300853 := by exact prefixLift 300853
  have htrace : WordTrace (prefixWord ++ tailWord_300853) baseStart_300853 baseEnd_300853 := by
    simpa [prefixWord, tailWord_300853, baseEnd_300853] using wordTrace_append hprefix tailTrace_300853
  have hstable : (prefixWord ++ tailWord_300853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300853).length < 2 ^ (prefixWord ++ tailWord_300853).sum := by decide
  have hdescent : baseEnd_300853 < baseStart_300853 := by decide
  rcases family_descends (prefixWord ++ tailWord_300853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300870 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_300870 : Nat := 118140960795 + 300870 * 2 ^ 59
def prefixEnd_300870 : Nat := 4983230072969 + 3 ^ 40 * 300870 * 2
def baseEnd_300870 : Nat := 68662633119263590418369

theorem tailTrace_300870 : CollatzResearch.WordTrace tailWord_300870 prefixEnd_300870 68662633119263590418369 := by
  unfold tailWord_300870
  simp only [CollatzResearch.WordTrace]
  refine ⟨342925950625214042193127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7315753613337899566786709 342925950625214042193127)
  ·
    refine ⟨514388925937821063289691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342925950625214042193127 514388925937821063289691)
    ·
      refine ⟨771583388906731594934537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 514388925937821063289691 771583388906731594934537)
      ·
        refine ⟨578687541680048696200903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771583388906731594934537 578687541680048696200903)
        ·
          refine ⟨868031312520073044301355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578687541680048696200903 868031312520073044301355)
          ·
            refine ⟨1302046968780109566452033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868031312520073044301355 1302046968780109566452033)
            ·
              refine ⟨976535226585082174839025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302046968780109566452033 976535226585082174839025)
              ·
                refine ⟨732401419938811631129269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976535226585082174839025 732401419938811631129269)
                ·
                  refine ⟨68662633119263590418369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 732401419938811631129269 68662633119263590418369)
                  ·
                    rfl

theorem cell21_300870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_300870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300870 prefixEnd_300870 := by exact prefixLift 300870
  have htrace : WordTrace (prefixWord ++ tailWord_300870) baseStart_300870 baseEnd_300870 := by
    simpa [prefixWord, tailWord_300870, baseEnd_300870] using wordTrace_append hprefix tailTrace_300870
  have hstable : (prefixWord ++ tailWord_300870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300870).length < 2 ^ (prefixWord ++ tailWord_300870).sum := by decide
  have hdescent : baseEnd_300870 < baseStart_300870 := by decide
  rcases family_descends (prefixWord ++ tailWord_300870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300881 : List Nat := [1, 2, 2, 1, 5, 2, 1, 7]
def baseStart_300881 : Nat := 118140960795 + 300881 * 2 ^ 59
def prefixEnd_300881 : Nat := 4983230072969 + 3 ^ 40 * 300881 * 2
def baseEnd_300881 : Nat := 22888381156376671911671

theorem tailTrace_300881 : CollatzResearch.WordTrace tailWord_300881 prefixEnd_300881 22888381156376671911671 := by
  unfold tailWord_300881
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974031622966998228830497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7316021081977998819220331 10974031622966998228830497)
  ·
    refine ⟨8230523717225248671622873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10974031622966998228830497 8230523717225248671622873)
    ·
      refine ⟨6172892787918936503717155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8230523717225248671622873 6172892787918936503717155)
      ·
        refine ⟨9259339181878404755575733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6172892787918936503717155 9259339181878404755575733)
        ·
          refine ⟨868063048301100445835225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9259339181878404755575733 868063048301100445835225)
          ·
            refine ⟨651047286225825334376419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 868063048301100445835225 651047286225825334376419)
            ·
              refine ⟨976570929338738001564629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651047286225825334376419 976570929338738001564629)
              ·
                refine ⟨22888381156376671911671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 976570929338738001564629 22888381156376671911671)
                ·
                  rfl

theorem cell21_300881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 7].length) (baseStart_300881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300881 prefixEnd_300881 := by exact prefixLift 300881
  have htrace : WordTrace (prefixWord ++ tailWord_300881) baseStart_300881 baseEnd_300881 := by
    simpa [prefixWord, tailWord_300881, baseEnd_300881] using wordTrace_append hprefix tailTrace_300881
  have hstable : (prefixWord ++ tailWord_300881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300881).length < 2 ^ (prefixWord ++ tailWord_300881).sum := by decide
  have hdescent : baseEnd_300881 < baseStart_300881 := by decide
  rcases family_descends (prefixWord ++ tailWord_300881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300887 : List Nat := [1, 1, 3, 2, 6, 1, 1, 3, 3]
def baseStart_300887 : Nat := 118140960795 + 300887 * 2 ^ 59
def prefixEnd_300887 : Nat := 4983230072969 + 3 ^ 40 * 300887 * 2
def baseEnd_300887 : Nat := 68666512750875338635001

theorem tailTrace_300887 : CollatzResearch.WordTrace tailWord_300887 prefixEnd_300887 68666512750875338635001 := by
  unfold tailWord_300887
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974250460945261253548915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7316166973963507502365943 10974250460945261253548915)
  ·
    refine ⟨16461375691417891880323373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10974250460945261253548915 16461375691417891880323373)
    ·
      refine ⟨6173015884281709455121265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16461375691417891880323373 6173015884281709455121265)
      ·
        refine ⟨4629761913211282091340949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6173015884281709455121265 4629761913211282091340949)
        ·
          refine ⟨217020089681778848031607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4629761913211282091340949 217020089681778848031607)
          ·
            refine ⟨325530134522668272047411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217020089681778848031607 325530134522668272047411)
            ·
              refine ⟨488295201784002408071117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325530134522668272047411 488295201784002408071117)
              ·
                refine ⟨183110700669000903026669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 488295201784002408071117 183110700669000903026669)
                ·
                  refine ⟨68666512750875338635001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183110700669000903026669 68666512750875338635001)
                  ·
                    rfl

theorem cell21_300887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 3].length) (baseStart_300887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300887 prefixEnd_300887 := by exact prefixLift 300887
  have htrace : WordTrace (prefixWord ++ tailWord_300887) baseStart_300887 baseEnd_300887 := by
    simpa [prefixWord, tailWord_300887, baseEnd_300887] using wordTrace_append hprefix tailTrace_300887
  have hstable : (prefixWord ++ tailWord_300887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300887).length < 2 ^ (prefixWord ++ tailWord_300887).sum := by decide
  have hdescent : baseEnd_300887 < baseStart_300887 := by decide
  rcases family_descends (prefixWord ++ tailWord_300887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300898 : List Nat := [3, 3, 2, 1, 2, 3, 7]
def baseStart_300898 : Nat := 118140960795 + 300898 * 2 ^ 59
def prefixEnd_300898 : Nat := 4983230072969 + 3 ^ 40 * 300898 * 2
def baseEnd_300898 : Nat := 7629891455637973772405

theorem tailTrace_300898 : CollatzResearch.WordTrace tailWord_300898 prefixEnd_300898 7629891455637973772405 := by
  unfold tailWord_300898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2743662915976352533049837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7316434442603606754799565 2743662915976352533049837)
  ·
    refine ⟨1028873593491132199893689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2743662915976352533049837 1028873593491132199893689)
    ·
      refine ⟨771655195118349149920267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1028873593491132199893689 771655195118349149920267)
      ·
        refine ⟨1157482792677523724880401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771655195118349149920267 1157482792677523724880401)
        ·
          refine ⟨868112094508142793660301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1157482792677523724880401 868112094508142793660301)
          ·
            refine ⟨325542035440553547622613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 868112094508142793660301 325542035440553547622613)
            ·
              refine ⟨7629891455637973772405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 325542035440553547622613 7629891455637973772405)
              ·
                rfl

theorem cell21_300898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 7].length) (baseStart_300898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300898 prefixEnd_300898 := by exact prefixLift 300898
  have htrace : WordTrace (prefixWord ++ tailWord_300898) baseStart_300898 baseEnd_300898 := by
    simpa [prefixWord, tailWord_300898, baseEnd_300898] using wordTrace_append hprefix tailTrace_300898
  have hstable : (prefixWord ++ tailWord_300898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300898).length < 2 ^ (prefixWord ++ tailWord_300898).sum := by decide
  have hdescent : baseEnd_300898 < baseStart_300898 := by decide
  rcases family_descends (prefixWord ++ tailWord_300898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300918 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_300918 : Nat := 118140960795 + 300918 * 2 ^ 59
def prefixEnd_300918 : Nat := 4983230072969 + 3 ^ 40 * 300918 * 2
def baseEnd_300918 : Nat := 68673587373226173618271

theorem tailTrace_300918 : CollatzResearch.WordTrace tailWord_300918 prefixEnd_300918 68673587373226173618271 := by
  unfold tailWord_300918
  simp only [CollatzResearch.WordTrace]
  refine ⟨685961320239559596745463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7316920749221969031951605 685961320239559596745463)
  ·
    refine ⟨1028941980359339395118195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 685961320239559596745463 1028941980359339395118195)
    ·
      refine ⟨1543412970539009092677293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1028941980359339395118195 1543412970539009092677293)
      ·
        refine ⟨578779863952128409753985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1543412970539009092677293 578779863952128409753985)
        ·
          refine ⟨434084897964096307315489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578779863952128409753985 434084897964096307315489)
          ·
            refine ⟨325563673473072230486617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434084897964096307315489 325563673473072230486617)
            ·
              refine ⟨244172755104804172864963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325563673473072230486617 244172755104804172864963)
              ·
                refine ⟨366259132657206259297445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244172755104804172864963 366259132657206259297445)
                ·
                  refine ⟨68673587373226173618271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366259132657206259297445 68673587373226173618271)
                  ·
                    rfl

theorem cell21_300918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_300918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_300918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_300918 prefixEnd_300918 := by exact prefixLift 300918
  have htrace : WordTrace (prefixWord ++ tailWord_300918) baseStart_300918 baseEnd_300918 := by
    simpa [prefixWord, tailWord_300918, baseEnd_300918] using wordTrace_append hprefix tailTrace_300918
  have hstable : (prefixWord ++ tailWord_300918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300918).length < 2 ^ (prefixWord ++ tailWord_300918).sum := by decide
  have hdescent : baseEnd_300918 < baseStart_300918 := by decide
  rcases family_descends (prefixWord ++ tailWord_300918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301016 : List Nat := [2, 1, 2, 2, 2, 2, 10]
def baseStart_301016 : Nat := 118140960795 + 301016 * 2 ^ 59
def prefixEnd_301016 : Nat := 4983230072969 + 3 ^ 40 * 301016 * 2
def baseEnd_301016 : Nat := 7632883589822197887193

theorem tailTrace_301016 : CollatzResearch.WordTrace tailWord_301016 prefixEnd_301016 7632883589822197887193 := by
  unfold tailWord_301016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5489477738738958142497451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7319303651651944189996601 5489477738738958142497451)
  ·
    refine ⟨8234216608108437213746177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5489477738738958142497451 8234216608108437213746177)
    ·
      refine ⟨6175662456081327910309633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8234216608108437213746177 6175662456081327910309633)
      ·
        refine ⟨4631746842060995932732225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6175662456081327910309633 4631746842060995932732225)
        ·
          refine ⟨3473810131545746949549169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4631746842060995932732225 3473810131545746949549169)
          ·
            refine ⟨2605357598659310212161877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3473810131545746949549169 2605357598659310212161877)
            ·
              refine ⟨7632883589822197887193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2605357598659310212161877 7632883589822197887193)
              ·
                rfl

theorem cell21_301016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 10].length) (baseStart_301016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301016 prefixEnd_301016 := by exact prefixLift 301016
  have htrace : WordTrace (prefixWord ++ tailWord_301016) baseStart_301016 baseEnd_301016 := by
    simpa [prefixWord, tailWord_301016, baseEnd_301016] using wordTrace_append hprefix tailTrace_301016
  have hstable : (prefixWord ++ tailWord_301016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301016).length < 2 ^ (prefixWord ++ tailWord_301016).sum := by decide
  have hdescent : baseEnd_301016 < baseStart_301016 := by decide
  rcases family_descends (prefixWord ++ tailWord_301016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301174 : List Nat := [5, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_301174 : Nat := 118140960795 + 301174 * 2 ^ 59
def prefixEnd_301174 : Nat := 4983230072969 + 3 ^ 40 * 301174 * 2
def baseEnd_301174 : Nat := 68732010061026617351081

theorem tailTrace_301174 : CollatzResearch.WordTrace tailWord_301174 prefixEnd_301174 68732010061026617351081 := by
  unfold tailWord_301174
  simp only [CollatzResearch.WordTrace]
  refine ⟨686544888181594329327911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7323145473937006179497717 686544888181594329327911)
  ·
    refine ⟨1029817332272391493991867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 686544888181594329327911 1029817332272391493991867)
    ·
      refine ⟨1544725998408587240987801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029817332272391493991867 1544725998408587240987801)
      ·
        refine ⟨1158544498806440430740851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1544725998408587240987801 1158544498806440430740851)
        ·
          refine ⟨1737816748209660646111277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158544498806440430740851 1737816748209660646111277)
          ·
            refine ⟨651681280578622742291729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1737816748209660646111277 651681280578622742291729)
            ·
              refine ⟨488760960433967056718797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651681280578622742291729 488760960433967056718797)
              ·
                refine ⟨183285360162737646269549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 488760960433967056718797 183285360162737646269549)
                ·
                  refine ⟨68732010061026617351081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183285360162737646269549 68732010061026617351081)
                  ·
                    rfl

theorem cell21_301174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_301174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301174 prefixEnd_301174 := by exact prefixLift 301174
  have htrace : WordTrace (prefixWord ++ tailWord_301174) baseStart_301174 baseEnd_301174 := by
    simpa [prefixWord, tailWord_301174, baseEnd_301174] using wordTrace_append hprefix tailTrace_301174
  have hstable : (prefixWord ++ tailWord_301174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301174).length < 2 ^ (prefixWord ++ tailWord_301174).sum := by decide
  have hdescent : baseEnd_301174 < baseStart_301174 := by decide
  rcases family_descends (prefixWord ++ tailWord_301174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301185 : List Nat := [1, 2, 4, 2, 3, 1, 8]
def baseStart_301185 : Nat := 118140960795 + 301185 * 2 ^ 59
def prefixEnd_301185 : Nat := 4983230072969 + 3 ^ 40 * 301185 * 2
def baseEnd_301185 : Nat := 7637168934543671407525

theorem tailTrace_301185 : CollatzResearch.WordTrace tailWord_301185 prefixEnd_301185 7637168934543671407525 := by
  unfold tailWord_301185
  simp only [CollatzResearch.WordTrace]
  refine ⟨10985119413865658147897009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7323412942577105431931339 10985119413865658147897009)
  ·
    refine ⟨8238839560399243610922757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10985119413865658147897009 8238839560399243610922757)
    ·
      refine ⟨1544782417574858177048017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8238839560399243610922757 1544782417574858177048017)
      ·
        refine ⟨1158586813181143632786013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1544782417574858177048017 1158586813181143632786013)
        ·
          refine ⟨434470054942928862294755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1158586813181143632786013 434470054942928862294755)
          ·
            refine ⟨651705082414393293442133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434470054942928862294755 651705082414393293442133)
            ·
              refine ⟨7637168934543671407525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 651705082414393293442133 7637168934543671407525)
              ·
                rfl

theorem cell21_301185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 8].length) (baseStart_301185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301185 prefixEnd_301185 := by exact prefixLift 301185
  have htrace : WordTrace (prefixWord ++ tailWord_301185) baseStart_301185 baseEnd_301185 := by
    simpa [prefixWord, tailWord_301185, baseEnd_301185] using wordTrace_append hprefix tailTrace_301185
  have hstable : (prefixWord ++ tailWord_301185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301185).length < 2 ^ (prefixWord ++ tailWord_301185).sum := by decide
  have hdescent : baseEnd_301185 < baseStart_301185 := by decide
  rcases family_descends (prefixWord ++ tailWord_301185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301236 : List Nat := [2, 5, 3, 1, 1, 2, 7]
def baseStart_301236 : Nat := 118140960795 + 301236 * 2 ^ 59
def prefixEnd_301236 : Nat := 4983230072969 + 3 ^ 40 * 301236 * 2
def baseEnd_301236 : Nat := 7638462145080920813069

theorem tailTrace_301236 : CollatzResearch.WordTrace tailWord_301236 prefixEnd_301236 7638462145080920813069 := by
  unfold tailWord_301236
  simp only [CollatzResearch.WordTrace]
  refine ⟨5493489768340446929001781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7324653024453929238669041 5493489768340446929001781)
  ·
    refine ⟨515014665781916899593917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5493489768340446929001781 515014665781916899593917)
    ·
      refine ⟨193130499668218837347719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 515014665781916899593917 193130499668218837347719)
      ·
        refine ⟨289695749502328256021579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193130499668218837347719 289695749502328256021579)
        ·
          refine ⟨434543624253492384032369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289695749502328256021579 434543624253492384032369)
          ·
            refine ⟨325907718190119288024277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434543624253492384032369 325907718190119288024277)
            ·
              refine ⟨7638462145080920813069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 325907718190119288024277 7638462145080920813069)
              ·
                rfl

theorem cell21_301236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 7].length) (baseStart_301236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301236 prefixEnd_301236 := by exact prefixLift 301236
  have htrace : WordTrace (prefixWord ++ tailWord_301236) baseStart_301236 baseEnd_301236 := by
    simpa [prefixWord, tailWord_301236, baseEnd_301236] using wordTrace_append hprefix tailTrace_301236
  have hstable : (prefixWord ++ tailWord_301236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301236).length < 2 ^ (prefixWord ++ tailWord_301236).sum := by decide
  have hdescent : baseEnd_301236 < baseStart_301236 := by decide
  rcases family_descends (prefixWord ++ tailWord_301236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301250 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_301250 : Nat := 118140960795 + 301250 * 2 ^ 59
def prefixEnd_301250 : Nat := 4983230072969 + 3 ^ 40 * 301250 * 2
def baseEnd_301250 : Nat := 68749354296467374084259

theorem tailTrace_301250 : CollatzResearch.WordTrace tailWord_301250 prefixEnd_301250 68749354296467374084259 := by
  unfold tailWord_301250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746872539657543562253301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7324993439086782832675469 2746872539657543562253301)
  ·
    refine ⟨257519300592894708961247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2746872539657543562253301 257519300592894708961247)
    ·
      refine ⟨386278950889342063441871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257519300592894708961247 386278950889342063441871)
      ·
        refine ⟨579418426334013095162807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386278950889342063441871 579418426334013095162807)
        ·
          refine ⟨869127639501019642744211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579418426334013095162807 869127639501019642744211)
          ·
            refine ⟨1303691459251529464116317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869127639501019642744211 1303691459251529464116317)
            ·
              refine ⟨488884297219323549043619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1303691459251529464116317 488884297219323549043619)
              ·
                refine ⟨733326445828985323565429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488884297219323549043619 733326445828985323565429)
                ·
                  refine ⟨68749354296467374084259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 733326445828985323565429 68749354296467374084259)
                  ·
                    rfl

theorem cell21_301250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_301250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301250 prefixEnd_301250 := by exact prefixLift 301250
  have htrace : WordTrace (prefixWord ++ tailWord_301250) baseStart_301250 baseEnd_301250 := by
    simpa [prefixWord, tailWord_301250, baseEnd_301250] using wordTrace_append hprefix tailTrace_301250
  have hstable : (prefixWord ++ tailWord_301250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301250).length < 2 ^ (prefixWord ++ tailWord_301250).sum := by decide
  have hdescent : baseEnd_301250 < baseStart_301250 := by decide
  rcases family_descends (prefixWord ++ tailWord_301250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301292 : List Nat := [2, 2, 1, 1, 2, 3, 2, 5, 3]
def baseStart_301292 : Nat := 118140960795 + 301292 * 2 ^ 59
def prefixEnd_301292 : Nat := 4983230072969 + 3 ^ 40 * 301292 * 2
def baseEnd_301292 : Nat := 68758939268684634384173

theorem tailTrace_301292 : CollatzResearch.WordTrace tailWord_301292 prefixEnd_301292 68758939268684634384173 := by
  unfold tailWord_301292
  simp only [CollatzResearch.WordTrace]
  refine ⟨5494511012239007711021065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7326014682985343614694753 5494511012239007711021065)
  ·
    refine ⟨4120883259179255783265799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5494511012239007711021065 4120883259179255783265799)
    ·
      refine ⟨6181324888768883674898699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4120883259179255783265799 6181324888768883674898699)
      ·
        refine ⟨9271987333153325512348049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6181324888768883674898699 9271987333153325512348049)
        ·
          refine ⟨6953990499864994134261037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9271987333153325512348049 6953990499864994134261037)
          ·
            refine ⟨2607746437449372800347889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6953990499864994134261037 2607746437449372800347889)
            ·
              refine ⟨1955809828087029600260917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2607746437449372800347889 1955809828087029600260917)
              ·
                refine ⟨183357171383159025024461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1955809828087029600260917 183357171383159025024461)
                ·
                  refine ⟨68758939268684634384173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183357171383159025024461 68758939268684634384173)
                  ·
                    rfl

theorem cell21_301292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_301292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301292 prefixEnd_301292 := by exact prefixLift 301292
  have htrace : WordTrace (prefixWord ++ tailWord_301292) baseStart_301292 baseEnd_301292 := by
    simpa [prefixWord, tailWord_301292, baseEnd_301292] using wordTrace_append hprefix tailTrace_301292
  have hstable : (prefixWord ++ tailWord_301292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301292).length < 2 ^ (prefixWord ++ tailWord_301292).sum := by decide
  have hdescent : baseEnd_301292 < baseStart_301292 := by decide
  rcases family_descends (prefixWord ++ tailWord_301292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301306 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_301306 : Nat := 118140960795 + 301306 * 2 ^ 59
def prefixEnd_301306 : Nat := 4983230072969 + 3 ^ 40 * 301306 * 2
def baseEnd_301306 : Nat := 68762134259423721150811

theorem tailTrace_301306 : CollatzResearch.WordTrace tailWord_301306 prefixEnd_301306 68762134259423721150811 := by
  unfold tailWord_301306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2747383161606823953262943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7326355097618197208701181 2747383161606823953262943)
  ·
    refine ⟨4121074742410235929894415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2747383161606823953262943 4121074742410235929894415)
    ·
      refine ⟨6181612113615353894841623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4121074742410235929894415 6181612113615353894841623)
      ·
        refine ⟨9272418170423030842262435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6181612113615353894841623 9272418170423030842262435)
        ·
          refine ⟨13908627255634546263393653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9272418170423030842262435 13908627255634546263393653)
          ·
            refine ⟨1303933805215738712193155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13908627255634546263393653 1303933805215738712193155)
            ·
              refine ⟨1955900707823608068289733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303933805215738712193155 1955900707823608068289733)
              ·
                refine ⟨366731382716926512804325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1955900707823608068289733 366731382716926512804325)
                ·
                  refine ⟨68762134259423721150811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366731382716926512804325 68762134259423721150811)
                  ·
                    rfl

theorem cell21_301306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_301306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301306 prefixEnd_301306 := by exact prefixLift 301306
  have htrace : WordTrace (prefixWord ++ tailWord_301306) baseStart_301306 baseEnd_301306 := by
    simpa [prefixWord, tailWord_301306, baseEnd_301306] using wordTrace_append hprefix tailTrace_301306
  have hstable : (prefixWord ++ tailWord_301306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301306).length < 2 ^ (prefixWord ++ tailWord_301306).sum := by decide
  have hdescent : baseEnd_301306 < baseStart_301306 := by decide
  rcases family_descends (prefixWord ++ tailWord_301306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301357 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 4]
def baseStart_301357 : Nat := 118140960795 + 301357 * 2 ^ 59
def prefixEnd_301357 : Nat := 4983230072969 + 3 ^ 40 * 301357 * 2
def baseEnd_301357 : Nat := 68773773154258965800707

theorem tailTrace_301357 : CollatzResearch.WordTrace tailWord_301357 prefixEnd_301357 68773773154258965800707 := by
  unfold tailWord_301357
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991392769242531523158325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7327595179495021015438883 10991392769242531523158325)
  ·
    refine ⟨1030443072116487330296093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10991392769242531523158325 1030443072116487330296093)
    ·
      refine ⟨386416152043682748861035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1030443072116487330296093 386416152043682748861035)
      ·
        refine ⟨579624228065524123291553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386416152043682748861035 579624228065524123291553)
        ·
          refine ⟨434718171049143092468665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 579624228065524123291553 434718171049143092468665)
          ·
            refine ⟨326038628286857319351499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434718171049143092468665 326038628286857319351499)
            ·
              refine ⟨489057942430285979027249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326038628286857319351499 489057942430285979027249)
              ·
                refine ⟨366793456822714484270437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489057942430285979027249 366793456822714484270437)
                ·
                  refine ⟨68773773154258965800707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366793456822714484270437 68773773154258965800707)
                  ·
                    rfl

theorem cell21_301357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_301357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301357 prefixEnd_301357 := by exact prefixLift 301357
  have htrace : WordTrace (prefixWord ++ tailWord_301357) baseStart_301357 baseEnd_301357 := by
    simpa [prefixWord, tailWord_301357, baseEnd_301357] using wordTrace_append hprefix tailTrace_301357
  have hstable : (prefixWord ++ tailWord_301357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301357).length < 2 ^ (prefixWord ++ tailWord_301357).sum := by decide
  have hdescent : baseEnd_301357 < baseStart_301357 := by decide
  rcases family_descends (prefixWord ++ tailWord_301357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301368 : List Nat := [2, 1, 2, 1, 3, 1, 4, 4, 3]
def baseStart_301368 : Nat := 118140960795 + 301368 * 2 ^ 59
def prefixEnd_301368 : Nat := 4983230072969 + 3 ^ 40 * 301368 * 2
def baseEnd_301368 : Nat := 68776283504125391117351

theorem tailTrace_301368 : CollatzResearch.WordTrace tailWord_301368 prefixEnd_301368 68776283504125391117351 := by
  unfold tailWord_301368
  simp only [CollatzResearch.WordTrace]
  refine ⟨5495896986101340200904379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7327862648135120267872505 5495896986101340200904379)
  ·
    refine ⟨8243845479152010301356569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5495896986101340200904379 8243845479152010301356569)
    ·
      refine ⟨6182884109364007726017427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8243845479152010301356569 6182884109364007726017427)
      ·
        refine ⟨9274326164046011589026141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6182884109364007726017427 9274326164046011589026141)
        ·
          refine ⟨3477872311517254345884803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9274326164046011589026141 3477872311517254345884803)
          ·
            refine ⟨5216808467275881518827205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477872311517254345884803 5216808467275881518827205)
            ·
              refine ⟨978151587614227784780101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5216808467275881518827205 978151587614227784780101)
              ·
                refine ⟨183403422677667709646269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 978151587614227784780101 183403422677667709646269)
                ·
                  refine ⟨68776283504125391117351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183403422677667709646269 68776283504125391117351)
                  ·
                    rfl

theorem cell21_301368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_301368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301368 prefixEnd_301368 := by exact prefixLift 301368
  have htrace : WordTrace (prefixWord ++ tailWord_301368) baseStart_301368 baseEnd_301368 := by
    simpa [prefixWord, tailWord_301368, baseEnd_301368] using wordTrace_append hprefix tailTrace_301368
  have hstable : (prefixWord ++ tailWord_301368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301368).length < 2 ^ (prefixWord ++ tailWord_301368).sum := by decide
  have hdescent : baseEnd_301368 < baseStart_301368 := by decide
  rcases family_descends (prefixWord ++ tailWord_301368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301489 : List Nat := [1, 2, 2, 4, 1, 4, 1, 6]
def baseStart_301489 : Nat := 118140960795 + 301489 * 2 ^ 59
def prefixEnd_301489 : Nat := 4983230072969 + 3 ^ 40 * 301489 * 2
def baseEnd_301489 : Nat := 22934632450885356533479

theorem tailTrace_301489 : CollatzResearch.WordTrace tailWord_301489 prefixEnd_301489 22934632450885356533479 := by
  unfold tailWord_301489
  simp only [CollatzResearch.WordTrace]
  refine ⟨10996207204764318066963521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7330804803176212044642347 10996207204764318066963521)
  ·
    refine ⟨8247155403573238550222641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10996207204764318066963521 8247155403573238550222641)
    ·
      refine ⟨6185366552679928912666981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8247155403573238550222641 6185366552679928912666981)
      ·
        refine ⟨1159756228627486671125059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6185366552679928912666981 1159756228627486671125059)
        ·
          refine ⟨1739634342941230006687589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159756228627486671125059 1739634342941230006687589)
          ·
            refine ⟨326181439301480626253923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1739634342941230006687589 326181439301480626253923)
            ·
              refine ⟨489272158952220939380885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326181439301480626253923 489272158952220939380885)
              ·
                refine ⟨22934632450885356533479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 489272158952220939380885 22934632450885356533479)
                ·
                  rfl

theorem cell21_301489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 6].length) (baseStart_301489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301489 prefixEnd_301489 := by exact prefixLift 301489
  have htrace : WordTrace (prefixWord ++ tailWord_301489) baseStart_301489 baseEnd_301489 := by
    simpa [prefixWord, tailWord_301489, baseEnd_301489] using wordTrace_append hprefix tailTrace_301489
  have hstable : (prefixWord ++ tailWord_301489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301489).length < 2 ^ (prefixWord ++ tailWord_301489).sum := by decide
  have hdescent : baseEnd_301489 < baseStart_301489 := by decide
  rcases family_descends (prefixWord ++ tailWord_301489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301562 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 7]
def baseStart_301562 : Nat := 118140960795 + 301562 * 2 ^ 59
def prefixEnd_301562 : Nat := 4983230072969 + 3 ^ 40 * 301562 * 2
def baseEnd_301562 : Nat := 68820556947224164883621

theorem tailTrace_301562 : CollatzResearch.WordTrace tailWord_301562 prefixEnd_301562 68820556947224164883621 := by
  unfold tailWord_301562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2749717433374962883592735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7332579822333234356247293 2749717433374962883592735)
  ·
    refine ⟨4124576150062444325389103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2749717433374962883592735 4124576150062444325389103)
    ·
      refine ⟨6186864225093666488083655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4124576150062444325389103 6186864225093666488083655)
      ·
        refine ⟨9280296337640499732125483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6186864225093666488083655 9280296337640499732125483)
        ·
          refine ⟨13920444506460749598188225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9280296337640499732125483 13920444506460749598188225)
          ·
            refine ⟨10440333379845562198641169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13920444506460749598188225 10440333379845562198641169)
            ·
              refine ⟨7830250034884171648980877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10440333379845562198641169 7830250034884171648980877)
              ·
                refine ⟨2936343763081564368367829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7830250034884171648980877 2936343763081564368367829)
                ·
                  refine ⟨68820556947224164883621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2936343763081564368367829 68820556947224164883621)
                  ·
                    rfl

theorem cell21_301562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_301562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301562 prefixEnd_301562 := by exact prefixLift 301562
  have htrace : WordTrace (prefixWord ++ tailWord_301562) baseStart_301562 baseEnd_301562 := by
    simpa [prefixWord, tailWord_301562, baseEnd_301562] using wordTrace_append hprefix tailTrace_301562
  have hstable : (prefixWord ++ tailWord_301562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301562).length < 2 ^ (prefixWord ++ tailWord_301562).sum := by decide
  have hdescent : baseEnd_301562 < baseStart_301562 := by decide
  rcases family_descends (prefixWord ++ tailWord_301562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301596 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_301596 : Nat := 118140960795 + 301596 * 2 ^ 59
def prefixEnd_301596 : Nat := 4983230072969 + 3 ^ 40 * 301596 * 2
def baseEnd_301596 : Nat := 68828316210447661316885

theorem tailTrace_301596 : CollatzResearch.WordTrace tailWord_301596 prefixEnd_301596 68828316210447661316885 := by
  unfold tailWord_301596
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500054907688337670554321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7333406543584450227405761 5500054907688337670554321)
  ·
    refine ⟨4125041180766253252915741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5500054907688337670554321 4125041180766253252915741)
    ·
      refine ⟨1546890442787344969843403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4125041180766253252915741 1546890442787344969843403)
      ·
        refine ⟨2320335664181017454765105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546890442787344969843403 2320335664181017454765105)
        ·
          refine ⟨1740251748135763091073829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2320335664181017454765105 1740251748135763091073829)
          ·
            refine ⟨326297202775455579576343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1740251748135763091073829 326297202775455579576343)
            ·
              refine ⟨489445804163183369364515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326297202775455579576343 489445804163183369364515)
              ·
                refine ⟨734168706244775054046773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489445804163183369364515 734168706244775054046773)
                ·
                  refine ⟨68828316210447661316885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 734168706244775054046773 68828316210447661316885)
                  ·
                    rfl

theorem cell21_301596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_301596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301596 prefixEnd_301596 := by exact prefixLift 301596
  have htrace : WordTrace (prefixWord ++ tailWord_301596) baseStart_301596 baseEnd_301596 := by
    simpa [prefixWord, tailWord_301596, baseEnd_301596] using wordTrace_append hprefix tailTrace_301596
  have hstable : (prefixWord ++ tailWord_301596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301596).length < 2 ^ (prefixWord ++ tailWord_301596).sum := by decide
  have hdescent : baseEnd_301596 < baseStart_301596 := by decide
  rcases family_descends (prefixWord ++ tailWord_301596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301672 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_301672 : Nat := 118140960795 + 301672 * 2 ^ 59
def prefixEnd_301672 : Nat := 4983230072969 + 3 ^ 40 * 301672 * 2
def baseEnd_301672 : Nat := 68845660445888418050063

theorem tailTrace_301672 : CollatzResearch.WordTrace tailWord_301672 prefixEnd_301672 68845660445888418050063 := by
  unfold tailWord_301672
  simp only [CollatzResearch.WordTrace]
  refine ⟨5501440881550670160437635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7335254508734226880583513 5501440881550670160437635)
  ·
    refine ⟨8252161322326005240656453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5501440881550670160437635 8252161322326005240656453)
    ·
      refine ⟨1547280247936125982623085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8252161322326005240656453 1547280247936125982623085)
      ·
        refine ⟨580230092976047243483657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1547280247936125982623085 580230092976047243483657)
        ·
          refine ⟨435172569732035432612743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580230092976047243483657 435172569732035432612743)
          ·
            refine ⟨652758854598053148919115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435172569732035432612743 652758854598053148919115)
            ·
              refine ⟨979138281897079723378673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652758854598053148919115 979138281897079723378673)
              ·
                refine ⟨734353711422809792534005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979138281897079723378673 734353711422809792534005)
                ·
                  refine ⟨68845660445888418050063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 734353711422809792534005 68845660445888418050063)
                  ·
                    rfl

theorem cell21_301672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_301672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301672 prefixEnd_301672 := by exact prefixLift 301672
  have htrace : WordTrace (prefixWord ++ tailWord_301672) baseStart_301672 baseEnd_301672 := by
    simpa [prefixWord, tailWord_301672, baseEnd_301672] using wordTrace_append hprefix tailTrace_301672
  have hstable : (prefixWord ++ tailWord_301672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301672).length < 2 ^ (prefixWord ++ tailWord_301672).sum := by decide
  have hdescent : baseEnd_301672 < baseStart_301672 := by decide
  rcases family_descends (prefixWord ++ tailWord_301672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301700 : List Nat := [2, 3, 2, 1, 3, 2, 8]
def baseStart_301700 : Nat := 118140960795 + 301700 * 2 ^ 59
def prefixEnd_301700 : Nat := 4983230072969 + 3 ^ 40 * 301700 * 2
def baseEnd_301700 : Nat := 7650227825262954620371

theorem tailTrace_301700 : CollatzResearch.WordTrace tailWord_301700 prefixEnd_301700 7650227825262954620371 := by
  unfold tailWord_301700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5501951503499950551447277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7335935337999934068596369 5501951503499950551447277)
  ·
    refine ⟨2063231813812481456792729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5501951503499950551447277 2063231813812481456792729)
    ·
      refine ⟨1547423860359361092594547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2063231813812481456792729 1547423860359361092594547)
      ·
        refine ⟨2321135790539041638891821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1547423860359361092594547 2321135790539041638891821)
        ·
          refine ⟨870425921452140614584433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2321135790539041638891821 870425921452140614584433)
          ·
            refine ⟨652819441089105460938325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870425921452140614584433 652819441089105460938325)
            ·
              refine ⟨7650227825262954620371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 652819441089105460938325 7650227825262954620371)
              ·
                rfl

theorem cell21_301700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 8].length) (baseStart_301700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301700 prefixEnd_301700 := by exact prefixLift 301700
  have htrace : WordTrace (prefixWord ++ tailWord_301700) baseStart_301700 baseEnd_301700 := by
    simpa [prefixWord, tailWord_301700, baseEnd_301700] using wordTrace_append hprefix tailTrace_301700
  have hstable : (prefixWord ++ tailWord_301700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301700).length < 2 ^ (prefixWord ++ tailWord_301700).sum := by decide
  have hdescent : baseEnd_301700 < baseStart_301700 := by decide
  rcases family_descends (prefixWord ++ tailWord_301700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301759 : List Nat := [1, 1, 2, 2, 2, 4, 9]
def baseStart_301759 : Nat := 118140960795 + 301759 * 2 ^ 59
def prefixEnd_301759 : Nat := 4983230072969 + 3 ^ 40 * 301759 * 2
def baseEnd_301759 : Nat := 7651723892355066677765

theorem tailTrace_301759 : CollatzResearch.WordTrace tailWord_301759 prefixEnd_301759 7651723892355066677765 := by
  unfold tailWord_301759
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006054913786154179292331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7337369942524102786194887 11006054913786154179292331)
  ·
    refine ⟨16509082370679231268938497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11006054913786154179292331 16509082370679231268938497)
    ·
      refine ⟨12381811778009423451703873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16509082370679231268938497 12381811778009423451703873)
      ·
        refine ⟨9286358833507067588777905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12381811778009423451703873 9286358833507067588777905)
        ·
          refine ⟨6964769125130300691583429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9286358833507067588777905 6964769125130300691583429)
          ·
            refine ⟨1305894210961931379671893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6964769125130300691583429 1305894210961931379671893)
            ·
              refine ⟨7651723892355066677765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1305894210961931379671893 7651723892355066677765)
              ·
                rfl

theorem cell21_301759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 9].length) (baseStart_301759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301759 prefixEnd_301759 := by exact prefixLift 301759
  have htrace : WordTrace (prefixWord ++ tailWord_301759) baseStart_301759 baseEnd_301759 := by
    simpa [prefixWord, tailWord_301759, baseEnd_301759] using wordTrace_append hprefix tailTrace_301759
  have hstable : (prefixWord ++ tailWord_301759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301759).length < 2 ^ (prefixWord ++ tailWord_301759).sum := by decide
  have hdescent : baseEnd_301759 < baseStart_301759 := by decide
  rcases family_descends (prefixWord ++ tailWord_301759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301813 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 4]
def baseStart_301813 : Nat := 118140960795 + 301813 * 2 ^ 59
def prefixEnd_301813 : Nat := 4983230072969 + 3 ^ 40 * 301813 * 2
def baseEnd_301813 : Nat := 68877838566903506199775

theorem tailTrace_301813 : CollatzResearch.WordTrace tailWord_301813 prefixEnd_301813 68877838566903506199775 := by
  unfold tailWord_301813
  simp only [CollatzResearch.WordTrace]
  refine ⟨11008024455590521401758093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7338682970393680934505395 11008024455590521401758093)
  ·
    refine ⟨4128009170846445525659285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11008024455590521401758093 4128009170846445525659285)
    ·
      refine ⟨193500429883427134015279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4128009170846445525659285 193500429883427134015279)
      ·
        refine ⟨290250644825140701022919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193500429883427134015279 290250644825140701022919)
        ·
          refine ⟨435375967237711051534379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290250644825140701022919 435375967237711051534379)
          ·
            refine ⟨653063950856566577301569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435375967237711051534379 653063950856566577301569)
            ·
              refine ⟨489797963142424932976177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653063950856566577301569 489797963142424932976177)
              ·
                refine ⟨367348472356818699732133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489797963142424932976177 367348472356818699732133)
                ·
                  refine ⟨68877838566903506199775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367348472356818699732133 68877838566903506199775)
                  ·
                    rfl

theorem cell21_301813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_301813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301813 prefixEnd_301813 := by exact prefixLift 301813
  have htrace : WordTrace (prefixWord ++ tailWord_301813) baseStart_301813 baseEnd_301813 := by
    simpa [prefixWord, tailWord_301813, baseEnd_301813] using wordTrace_append hprefix tailTrace_301813
  have hstable : (prefixWord ++ tailWord_301813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301813).length < 2 ^ (prefixWord ++ tailWord_301813).sum := by decide
  have hdescent : baseEnd_301813 < baseStart_301813 := by decide
  rcases family_descends (prefixWord ++ tailWord_301813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301928 : List Nat := [2, 1, 4, 2, 1, 4, 7]
def baseStart_301928 : Nat := 118140960795 + 301928 * 2 ^ 59
def prefixEnd_301928 : Nat := 4983230072969 + 3 ^ 40 * 301928 * 2
def baseEnd_301928 : Nat := 7656009237076540198097

theorem tailTrace_301928 : CollatzResearch.WordTrace tailWord_301928 prefixEnd_301928 7656009237076540198097 := by
  unfold tailWord_301928
  simp only [CollatzResearch.WordTrace]
  refine ⟨5506109425086948021097219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7341479233449264028129625 5506109425086948021097219)
  ·
    refine ⟨8259164137630422031645829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5506109425086948021097219 8259164137630422031645829)
    ·
      refine ⟨1548593275805704130933593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8259164137630422031645829 1548593275805704130933593)
      ·
        refine ⟨1161444956854278098200195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1548593275805704130933593 1161444956854278098200195)
        ·
          refine ⟨1742167435281417147300293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1161444956854278098200195 1742167435281417147300293)
          ·
            refine ⟨326656394115265715118805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1742167435281417147300293 326656394115265715118805)
            ·
              refine ⟨7656009237076540198097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 326656394115265715118805 7656009237076540198097)
              ·
                rfl

theorem cell21_301928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 7].length) (baseStart_301928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301928 prefixEnd_301928 := by exact prefixLift 301928
  have htrace : WordTrace (prefixWord ++ tailWord_301928) baseStart_301928 baseEnd_301928 := by
    simpa [prefixWord, tailWord_301928, baseEnd_301928] using wordTrace_append hprefix tailTrace_301928
  have hstable : (prefixWord ++ tailWord_301928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301928).length < 2 ^ (prefixWord ++ tailWord_301928).sum := by decide
  have hdescent : baseEnd_301928 < baseStart_301928 := by decide
  rcases family_descends (prefixWord ++ tailWord_301928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301934 : List Nat := [4, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_301934 : Nat := 118140960795 + 301934 * 2 ^ 59
def prefixEnd_301934 : Nat := 4983230072969 + 3 ^ 40 * 301934 * 2
def baseEnd_301934 : Nat := 68905452415434184682861

theorem tailTrace_301934 : CollatzResearch.WordTrace tailWord_301934 prefixEnd_301934 68905452415434184682861 := by
  unfold tailWord_301934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376554711019019883364107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7341625125434772711275237 1376554711019019883364107)
  ·
    refine ⟨2064832066528529825046161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1376554711019019883364107 2064832066528529825046161)
    ·
      refine ⟨1548624049896397368784621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2064832066528529825046161 1548624049896397368784621)
      ·
        refine ⟨580734018711149013294233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1548624049896397368784621 580734018711149013294233)
        ·
          refine ⟨435550514033361759970675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580734018711149013294233 435550514033361759970675)
          ·
            refine ⟨653325771050042639956013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435550514033361759970675 653325771050042639956013)
            ·
              refine ⟨244997164143765989983505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 653325771050042639956013 244997164143765989983505)
              ·
                refine ⟨183747873107824492487629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244997164143765989983505 183747873107824492487629)
                ·
                  refine ⟨68905452415434184682861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183747873107824492487629 68905452415434184682861)
                  ·
                    rfl

theorem cell21_301934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_301934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_301934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_301934 prefixEnd_301934 := by exact prefixLift 301934
  have htrace : WordTrace (prefixWord ++ tailWord_301934) baseStart_301934 baseEnd_301934 := by
    simpa [prefixWord, tailWord_301934, baseEnd_301934] using wordTrace_append hprefix tailTrace_301934
  have hstable : (prefixWord ++ tailWord_301934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301934).length < 2 ^ (prefixWord ++ tailWord_301934).sum := by decide
  have hdescent : baseEnd_301934 < baseStart_301934 := by decide
  rcases family_descends (prefixWord ++ tailWord_301934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302032 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_302032 : Nat := 118140960795 + 302032 * 2 ^ 59
def prefixEnd_302032 : Nat := 4983230072969 + 3 ^ 40 * 302032 * 2
def baseEnd_302032 : Nat := 68927817350607792049327

theorem tailTrace_302032 : CollatzResearch.WordTrace tailWord_302032 prefixEnd_302032 68927817350607792049327 := by
  unfold tailWord_302032
  simp only [CollatzResearch.WordTrace]
  refine ⟨5508006020898560901990175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7344008027864747869320233 5508006020898560901990175)
  ·
    refine ⟨8262009031347841352985263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5508006020898560901990175 8262009031347841352985263)
    ·
      refine ⟨12393013547021762029477895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8262009031347841352985263 12393013547021762029477895)
      ·
        refine ⟨18589520320532643044216843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12393013547021762029477895 18589520320532643044216843)
        ·
          refine ⟨27884280480798964566325265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18589520320532643044216843 27884280480798964566325265)
          ·
            refine ⟨20913210360599223424743949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27884280480798964566325265 20913210360599223424743949)
            ·
              refine ⟨7842453885224708784278981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20913210360599223424743949 7842453885224708784278981)
              ·
                refine ⟨1470460103479632897052309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7842453885224708784278981 1470460103479632897052309)
                ·
                  refine ⟨68927817350607792049327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1470460103479632897052309 68927817350607792049327)
                  ·
                    rfl

theorem cell21_302032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_302032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302032 prefixEnd_302032 := by exact prefixLift 302032
  have htrace : WordTrace (prefixWord ++ tailWord_302032) baseStart_302032 baseEnd_302032 := by
    simpa [prefixWord, tailWord_302032, baseEnd_302032] using wordTrace_append hprefix tailTrace_302032
  have hstable : (prefixWord ++ tailWord_302032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302032).length < 2 ^ (prefixWord ++ tailWord_302032).sum := by decide
  have hdescent : baseEnd_302032 < baseStart_302032 := by decide
  rcases family_descends (prefixWord ++ tailWord_302032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302111 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 5]
def baseStart_302111 : Nat := 118140960795 + 302111 * 2 ^ 59
def prefixEnd_302111 : Nat := 4983230072969 + 3 ^ 40 * 302111 * 2
def baseEnd_302111 : Nat := 68945846226921210232499

theorem tailTrace_302111 : CollatzResearch.WordTrace tailWord_302111 prefixEnd_302111 68945846226921210232499 := by
  unfold tailWord_302111
  simp only [CollatzResearch.WordTrace]
  refine ⟨11018893408510918296106187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7345928939007278864070791 11018893408510918296106187)
  ·
    refine ⟨16528340112766377444159281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11018893408510918296106187 16528340112766377444159281)
    ·
      refine ⟨12396255084574783083119461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16528340112766377444159281 12396255084574783083119461)
      ·
        refine ⟨2324297828357771828084899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12396255084574783083119461 2324297828357771828084899)
        ·
          refine ⟨3486446742536657742127349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2324297828357771828084899 3486446742536657742127349)
          ·
            refine ⟨326854382112811663324439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3486446742536657742127349 326854382112811663324439)
            ·
              refine ⟨490281573169217494986659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326854382112811663324439 490281573169217494986659)
              ·
                refine ⟨735422359753826242479989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490281573169217494986659 735422359753826242479989)
                ·
                  refine ⟨68945846226921210232499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 735422359753826242479989 68945846226921210232499)
                  ·
                    rfl

theorem cell21_302111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 5].length) (baseStart_302111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302111 prefixEnd_302111 := by exact prefixLift 302111
  have htrace : WordTrace (prefixWord ++ tailWord_302111) baseStart_302111 baseEnd_302111 := by
    simpa [prefixWord, tailWord_302111, baseEnd_302111] using wordTrace_append hprefix tailTrace_302111
  have hstable : (prefixWord ++ tailWord_302111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302111).length < 2 ^ (prefixWord ++ tailWord_302111).sum := by decide
  have hdescent : baseEnd_302111 < baseStart_302111 := by decide
  rcases family_descends (prefixWord ++ tailWord_302111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302153 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 9]
def baseStart_302153 : Nat := 118140960795 + 302153 * 2 ^ 59
def prefixEnd_302153 : Nat := 4983230072969 + 3 ^ 40 * 302153 * 2
def baseEnd_302153 : Nat := 68955431199138470532413

theorem tailTrace_302153 : CollatzResearch.WordTrace tailWord_302153 prefixEnd_302153 68955431199138470532413 := by
  unfold tailWord_302153
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020425274358759469135113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7346950182905839646090075 11020425274358759469135113)
  ·
    refine ⟨8265318955769069601851335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11020425274358759469135113 8265318955769069601851335)
    ·
      refine ⟨12397978433653604402777003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8265318955769069601851335 12397978433653604402777003)
      ·
        refine ⟨18596967650480406604165505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12397978433653604402777003 18596967650480406604165505)
        ·
          refine ⟨13947725737860304953124129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18596967650480406604165505 13947725737860304953124129)
          ·
            refine ⟨10460794303395228714843097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13947725737860304953124129 10460794303395228714843097)
            ·
              refine ⟨7845595727546421536132323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10460794303395228714843097 7845595727546421536132323)
              ·
                refine ⟨11768393591319632304198485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7845595727546421536132323 11768393591319632304198485)
                ·
                  refine ⟨68955431199138470532413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11768393591319632304198485 68955431199138470532413)
                  ·
                    rfl

theorem cell21_302153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_302153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302153 prefixEnd_302153 := by exact prefixLift 302153
  have htrace : WordTrace (prefixWord ++ tailWord_302153) baseStart_302153 baseEnd_302153 := by
    simpa [prefixWord, tailWord_302153, baseEnd_302153] using wordTrace_append hprefix tailTrace_302153
  have hstable : (prefixWord ++ tailWord_302153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302153).length < 2 ^ (prefixWord ++ tailWord_302153).sum := by decide
  have hdescent : baseEnd_302153 < baseStart_302153 := by decide
  rcases family_descends (prefixWord ++ tailWord_302153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302339 : List Nat := [1, 1, 1, 3, 2, 5, 1, 4, 3]
def baseStart_302339 : Nat := 118140960795 + 302339 * 2 ^ 59
def prefixEnd_302339 : Nat := 4983230072969 + 3 ^ 40 * 302339 * 2
def baseEnd_302339 : Nat := 68997878933243480432033

theorem tailTrace_302339 : CollatzResearch.WordTrace tailWord_302339 prefixEnd_302339 68997878933243480432033 := by
  unfold tailWord_302339
  simp only [CollatzResearch.WordTrace]
  refine ⟨11027209251684913235406071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7351472834456608823604047 11027209251684913235406071)
  ·
    refine ⟨16540813877527369853109107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11027209251684913235406071 16540813877527369853109107)
    ·
      refine ⟨24811220816291054779663661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16540813877527369853109107 24811220816291054779663661)
      ·
        refine ⟨9304207806109145542373873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24811220816291054779663661 9304207806109145542373873)
        ·
          refine ⟨6978155854581859156780405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9304207806109145542373873 6978155854581859156780405)
          ·
            refine ⟨654202111367049295948163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6978155854581859156780405 654202111367049295948163)
            ·
              refine ⟨981303167050573943922245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 654202111367049295948163 981303167050573943922245)
              ·
                refine ⟨183994343821982614485421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 981303167050573943922245 183994343821982614485421)
                ·
                  refine ⟨68997878933243480432033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183994343821982614485421 68997878933243480432033)
                  ·
                    rfl

theorem cell21_302339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 3].length) (baseStart_302339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302339 prefixEnd_302339 := by exact prefixLift 302339
  have htrace : WordTrace (prefixWord ++ tailWord_302339) baseStart_302339 baseEnd_302339 := by
    simpa [prefixWord, tailWord_302339, baseEnd_302339] using wordTrace_append hprefix tailTrace_302339
  have hstable : (prefixWord ++ tailWord_302339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302339).length < 2 ^ (prefixWord ++ tailWord_302339).sum := by decide
  have hdescent : baseEnd_302339 < baseStart_302339 := by decide
  rcases family_descends (prefixWord ++ tailWord_302339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302432 : List Nat := [2, 1, 1, 3, 4, 3, 1, 3, 3]
def baseStart_302432 : Nat := 118140960795 + 302432 * 2 ^ 59
def prefixEnd_302432 : Nat := 4983230072969 + 3 ^ 40 * 302432 * 2
def baseEnd_302432 : Nat := 69019102800295985381843

theorem tailTrace_302432 : CollatzResearch.WordTrace tailWord_302432 prefixEnd_302432 69019102800295985381843 := by
  unfold tailWord_302432
  simp only [CollatzResearch.WordTrace]
  refine ⟨5515300620173995059270775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7353734160231993412361033 5515300620173995059270775)
  ·
    refine ⟨8272950930260992588906163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5515300620173995059270775 8272950930260992588906163)
    ·
      refine ⟨12409426395391488883359245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8272950930260992588906163 12409426395391488883359245)
      ·
        refine ⟨4653534898271808331259717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12409426395391488883359245 4653534898271808331259717)
        ·
          refine ⟨872537793425964062111197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4653534898271808331259717 872537793425964062111197)
          ·
            refine ⟨327201672534736523291699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 872537793425964062111197 327201672534736523291699)
            ·
              refine ⟨490802508802104784937549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327201672534736523291699 490802508802104784937549)
              ·
                refine ⟨184050940800789294351581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 490802508802104784937549 184050940800789294351581)
                ·
                  refine ⟨69019102800295985381843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184050940800789294351581 69019102800295985381843)
                  ·
                    rfl

theorem cell21_302432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_302432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302432 prefixEnd_302432 := by exact prefixLift 302432
  have htrace : WordTrace (prefixWord ++ tailWord_302432) baseStart_302432 baseEnd_302432 := by
    simpa [prefixWord, tailWord_302432, baseEnd_302432] using wordTrace_append hprefix tailTrace_302432
  have hstable : (prefixWord ++ tailWord_302432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302432).length < 2 ^ (prefixWord ++ tailWord_302432).sum := by decide
  have hdescent : baseEnd_302432 < baseStart_302432 := by decide
  rcases family_descends (prefixWord ++ tailWord_302432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302567 : List Nat := [1, 1, 5, 2, 1, 2, 2, 4, 3]
def baseStart_302567 : Nat := 118140960795 + 302567 * 2 ^ 59
def prefixEnd_302567 : Nat := 4983230072969 + 3 ^ 40 * 302567 * 2
def baseEnd_302567 : Nat := 69049911639565750631567

theorem tailTrace_302567 : CollatzResearch.WordTrace tailWord_302567 prefixEnd_302567 69049911639565750631567 := by
  unfold tailWord_302567
  simp only [CollatzResearch.WordTrace]
  refine ⟨11035525094858908174705955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7357016729905938783137303 11035525094858908174705955)
  ·
    refine ⟨16553287642288362262058933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11035525094858908174705955 16553287642288362262058933)
    ·
      refine ⟨1551870716464533962068025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16553287642288362262058933 1551870716464533962068025)
      ·
        refine ⟨1163903037348400471551019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1551870716464533962068025 1163903037348400471551019)
        ·
          refine ⟨1745854556022600707326529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1163903037348400471551019 1745854556022600707326529)
          ·
            refine ⟨1309390917016950530494897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1745854556022600707326529 1309390917016950530494897)
            ·
              refine ⟨982043187762712897871173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1309390917016950530494897 982043187762712897871173)
              ·
                refine ⟨184133097705508668350845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 982043187762712897871173 184133097705508668350845)
                ·
                  refine ⟨69049911639565750631567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184133097705508668350845 69049911639565750631567)
                  ·
                    rfl

theorem cell21_302567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 3].length) (baseStart_302567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302567 prefixEnd_302567 := by exact prefixLift 302567
  have htrace : WordTrace (prefixWord ++ tailWord_302567) baseStart_302567 baseEnd_302567 := by
    simpa [prefixWord, tailWord_302567, baseEnd_302567] using wordTrace_append hprefix tailTrace_302567
  have hstable : (prefixWord ++ tailWord_302567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302567).length < 2 ^ (prefixWord ++ tailWord_302567).sum := by decide
  have hdescent : baseEnd_302567 < baseStart_302567 := by decide
  rcases family_descends (prefixWord ++ tailWord_302567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302626 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_302626 : Nat := 118140960795 + 302626 * 2 ^ 59
def prefixEnd_302626 : Nat := 4983230072969 + 3 ^ 40 * 302626 * 2
def baseEnd_302626 : Nat := 69063376243394759148113

theorem tailTrace_302626 : CollatzResearch.WordTrace tailWord_302626 prefixEnd_302626 69063376243394759148113 := by
  unfold tailWord_302626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759419250411290312775933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7358451334430107500735821 2759419250411290312775933)
  ·
    refine ⟨1034782218904233867290975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2759419250411290312775933 1034782218904233867290975)
    ·
      refine ⟨1552173328356350800936463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1034782218904233867290975 1552173328356350800936463)
      ·
        refine ⟨2328259992534526201404695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552173328356350800936463 2328259992534526201404695)
        ·
          refine ⟨3492389988801789302107043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328259992534526201404695 3492389988801789302107043)
          ·
            refine ⟨5238584983202683953160565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492389988801789302107043 5238584983202683953160565)
            ·
              refine ⟨491117342175251620608803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5238584983202683953160565 491117342175251620608803)
              ·
                refine ⟨736676013262877430913205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491117342175251620608803 736676013262877430913205)
                ·
                  refine ⟨69063376243394759148113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 736676013262877430913205 69063376243394759148113)
                  ·
                    rfl

theorem cell21_302626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_302626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302626 prefixEnd_302626 := by exact prefixLift 302626
  have htrace : WordTrace (prefixWord ++ tailWord_302626) baseStart_302626 baseEnd_302626 := by
    simpa [prefixWord, tailWord_302626, baseEnd_302626] using wordTrace_append hprefix tailTrace_302626
  have hstable : (prefixWord ++ tailWord_302626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302626).length < 2 ^ (prefixWord ++ tailWord_302626).sum := by decide
  have hdescent : baseEnd_302626 < baseStart_302626 := by decide
  rcases family_descends (prefixWord ++ tailWord_302626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302632 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 4]
def baseStart_302632 : Nat := 118140960795 + 302632 * 2 ^ 59
def prefixEnd_302632 : Nat := 4983230072969 + 3 ^ 40 * 302632 * 2
def baseEnd_302632 : Nat := 69064745525140082048101

theorem tailTrace_302632 : CollatzResearch.WordTrace tailWord_302632 prefixEnd_302632 69064745525140082048101 := by
  unfold tailWord_302632
  simp only [CollatzResearch.WordTrace]
  refine ⟨5518947919811712137911075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7358597226415616183881433 5518947919811712137911075)
  ·
    refine ⟨8278421879717568206866613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5518947919811712137911075 8278421879717568206866613)
    ·
      refine ⟨776102051223522019393745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8278421879717568206866613 776102051223522019393745)
      ·
        refine ⟨582076538417641514545309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 776102051223522019393745 582076538417641514545309)
        ·
          refine ⟨218278701906615567954491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 582076538417641514545309 218278701906615567954491)
          ·
            refine ⟨327418052859923351931737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218278701906615567954491 327418052859923351931737)
            ·
              refine ⟨245563539644942513948803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327418052859923351931737 245563539644942513948803)
              ·
                refine ⟨368345309467413770923205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245563539644942513948803 368345309467413770923205)
                ·
                  refine ⟨69064745525140082048101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368345309467413770923205 69064745525140082048101)
                  ·
                    rfl

theorem cell21_302632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_302632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302632 prefixEnd_302632 := by exact prefixLift 302632
  have htrace : WordTrace (prefixWord ++ tailWord_302632) baseStart_302632 baseEnd_302632 := by
    simpa [prefixWord, tailWord_302632, baseEnd_302632] using wordTrace_append hprefix tailTrace_302632
  have hstable : (prefixWord ++ tailWord_302632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302632).length < 2 ^ (prefixWord ++ tailWord_302632).sum := by decide
  have hdescent : baseEnd_302632 < baseStart_302632 := by decide
  rcases family_descends (prefixWord ++ tailWord_302632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302792 : List Nat := [2, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_302792 : Nat := 118140960795 + 302792 * 2 ^ 59
def prefixEnd_302792 : Nat := 4983230072969 + 3 ^ 40 * 302792 * 2
def baseEnd_302792 : Nat := 69101259705015359381107

theorem tailTrace_302792 : CollatzResearch.WordTrace tailWord_302792 prefixEnd_302792 69101259705015359381107 := by
  unfold tailWord_302792
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521865759521885800823315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7362487679362514401097753 5521865759521885800823315)
  ·
    refine ⟨8282798639282828701234973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5521865759521885800823315 8282798639282828701234973)
    ·
      refine ⟨3106049489731060762963115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8282798639282828701234973 3106049489731060762963115)
      ·
        refine ⟨4659074234596591144444673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3106049489731060762963115 4659074234596591144444673)
        ·
          refine ⟨3494305675947443358333505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4659074234596591144444673 3494305675947443358333505)
          ·
            refine ⟨2620729256960582518750129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3494305675947443358333505 2620729256960582518750129)
            ·
              refine ⟨1965546942720436889062597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2620729256960582518750129 1965546942720436889062597)
              ·
                refine ⟨368540051760081916699237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1965546942720436889062597 368540051760081916699237)
                ·
                  refine ⟨69101259705015359381107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368540051760081916699237 69101259705015359381107)
                  ·
                    rfl

theorem cell21_302792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_302792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302792 prefixEnd_302792 := by exact prefixLift 302792
  have htrace : WordTrace (prefixWord ++ tailWord_302792) baseStart_302792 baseEnd_302792 := by
    simpa [prefixWord, tailWord_302792, baseEnd_302792] using wordTrace_append hprefix tailTrace_302792
  have hstable : (prefixWord ++ tailWord_302792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302792).length < 2 ^ (prefixWord ++ tailWord_302792).sum := by decide
  have hdescent : baseEnd_302792 < baseStart_302792 := by decide
  rcases family_descends (prefixWord ++ tailWord_302792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302809 : List Nat := [1, 2, 1, 2, 3, 3, 4, 1, 4]
def baseStart_302809 : Nat := 118140960795 + 302809 * 2 ^ 59
def prefixEnd_302809 : Nat := 4983230072969 + 3 ^ 40 * 302809 * 2
def baseEnd_302809 : Nat := 69105139336627107597739

theorem tailTrace_302809 : CollatzResearch.WordTrace tailWord_302809 prefixEnd_302809 69105139336627107597739 := by
  unfold tailWord_302809
  simp only [CollatzResearch.WordTrace]
  refine ⟨11044351559982183505015481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7362901039988122336676987 11044351559982183505015481)
  ·
    refine ⟨8283263669986637628761611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11044351559982183505015481 8283263669986637628761611)
    ·
      refine ⟨12424895504979956443142417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8283263669986637628761611 12424895504979956443142417)
      ·
        refine ⟨9318671628734967332356813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12424895504979956443142417 9318671628734967332356813)
        ·
          refine ⟨3494501860775612749633805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9318671628734967332356813 3494501860775612749633805)
          ·
            refine ⟨1310438197790854781112677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3494501860775612749633805 1310438197790854781112677)
            ·
              refine ⟨245707162085785271458627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1310438197790854781112677 245707162085785271458627)
              ·
                refine ⟨368560743128677907187941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245707162085785271458627 368560743128677907187941)
                ·
                  refine ⟨69105139336627107597739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368560743128677907187941 69105139336627107597739)
                  ·
                    rfl

theorem cell21_302809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_302809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302809 prefixEnd_302809 := by exact prefixLift 302809
  have htrace : WordTrace (prefixWord ++ tailWord_302809) baseStart_302809 baseEnd_302809 := by
    simpa [prefixWord, tailWord_302809, baseEnd_302809] using wordTrace_append hprefix tailTrace_302809
  have hstable : (prefixWord ++ tailWord_302809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302809).length < 2 ^ (prefixWord ++ tailWord_302809).sum := by decide
  have hdescent : baseEnd_302809 < baseStart_302809 := by decide
  rcases family_descends (prefixWord ++ tailWord_302809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302846 : List Nat := [4, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_302846 : Nat := 118140960795 + 302846 * 2 ^ 59
def prefixEnd_302846 : Nat := 4983230072969 + 3 ^ 40 * 302846 * 2
def baseEnd_302846 : Nat := 69113583240723265480997

theorem tailTrace_302846 : CollatzResearch.WordTrace tailWord_302846 prefixEnd_302846 69113583240723265480997 := by
  unfold tailWord_302846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380712632606017353014049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7363800707232092549408261 1380712632606017353014049)
  ·
    refine ⟨1035534474454513014760537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1380712632606017353014049 1035534474454513014760537)
    ·
      refine ⟨776650855840884761070403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1035534474454513014760537 776650855840884761070403)
      ·
        refine ⟨1164976283761327141605605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776650855840884761070403 1164976283761327141605605)
        ·
          refine ⟨218433053205248839051051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1164976283761327141605605 218433053205248839051051)
          ·
            refine ⟨327649579807873258576577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218433053205248839051051 327649579807873258576577)
            ·
              refine ⟨245737184855904943932433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327649579807873258576577 245737184855904943932433)
              ·
                refine ⟨184302888641928707949325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245737184855904943932433 184302888641928707949325)
                ·
                  refine ⟨69113583240723265480997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184302888641928707949325 69113583240723265480997)
                  ·
                    rfl

theorem cell21_302846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_302846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302846 prefixEnd_302846 := by exact prefixLift 302846
  have htrace : WordTrace (prefixWord ++ tailWord_302846) baseStart_302846 baseEnd_302846 := by
    simpa [prefixWord, tailWord_302846, baseEnd_302846] using wordTrace_append hprefix tailTrace_302846
  have hstable : (prefixWord ++ tailWord_302846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302846).length < 2 ^ (prefixWord ++ tailWord_302846).sum := by decide
  have hdescent : baseEnd_302846 < baseStart_302846 := by decide
  rcases family_descends (prefixWord ++ tailWord_302846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302851 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 6]
def baseStart_302851 : Nat := 118140960795 + 302851 * 2 ^ 59
def prefixEnd_302851 : Nat := 4983230072969 + 3 ^ 40 * 302851 * 2
def baseEnd_302851 : Nat := 69114724308844367897653

theorem tailTrace_302851 : CollatzResearch.WordTrace tailWord_302851 prefixEnd_302851 69114724308844367897653 := by
  unfold tailWord_302851
  simp only [CollatzResearch.WordTrace]
  refine ⟨11045883425830024678044407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7363922283886683118696271 11045883425830024678044407)
  ·
    refine ⟨16568825138745037017066611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11045883425830024678044407 16568825138745037017066611)
    ·
      refine ⟨24853237708117555525599917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16568825138745037017066611 24853237708117555525599917)
      ·
        refine ⟨9319964140544083322099969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24853237708117555525599917 9319964140544083322099969)
        ·
          refine ⟨6989973105408062491574977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9319964140544083322099969 6989973105408062491574977)
          ·
            refine ⟨5242479829056046868681233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6989973105408062491574977 5242479829056046868681233)
            ·
              refine ⟨3931859871792035151510925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5242479829056046868681233 3931859871792035151510925)
              ·
                refine ⟨1474447451922013181816597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3931859871792035151510925 1474447451922013181816597)
                ·
                  refine ⟨69114724308844367897653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1474447451922013181816597 69114724308844367897653)
                  ·
                    rfl

theorem cell21_302851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_302851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302851 prefixEnd_302851 := by exact prefixLift 302851
  have htrace : WordTrace (prefixWord ++ tailWord_302851) baseStart_302851 baseEnd_302851 := by
    simpa [prefixWord, tailWord_302851, baseEnd_302851] using wordTrace_append hprefix tailTrace_302851
  have hstable : (prefixWord ++ tailWord_302851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302851).length < 2 ^ (prefixWord ++ tailWord_302851).sum := by decide
  have hdescent : baseEnd_302851 < baseStart_302851 := by decide
  rcases family_descends (prefixWord ++ tailWord_302851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_302902 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_302902 : Nat := 118140960795 + 302902 * 2 ^ 59
def prefixEnd_302902 : Nat := 4983230072969 + 3 ^ 40 * 302902 * 2
def baseEnd_302902 : Nat := 69126363203679612547549

theorem tailTrace_302902 : CollatzResearch.WordTrace tailWord_302902 prefixEnd_302902 69126363203679612547549 := by
  unfold tailWord_302902
  simp only [CollatzResearch.WordTrace]
  refine ⟨690483971790328774259435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7365162365763506925433973 690483971790328774259435)
  ·
    refine ⟨1035725957685493161389153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 690483971790328774259435 1035725957685493161389153)
    ·
      refine ⟨776794468264119871041865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1035725957685493161389153 776794468264119871041865)
      ·
        refine ⟨582595851198089903281399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 776794468264119871041865 582595851198089903281399)
        ·
          refine ⟨873893776797134854922099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 582595851198089903281399 873893776797134854922099)
          ·
            refine ⟨1310840665195702282383149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873893776797134854922099 1310840665195702282383149)
            ·
              refine ⟨491565249448388355893681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1310840665195702282383149 491565249448388355893681)
              ·
                refine ⟨368673937086291266920261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 491565249448388355893681 368673937086291266920261)
                ·
                  refine ⟨69126363203679612547549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 368673937086291266920261 69126363203679612547549)
                  ·
                    rfl

theorem cell21_302902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_302902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_302902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_302902 prefixEnd_302902 := by exact prefixLift 302902
  have htrace : WordTrace (prefixWord ++ tailWord_302902) baseStart_302902 baseEnd_302902 := by
    simpa [prefixWord, tailWord_302902, baseEnd_302902] using wordTrace_append hprefix tailTrace_302902
  have hstable : (prefixWord ++ tailWord_302902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_302902).length < 2 ^ (prefixWord ++ tailWord_302902).sum := by decide
  have hdescent : baseEnd_302902 < baseStart_302902 := by decide
  rcases family_descends (prefixWord ++ tailWord_302902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303082 : List Nat := [3, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_303082 : Nat := 118140960795 + 303082 * 2 ^ 59
def prefixEnd_303082 : Nat := 4983230072969 + 3 ^ 40 * 303082 * 2
def baseEnd_303082 : Nat := 69167441656039299547181

theorem tailTrace_303082 : CollatzResearch.WordTrace tailWord_303082 prefixEnd_303082 69167441656039299547181 := by
  unfold tailWord_303082
  simp only [CollatzResearch.WordTrace]
  refine ⟨2763577171998287782425875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7369539125328767419802333 2763577171998287782425875)
  ·
    refine ⟨4145365757997431673638813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2763577171998287782425875 4145365757997431673638813)
    ·
      refine ⟨1554512159249036877614555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4145365757997431673638813 1554512159249036877614555)
      ·
        refine ⟨2331768238873555316421833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554512159249036877614555 2331768238873555316421833)
        ·
          refine ⟨1748826179155166487316375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2331768238873555316421833 1748826179155166487316375)
          ·
            refine ⟨2623239268732749730974563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748826179155166487316375 2623239268732749730974563)
            ·
              refine ⟨3934858903099124596461845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623239268732749730974563 3934858903099124596461845)
              ·
                refine ⟨184446511082771465459149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3934858903099124596461845 184446511082771465459149)
                ·
                  refine ⟨69167441656039299547181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184446511082771465459149 69167441656039299547181)
                  ·
                    rfl

theorem cell21_303082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_303082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303082 prefixEnd_303082 := by exact prefixLift 303082
  have htrace : WordTrace (prefixWord ++ tailWord_303082) baseStart_303082 baseEnd_303082 := by
    simpa [prefixWord, tailWord_303082, baseEnd_303082] using wordTrace_append hprefix tailTrace_303082
  have hstable : (prefixWord ++ tailWord_303082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303082).length < 2 ^ (prefixWord ++ tailWord_303082).sum := by decide
  have hdescent : baseEnd_303082 < baseStart_303082 := by decide
  rcases family_descends (prefixWord ++ tailWord_303082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303127 : List Nat := [1, 1, 3, 5, 2, 2, 7]
def baseStart_303127 : Nat := 118140960795 + 303127 * 2 ^ 59
def prefixEnd_303127 : Nat := 4983230072969 + 3 ^ 40 * 303127 * 2
def baseEnd_303127 : Nat := 7686412363236580144121

theorem tailTrace_303127 : CollatzResearch.WordTrace tailWord_303127 prefixEnd_303127 7686412363236580144121 := by
  unfold tailWord_303127
  simp only [CollatzResearch.WordTrace]
  refine ⟨11055949972830123815091635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7370633315220082543394423 11055949972830123815091635)
  ·
    refine ⟨16583924959245185722637453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11055949972830123815091635 16583924959245185722637453)
    ·
      refine ⟨6218971859716944645989045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16583924959245185722637453 6218971859716944645989045)
      ·
        refine ⟨583028611848463560561473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6218971859716944645989045 583028611848463560561473)
        ·
          refine ⟨437271458886347670421105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 583028611848463560561473 437271458886347670421105)
          ·
            refine ⟨327953594164760752815829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437271458886347670421105 327953594164760752815829)
            ·
              refine ⟨7686412363236580144121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 327953594164760752815829 7686412363236580144121)
              ·
                rfl

theorem cell21_303127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 7].length) (baseStart_303127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303127 prefixEnd_303127 := by exact prefixLift 303127
  have htrace : WordTrace (prefixWord ++ tailWord_303127) baseStart_303127 baseEnd_303127 := by
    simpa [prefixWord, tailWord_303127, baseEnd_303127] using wordTrace_append hprefix tailTrace_303127
  have hstable : (prefixWord ++ tailWord_303127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303127).length < 2 ^ (prefixWord ++ tailWord_303127).sum := by decide
  have hdescent : baseEnd_303127 < baseStart_303127 := by decide
  rcases family_descends (prefixWord ++ tailWord_303127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303141 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 5]
def baseStart_303141 : Nat := 118140960795 + 303141 * 2 ^ 59
def prefixEnd_303141 : Nat := 4983230072969 + 3 ^ 40 * 303141 * 2
def baseEnd_303141 : Nat := 69180906259868308063727

theorem tailTrace_303141 : CollatzResearch.WordTrace tailWord_303141 prefixEnd_303141 69180906259868308063727 := by
  unfold tailWord_303141
  simp only [CollatzResearch.WordTrace]
  refine ⟨11056460594779404206101277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7370973729852936137400851 11056460594779404206101277)
  ·
    refine ⟨4146172723042276577287979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11056460594779404206101277 4146172723042276577287979)
    ·
      refine ⟨6219259084563414865931969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4146172723042276577287979 6219259084563414865931969)
      ·
        refine ⟨4664444313422561149448977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6219259084563414865931969 4664444313422561149448977)
        ·
          refine ⟨3498333235066920862086733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4664444313422561149448977 3498333235066920862086733)
          ·
            refine ⟨1311874963150095323282525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3498333235066920862086733 1311874963150095323282525)
            ·
              refine ⟨491953111181285746230947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1311874963150095323282525 491953111181285746230947)
              ·
                refine ⟨737929666771928619346421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491953111181285746230947 737929666771928619346421)
                ·
                  refine ⟨69180906259868308063727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 737929666771928619346421 69180906259868308063727)
                  ·
                    rfl

theorem cell21_303141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_303141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303141 prefixEnd_303141 := by exact prefixLift 303141
  have htrace : WordTrace (prefixWord ++ tailWord_303141) baseStart_303141 baseEnd_303141 := by
    simpa [prefixWord, tailWord_303141, baseEnd_303141] using wordTrace_append hprefix tailTrace_303141
  have hstable : (prefixWord ++ tailWord_303141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303141).length < 2 ^ (prefixWord ++ tailWord_303141).sum := by decide
  have hdescent : baseEnd_303141 < baseStart_303141 := by decide
  rcases family_descends (prefixWord ++ tailWord_303141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303144 : List Nat := [2, 1, 5, 3, 1, 1, 2, 6]
def baseStart_303144 : Nat := 118140960795 + 303144 * 2 ^ 59
def prefixEnd_303144 : Nat := 4983230072969 + 3 ^ 40 * 303144 * 2
def baseEnd_303144 : Nat := 23060530300246989837907

theorem tailTrace_303144 : CollatzResearch.WordTrace tailWord_303144 prefixEnd_303144 23060530300246989837907 := by
  unfold tailWord_303144
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528285006884267859230243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7371046675845690478973657 5528285006884267859230243)
  ·
    refine ⟨8292427510326401788845365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528285006884267859230243 8292427510326401788845365)
    ·
      refine ⟨777415079093100167704253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8292427510326401788845365 777415079093100167704253)
      ·
        refine ⟨291530654659912562889095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 777415079093100167704253 291530654659912562889095)
        ·
          refine ⟨437295981989868844333643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291530654659912562889095 437295981989868844333643)
          ·
            refine ⟨655943972984803266500465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437295981989868844333643 655943972984803266500465)
            ·
              refine ⟨491957979738602449875349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 655943972984803266500465 491957979738602449875349)
              ·
                refine ⟨23060530300246989837907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 491957979738602449875349 23060530300246989837907)
                ·
                  rfl

theorem cell21_303144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_303144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303144 prefixEnd_303144 := by exact prefixLift 303144
  have htrace : WordTrace (prefixWord ++ tailWord_303144) baseStart_303144 baseEnd_303144 := by
    simpa [prefixWord, tailWord_303144, baseEnd_303144] using wordTrace_append hprefix tailTrace_303144
  have hstable : (prefixWord ++ tailWord_303144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303144).length < 2 ^ (prefixWord ++ tailWord_303144).sum := by decide
  have hdescent : baseEnd_303144 < baseStart_303144 := by decide
  rcases family_descends (prefixWord ++ tailWord_303144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303186 : List Nat := [3, 2, 2, 1, 4, 9]
def baseStart_303186 : Nat := 118140960795 + 303186 * 2 ^ 59
def prefixEnd_303186 : Nat := 4983230072969 + 3 ^ 40 * 303186 * 2
def baseEnd_303186 : Nat := 2562636143442897400505

theorem tailTrace_303186 : CollatzResearch.WordTrace tailWord_303186 prefixEnd_303186 2562636143442897400505 := by
  unfold tailWord_303186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2764525469904094222872353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7372067919744251260992941 2764525469904094222872353)
  ·
    refine ⟨2073394102428070667154265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2764525469904094222872353 2073394102428070667154265)
    ·
      refine ⟨1555045576821053000365699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2073394102428070667154265 1555045576821053000365699)
      ·
        refine ⟨2332568365231579500548549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555045576821053000365699 2332568365231579500548549)
        ·
          refine ⟨437356568480921156352853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2332568365231579500548549 437356568480921156352853)
          ·
            refine ⟨2562636143442897400505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 437356568480921156352853 2562636143442897400505)
            ·
              rfl

theorem cell21_303186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 9].length) (baseStart_303186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303186 prefixEnd_303186 := by exact prefixLift 303186
  have htrace : WordTrace (prefixWord ++ tailWord_303186) baseStart_303186 baseEnd_303186 := by
    simpa [prefixWord, tailWord_303186, baseEnd_303186] using wordTrace_append hprefix tailTrace_303186
  have hstable : (prefixWord ++ tailWord_303186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303186).length < 2 ^ (prefixWord ++ tailWord_303186).sum := by decide
  have hdescent : baseEnd_303186 < baseStart_303186 := by decide
  rcases family_descends (prefixWord ++ tailWord_303186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303265 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 4]
def baseStart_303265 : Nat := 118140960795 + 303265 * 2 ^ 59
def prefixEnd_303265 : Nat := 4983230072969 + 3 ^ 40 * 303265 * 2
def baseEnd_303265 : Nat := 69209204749271647996807

theorem tailTrace_303265 : CollatzResearch.WordTrace tailWord_303265 prefixEnd_303265 69209204749271647996807 := by
  unfold tailWord_303265
  simp only [CollatzResearch.WordTrace]
  refine ⟨11060983246330173383615249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7373988830886782255743499 11060983246330173383615249)
  ·
    refine ⟨8295737434747630037711437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11060983246330173383615249 8295737434747630037711437)
    ·
      refine ⟨3110901538030361264141789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8295737434747630037711437 3110901538030361264141789)
      ·
        refine ⟨1166588076761385474053171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3110901538030361264141789 1166588076761385474053171)
        ·
          refine ⟨1749882115142078211079757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1166588076761385474053171 1749882115142078211079757)
          ·
            refine ⟨656205793178279329154909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1749882115142078211079757 656205793178279329154909)
            ·
              refine ⟨246077172441854748433091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 656205793178279329154909 246077172441854748433091)
              ·
                refine ⟨369115758662782122649637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246077172441854748433091 369115758662782122649637)
                ·
                  refine ⟨69209204749271647996807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369115758662782122649637 69209204749271647996807)
                  ·
                    rfl

theorem cell21_303265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_303265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303265 prefixEnd_303265 := by exact prefixLift 303265
  have htrace : WordTrace (prefixWord ++ tailWord_303265) baseStart_303265 baseEnd_303265 := by
    simpa [prefixWord, tailWord_303265, baseEnd_303265] using wordTrace_append hprefix tailTrace_303265
  have hstable : (prefixWord ++ tailWord_303265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303265).length < 2 ^ (prefixWord ++ tailWord_303265).sum := by decide
  have hdescent : baseEnd_303265 < baseStart_303265 := by decide
  rcases family_descends (prefixWord ++ tailWord_303265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303285 : List Nat := [1, 3, 3, 4, 2, 1, 1, 3, 3]
def baseStart_303285 : Nat := 118140960795 + 303285 * 2 ^ 59
def prefixEnd_303285 : Nat := 4983230072969 + 3 ^ 40 * 303285 * 2
def baseEnd_303285 : Nat := 69213769021756057663433

theorem tailTrace_303285 : CollatzResearch.WordTrace tailWord_303285 prefixEnd_303285 69213769021756057663433 := by
  unfold tailWord_303285
  simp only [CollatzResearch.WordTrace]
  refine ⟨11061712706257716799343309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7374475137505144532895539 11061712706257716799343309)
  ·
    refine ⟨4148142264846643799753741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11061712706257716799343309 4148142264846643799753741)
    ·
      refine ⟨1555553349317491424907653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4148142264846643799753741 1555553349317491424907653)
      ·
        refine ⟨291666252997029642170185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1555553349317491424907653 291666252997029642170185)
        ·
          refine ⟨218749689747772231627639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 291666252997029642170185 218749689747772231627639)
          ·
            refine ⟨328124534621658347441459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218749689747772231627639 328124534621658347441459)
            ·
              refine ⟨492186801932487521162189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328124534621658347441459 492186801932487521162189)
              ·
                refine ⟨184570050724682820435821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 492186801932487521162189 184570050724682820435821)
                ·
                  refine ⟨69213769021756057663433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184570050724682820435821 69213769021756057663433)
                  ·
                    rfl

theorem cell21_303285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_303285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303285 prefixEnd_303285 := by exact prefixLift 303285
  have htrace : WordTrace (prefixWord ++ tailWord_303285) baseStart_303285 baseEnd_303285 := by
    simpa [prefixWord, tailWord_303285, baseEnd_303285] using wordTrace_append hprefix tailTrace_303285
  have hstable : (prefixWord ++ tailWord_303285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303285).length < 2 ^ (prefixWord ++ tailWord_303285).sum := by decide
  have hdescent : baseEnd_303285 < baseStart_303285 := by decide
  rcases family_descends (prefixWord ++ tailWord_303285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303307 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 4]
def baseStart_303307 : Nat := 118140960795 + 303307 * 2 ^ 59
def prefixEnd_303307 : Nat := 4983230072969 + 3 ^ 40 * 303307 * 2
def baseEnd_303307 : Nat := 69218789721488908296721

theorem tailTrace_303307 : CollatzResearch.WordTrace tailWord_303307 prefixEnd_303307 69218789721488908296721 := by
  unfold tailWord_303307
  simp only [CollatzResearch.WordTrace]
  refine ⟨11062515112178014556644175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7375010074785343037762783 11062515112178014556644175)
  ·
    refine ⟨16593772668267021834966263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11062515112178014556644175 16593772668267021834966263)
    ·
      refine ⟨24890659002400532752449395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16593772668267021834966263 24890659002400532752449395)
      ·
        refine ⟨37335988503600799128674093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24890659002400532752449395 37335988503600799128674093)
        ·
          refine ⟨14000995688850299673252785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37335988503600799128674093 14000995688850299673252785)
          ·
            refine ⟨10500746766637724754939589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14000995688850299673252785 10500746766637724754939589)
            ·
              refine ⟨1968890018744573391551173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10500746766637724754939589 1968890018744573391551173)
              ·
                refine ⟨369166878514607510915845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1968890018744573391551173 369166878514607510915845)
                ·
                  refine ⟨69218789721488908296721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369166878514607510915845 69218789721488908296721)
                  ·
                    rfl

theorem cell21_303307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 4].length) (baseStart_303307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303307 prefixEnd_303307 := by exact prefixLift 303307
  have htrace : WordTrace (prefixWord ++ tailWord_303307) baseStart_303307 baseEnd_303307 := by
    simpa [prefixWord, tailWord_303307, baseEnd_303307] using wordTrace_append hprefix tailTrace_303307
  have hstable : (prefixWord ++ tailWord_303307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303307).length < 2 ^ (prefixWord ++ tailWord_303307).sum := by decide
  have hdescent : baseEnd_303307 < baseStart_303307 := by decide
  rcases family_descends (prefixWord ++ tailWord_303307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303310 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_303310 : Nat := 118140960795 + 303310 * 2 ^ 59
def prefixEnd_303310 : Nat := 4983230072969 + 3 ^ 40 * 303310 * 2
def baseEnd_303310 : Nat := 69219474362361569746715

theorem tailTrace_303310 : CollatzResearch.WordTrace tailWord_303310 prefixEnd_303310 69219474362361569746715 := by
  unfold tailWord_303310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382828066395893258625423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7375083020778097379335589 1382828066395893258625423)
  ·
    refine ⟨2074242099593839887938135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1382828066395893258625423 2074242099593839887938135)
    ·
      refine ⟨3111363149390759831907203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2074242099593839887938135 3111363149390759831907203)
      ·
        refine ⟨4667044724086139747860805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3111363149390759831907203 4667044724086139747860805)
        ·
          refine ⟨875070885766151202723901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4667044724086139747860805 875070885766151202723901)
          ·
            refine ⟨328151582162306701021463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 875070885766151202723901 328151582162306701021463)
            ·
              refine ⟨492227373243460051532195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328151582162306701021463 492227373243460051532195)
              ·
                refine ⟨738341059865190077298293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492227373243460051532195 738341059865190077298293)
                ·
                  refine ⟨69219474362361569746715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 738341059865190077298293 69219474362361569746715)
                  ·
                    rfl

theorem cell21_303310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_303310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303310 prefixEnd_303310 := by exact prefixLift 303310
  have htrace : WordTrace (prefixWord ++ tailWord_303310) baseStart_303310 baseEnd_303310 := by
    simpa [prefixWord, tailWord_303310, baseEnd_303310] using wordTrace_append hprefix tailTrace_303310
  have hstable : (prefixWord ++ tailWord_303310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303310).length < 2 ^ (prefixWord ++ tailWord_303310).sum := by decide
  have hdescent : baseEnd_303310 < baseStart_303310 := by decide
  rcases family_descends (prefixWord ++ tailWord_303310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303321 : List Nat := [1, 2, 1, 2, 3, 1, 3, 8]
def baseStart_303321 : Nat := 118140960795 + 303321 * 2 ^ 59
def prefixEnd_303321 : Nat := 4983230072969 + 3 ^ 40 * 303321 * 2
def baseEnd_303321 : Nat := 23073994904075998354453

theorem tailTrace_303321 : CollatzResearch.WordTrace tailWord_303321 prefixEnd_303321 23073994904075998354453 := by
  unfold tailWord_303321
  simp only [CollatzResearch.WordTrace]
  refine ⟨11063025734127294947653817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7375350489418196631769211 11063025734127294947653817)
  ·
    refine ⟨8297269300595471210740363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11063025734127294947653817 8297269300595471210740363)
    ·
      refine ⟨12445903950893206816110545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8297269300595471210740363 12445903950893206816110545)
      ·
        refine ⟨9334427963169905112082909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12445903950893206816110545 9334427963169905112082909)
        ·
          refine ⟨3500410486188714417031091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9334427963169905112082909 3500410486188714417031091)
          ·
            refine ⟨5250615729283071625546637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500410486188714417031091 5250615729283071625546637)
            ·
              refine ⟨1968980898481151859579989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5250615729283071625546637 1968980898481151859579989)
              ·
                refine ⟨23073994904075998354453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1968980898481151859579989 23073994904075998354453)
                ·
                  rfl

theorem cell21_303321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 8].length) (baseStart_303321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303321 prefixEnd_303321 := by exact prefixLift 303321
  have htrace : WordTrace (prefixWord ++ tailWord_303321) baseStart_303321 baseEnd_303321 := by
    simpa [prefixWord, tailWord_303321, baseEnd_303321] using wordTrace_append hprefix tailTrace_303321
  have hstable : (prefixWord ++ tailWord_303321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303321).length < 2 ^ (prefixWord ++ tailWord_303321).sum := by decide
  have hdescent : baseEnd_303321 < baseStart_303321 := by decide
  rcases family_descends (prefixWord ++ tailWord_303321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303417 : List Nat := [1, 2, 1, 6, 1, 3, 1, 2, 4]
def baseStart_303417 : Nat := 118140960795 + 303417 * 2 ^ 59
def prefixEnd_303417 : Nat := 4983230072969 + 3 ^ 40 * 303417 * 2
def baseEnd_303417 : Nat := 69243893220153161463163

theorem tailTrace_303417 : CollatzResearch.WordTrace tailWord_303417 prefixEnd_303417 69243893220153161463163 := by
  unfold tailWord_303417
  simp only [CollatzResearch.WordTrace]
  refine ⟨11066527141779503343148505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7377684761186335562099003 11066527141779503343148505)
  ·
    refine ⟨8299895356334627507361379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11066527141779503343148505 8299895356334627507361379)
    ·
      refine ⟨12449843034501941261042069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8299895356334627507361379 12449843034501941261042069)
      ·
        refine ⟨583586392242278496611347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12449843034501941261042069 583586392242278496611347)
        ·
          refine ⟨875379588363417744917021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583586392242278496611347 875379588363417744917021)
          ·
            refine ⟨328267345636281654343883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 875379588363417744917021 328267345636281654343883)
            ·
              refine ⟨492401018454422481515825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328267345636281654343883 492401018454422481515825)
              ·
                refine ⟨369300763840816861136869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 492401018454422481515825 369300763840816861136869)
                ·
                  refine ⟨69243893220153161463163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369300763840816861136869 69243893220153161463163)
                  ·
                    rfl

theorem cell21_303417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_303417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303417 prefixEnd_303417 := by exact prefixLift 303417
  have htrace : WordTrace (prefixWord ++ tailWord_303417) baseStart_303417 baseEnd_303417 := by
    simpa [prefixWord, tailWord_303417, baseEnd_303417] using wordTrace_append hprefix tailTrace_303417
  have hstable : (prefixWord ++ tailWord_303417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303417).length < 2 ^ (prefixWord ++ tailWord_303417).sum := by decide
  have hdescent : baseEnd_303417 < baseStart_303417 := by decide
  rcases family_descends (prefixWord ++ tailWord_303417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303530 : List Nat := [3, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_303530 : Nat := 118140960795 + 303530 * 2 ^ 59
def prefixEnd_303530 : Nat := 4983230072969 + 3 ^ 40 * 303530 * 2
def baseEnd_303530 : Nat := 69269681359690076079599

theorem tailTrace_303530 : CollatzResearch.WordTrace tailWord_303530 prefixEnd_303530 69269681359690076079599 := by
  unfold tailWord_303530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2767662147592530910503011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7380432393580082428008029 2767662147592530910503011)
  ·
    refine ⟨4151493221388796365754517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2767662147592530910503011 4151493221388796365754517)
    ·
      refine ⟨194601244752599829644743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4151493221388796365754517 194601244752599829644743)
      ·
        refine ⟨291901867128899744467115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194601244752599829644743 291901867128899744467115)
        ·
          refine ⟨437852800693349616700673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291901867128899744467115 437852800693349616700673)
          ·
            refine ⟨328389600520012212525505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 437852800693349616700673 328389600520012212525505)
            ·
              refine ⟨246292200390009159394129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328389600520012212525505 246292200390009159394129)
              ·
                refine ⟨184719150292506869545597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246292200390009159394129 184719150292506869545597)
                ·
                  refine ⟨69269681359690076079599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184719150292506869545597 69269681359690076079599)
                  ·
                    rfl

theorem cell21_303530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_303530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303530 prefixEnd_303530 := by exact prefixLift 303530
  have htrace : WordTrace (prefixWord ++ tailWord_303530) baseStart_303530 baseEnd_303530 := by
    simpa [prefixWord, tailWord_303530, baseEnd_303530] using wordTrace_append hprefix tailTrace_303530
  have hstable : (prefixWord ++ tailWord_303530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303530).length < 2 ^ (prefixWord ++ tailWord_303530).sum := by decide
  have hdescent : baseEnd_303530 < baseStart_303530 := by decide
  rcases family_descends (prefixWord ++ tailWord_303530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303597 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 5]
def baseStart_303597 : Nat := 118140960795 + 303597 * 2 ^ 59
def prefixEnd_303597 : Nat := 4983230072969 + 3 ^ 40 * 303597 * 2
def baseEnd_303597 : Nat := 69284971672512848462795

theorem tailTrace_303597 : CollatzResearch.WordTrace tailWord_303597 prefixEnd_303597 69284971672512848462795 := by
  unfold tailWord_303597
  simp only [CollatzResearch.WordTrace]
  refine ⟨11073092281127394084701045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7382061520751596056467363 11073092281127394084701045)
  ·
    refine ⟨1038102401355693195440723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11073092281127394084701045 1038102401355693195440723)
    ·
      refine ⟨1557153602033539793161085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038102401355693195440723 1557153602033539793161085)
      ·
        refine ⟨583932600762577422435407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1557153602033539793161085 583932600762577422435407)
        ·
          refine ⟨875898901143866133653111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 583932600762577422435407 875898901143866133653111)
          ·
            refine ⟨1313848351715799200479667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875898901143866133653111 1313848351715799200479667)
            ·
              refine ⟨1970772527573698800719501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313848351715799200479667 1970772527573698800719501)
              ·
                refine ⟨739039697840137050269813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1970772527573698800719501 739039697840137050269813)
                ·
                  refine ⟨69284971672512848462795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 739039697840137050269813 69284971672512848462795)
                  ·
                    rfl

theorem cell21_303597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_303597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303597 prefixEnd_303597 := by exact prefixLift 303597
  have htrace : WordTrace (prefixWord ++ tailWord_303597) baseStart_303597 baseEnd_303597 := by
    simpa [prefixWord, tailWord_303597, baseEnd_303597] using wordTrace_append hprefix tailTrace_303597
  have hstable : (prefixWord ++ tailWord_303597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303597).length < 2 ^ (prefixWord ++ tailWord_303597).sum := by decide
  have hdescent : baseEnd_303597 < baseStart_303597 := by decide
  rcases family_descends (prefixWord ++ tailWord_303597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303662 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_303662 : Nat := 118140960795 + 303662 * 2 ^ 59
def prefixEnd_303662 : Nat := 4983230072969 + 3 ^ 40 * 303662 * 2
def baseEnd_303662 : Nat := 69299805558087179879329

theorem tailTrace_303662 : CollatzResearch.WordTrace tailWord_303662 prefixEnd_303662 69299805558087179879329 := by
  unfold tailWord_303662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384432878236488773227155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7383642017261273457211493 1384432878236488773227155)
  ·
    refine ⟨2076649317354733159840733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1384432878236488773227155 2076649317354733159840733)
    ·
      refine ⟨778743494008024934940275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2076649317354733159840733 778743494008024934940275)
      ·
        refine ⟨1168115241012037402410413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778743494008024934940275 1168115241012037402410413)
        ·
          refine ⟨438043215379514025903905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1168115241012037402410413 438043215379514025903905)
          ·
            refine ⟨328532411534635519427929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438043215379514025903905 328532411534635519427929)
            ·
              refine ⟨246399308650976639570947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328532411534635519427929 246399308650976639570947)
              ·
                refine ⟨369598962976464959356421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246399308650976639570947 369598962976464959356421)
                ·
                  refine ⟨69299805558087179879329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369598962976464959356421 69299805558087179879329)
                  ·
                    rfl

theorem cell21_303662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_303662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303662 prefixEnd_303662 := by exact prefixLift 303662
  have htrace : WordTrace (prefixWord ++ tailWord_303662) baseStart_303662 baseEnd_303662 := by
    simpa [prefixWord, tailWord_303662, baseEnd_303662] using wordTrace_append hprefix tailTrace_303662
  have hstable : (prefixWord ++ tailWord_303662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303662).length < 2 ^ (prefixWord ++ tailWord_303662).sum := by decide
  have hdescent : baseEnd_303662 < baseStart_303662 := by decide
  rcases family_descends (prefixWord ++ tailWord_303662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303710 : List Nat := [4, 4, 1, 2, 2, 1, 1, 6]
def baseStart_303710 : Nat := 118140960795 + 303710 * 2 ^ 59
def prefixEnd_303710 : Nat := 4983230072969 + 3 ^ 40 * 303710 * 2
def baseEnd_303710 : Nat := 23103586604016587693077

theorem tailTrace_303710 : CollatzResearch.WordTrace tailWord_303710 prefixEnd_303710 23103586604016587693077 := by
  unfold tailWord_303710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384651716214751797945573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7384809153145342922376389 1384651716214751797945573)
  ·
    refine ⟨259622196790265962114795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1384651716214751797945573 259622196790265962114795)
    ·
      refine ⟨389433295185398943172193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 259622196790265962114795 389433295185398943172193)
      ·
        refine ⟨292074971389049207379145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 389433295185398943172193 292074971389049207379145)
        ·
          refine ⟨219056228541786905534359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292074971389049207379145 219056228541786905534359)
          ·
            refine ⟨328584342812680358301539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219056228541786905534359 328584342812680358301539)
            ·
              refine ⟨492876514219020537452309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328584342812680358301539 492876514219020537452309)
              ·
                refine ⟨23103586604016587693077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 492876514219020537452309 23103586604016587693077)
                ·
                  rfl

theorem cell21_303710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_303710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303710 prefixEnd_303710 := by exact prefixLift 303710
  have htrace : WordTrace (prefixWord ++ tailWord_303710) baseStart_303710 baseEnd_303710 := by
    simpa [prefixWord, tailWord_303710, baseEnd_303710] using wordTrace_append hprefix tailTrace_303710
  have hstable : (prefixWord ++ tailWord_303710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303710).length < 2 ^ (prefixWord ++ tailWord_303710).sum := by decide
  have hdescent : baseEnd_303710 < baseStart_303710 := by decide
  rcases family_descends (prefixWord ++ tailWord_303710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303749 : List Nat := [1, 3, 1, 1, 4, 2, 1, 5, 3]
def baseStart_303749 : Nat := 118140960795 + 303749 * 2 ^ 59
def prefixEnd_303749 : Nat := 4983230072969 + 3 ^ 40 * 303749 * 2
def baseEnd_303749 : Nat := 69319660143394361929151

theorem tailTrace_303749 : CollatzResearch.WordTrace tailWord_303749 prefixEnd_303749 69319660143394361929151 := by
  unfold tailWord_303749
  simp only [CollatzResearch.WordTrace]
  refine ⟨11078636176576724044234301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7385757451051149362822867 11078636176576724044234301)
  ·
    refine ⟨4154488566216271516587863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11078636176576724044234301 4154488566216271516587863)
    ·
      refine ⟨6231732849324407274881795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4154488566216271516587863 6231732849324407274881795)
      ·
        refine ⟨9347599273986610912322693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231732849324407274881795 9347599273986610912322693)
        ·
          refine ⟨1752674863872489546060505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9347599273986610912322693 1752674863872489546060505)
          ·
            refine ⟨1314506147904367159545379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752674863872489546060505 1314506147904367159545379)
            ·
              refine ⟨1971759221856550739318069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314506147904367159545379 1971759221856550739318069)
              ·
                refine ⟨184852427049051631811069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1971759221856550739318069 184852427049051631811069)
                ·
                  refine ⟨69319660143394361929151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184852427049051631811069 69319660143394361929151)
                  ·
                    rfl

theorem cell21_303749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_303749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303749 prefixEnd_303749 := by exact prefixLift 303749
  have htrace : WordTrace (prefixWord ++ tailWord_303749) baseStart_303749 baseEnd_303749 := by
    simpa [prefixWord, tailWord_303749, baseEnd_303749] using wordTrace_append hprefix tailTrace_303749
  have hstable : (prefixWord ++ tailWord_303749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303749).length < 2 ^ (prefixWord ++ tailWord_303749).sum := by decide
  have hdescent : baseEnd_303749 < baseStart_303749 := by decide
  rcases family_descends (prefixWord ++ tailWord_303749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303780 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_303780 : Nat := 118140960795 + 303780 * 2 ^ 59
def prefixEnd_303780 : Nat := 4983230072969 + 3 ^ 40 * 303780 * 2
def baseEnd_303780 : Nat := 69326734765745196912421

theorem tailTrace_303780 : CollatzResearch.WordTrace tailWord_303780 prefixEnd_303780 69326734765745196912421 := by
  unfold tailWord_303780
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539883419732208169306397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7386511226309610892408529 5539883419732208169306397)
  ·
    refine ⟨2077456282399578063489899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5539883419732208169306397 2077456282399578063489899)
    ·
      refine ⟨3116184423599367095234849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2077456282399578063489899 3116184423599367095234849)
      ·
        refine ⟨2337138317699525321426137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3116184423599367095234849 2337138317699525321426137)
        ·
          refine ⟨1752853738274643991069603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2337138317699525321426137 1752853738274643991069603)
          ·
            refine ⟨2629280607411965986604405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752853738274643991069603 2629280607411965986604405)
            ·
              refine ⟨246495056944871811244163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2629280607411965986604405 246495056944871811244163)
              ·
                refine ⟨369742585417307716866245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246495056944871811244163 369742585417307716866245)
                ·
                  refine ⟨69326734765745196912421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369742585417307716866245 69326734765745196912421)
                  ·
                    rfl

theorem cell21_303780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_303780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303780 prefixEnd_303780 := by exact prefixLift 303780
  have htrace : WordTrace (prefixWord ++ tailWord_303780) baseStart_303780 baseEnd_303780 := by
    simpa [prefixWord, tailWord_303780, baseEnd_303780] using wordTrace_append hprefix tailTrace_303780
  have hstable : (prefixWord ++ tailWord_303780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303780).length < 2 ^ (prefixWord ++ tailWord_303780).sum := by decide
  have hdescent : baseEnd_303780 < baseStart_303780 := by decide
  rcases family_descends (prefixWord ++ tailWord_303780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303839 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 4]
def baseStart_303839 : Nat := 118140960795 + 303839 * 2 ^ 59
def prefixEnd_303839 : Nat := 4983230072969 + 3 ^ 40 * 303839 * 2
def baseEnd_303839 : Nat := 69340199369574205428967

theorem tailTrace_303839 : CollatzResearch.WordTrace tailWord_303839 prefixEnd_303839 69340199369574205428967 := by
  unfold tailWord_303839
  simp only [CollatzResearch.WordTrace]
  refine ⟨11081918746250669415010571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7387945830833779610007047 11081918746250669415010571)
  ·
    refine ⟨16622878119376004122515857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11081918746250669415010571 16622878119376004122515857)
    ·
      refine ⟨12467158589532003091886893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16622878119376004122515857 12467158589532003091886893)
      ·
        refine ⟨4675184471074501159457585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12467158589532003091886893 4675184471074501159457585)
        ·
          refine ⟨3506388353305875869593189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4675184471074501159457585 3506388353305875869593189)
          ·
            refine ⟨657447816244851725548723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3506388353305875869593189 657447816244851725548723)
            ·
              refine ⟨986171724367277588323085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 657447816244851725548723 986171724367277588323085)
              ·
                refine ⟨369814396637729095621157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 986171724367277588323085 369814396637729095621157)
                ·
                  refine ⟨69340199369574205428967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 369814396637729095621157 69340199369574205428967)
                  ·
                    rfl

theorem cell21_303839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 4].length) (baseStart_303839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303839 prefixEnd_303839 := by exact prefixLift 303839
  have htrace : WordTrace (prefixWord ++ tailWord_303839) baseStart_303839 baseEnd_303839 := by
    simpa [prefixWord, tailWord_303839, baseEnd_303839] using wordTrace_append hprefix tailTrace_303839
  have hstable : (prefixWord ++ tailWord_303839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303839).length < 2 ^ (prefixWord ++ tailWord_303839).sum := by decide
  have hdescent : baseEnd_303839 < baseStart_303839 := by decide
  rcases family_descends (prefixWord ++ tailWord_303839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303853 : List Nat := [1, 5, 1, 2, 1, 1, 1, 9]
def baseStart_303853 : Nat := 118140960795 + 303853 * 2 ^ 59
def prefixEnd_303853 : Nat := 4983230072969 + 3 ^ 40 * 303853 * 2
def baseEnd_303853 : Nat := 23114464786771097398535

theorem tailTrace_303853 : CollatzResearch.WordTrace tailWord_303853 prefixEnd_303853 23114464786771097398535 := by
  unfold tailWord_303853
  simp only [CollatzResearch.WordTrace]
  refine ⟨11082429368199949806020213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7388286245466633204013475 11082429368199949806020213)
  ·
    refine ⟨1038977753268745294314395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11082429368199949806020213 1038977753268745294314395)
    ·
      refine ⟨1558466629903117941471593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038977753268745294314395 1558466629903117941471593)
      ·
        refine ⟨1168849972427338456103695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1558466629903117941471593 1168849972427338456103695)
        ·
          refine ⟨1753274958641007684155543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168849972427338456103695 1753274958641007684155543)
          ·
            refine ⟨2629912437961511526233315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753274958641007684155543 2629912437961511526233315)
            ·
              refine ⟨3944868656942267289349973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629912437961511526233315 3944868656942267289349973)
              ·
                refine ⟨23114464786771097398535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3944868656942267289349973 23114464786771097398535)
                ·
                  rfl

theorem cell21_303853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 9].length) (baseStart_303853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303853 prefixEnd_303853 := by exact prefixLift 303853
  have htrace : WordTrace (prefixWord ++ tailWord_303853) baseStart_303853 baseEnd_303853 := by
    simpa [prefixWord, tailWord_303853, baseEnd_303853] using wordTrace_append hprefix tailTrace_303853
  have hstable : (prefixWord ++ tailWord_303853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303853).length < 2 ^ (prefixWord ++ tailWord_303853).sum := by decide
  have hdescent : baseEnd_303853 < baseStart_303853 := by decide
  rcases family_descends (prefixWord ++ tailWord_303853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_303918 : List Nat := [4, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_303918 : Nat := 118140960795 + 303918 * 2 ^ 59
def prefixEnd_303918 : Nat := 4983230072969 + 3 ^ 40 * 303918 * 2
def baseEnd_303918 : Nat := 69358228245887623612139

theorem tailTrace_303918 : CollatzResearch.WordTrace tailWord_303918 prefixEnd_303918 69358228245887623612139 := by
  unfold tailWord_303918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385600014120558238392051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7389866741976310604757605 1385600014120558238392051)
  ·
    refine ⟨2078400021180837357588077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1385600014120558238392051 2078400021180837357588077)
    ·
      refine ⟨779400007942814009095529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2078400021180837357588077 779400007942814009095529)
      ·
        refine ⟨584550005957110506821647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 779400007942814009095529 584550005957110506821647)
        ·
          refine ⟨876825008935665760232471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584550005957110506821647 876825008935665760232471)
          ·
            refine ⟨1315237513403498640348707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876825008935665760232471 1315237513403498640348707)
            ·
              refine ⟨1972856270105247960523061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315237513403498640348707 1972856270105247960523061)
              ·
                refine ⟨184955275322366996299037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1972856270105247960523061 184955275322366996299037)
                ·
                  refine ⟨69358228245887623612139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 184955275322366996299037 69358228245887623612139)
                  ·
                    rfl

theorem cell21_303918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_303918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_303918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_303918 prefixEnd_303918 := by exact prefixLift 303918
  have htrace : WordTrace (prefixWord ++ tailWord_303918) baseStart_303918 baseEnd_303918 := by
    simpa [prefixWord, tailWord_303918, baseEnd_303918] using wordTrace_append hprefix tailTrace_303918
  have hstable : (prefixWord ++ tailWord_303918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_303918).length < 2 ^ (prefixWord ++ tailWord_303918).sum := by decide
  have hdescent : baseEnd_303918 < baseStart_303918 := by decide
  rcases family_descends (prefixWord ++ tailWord_303918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304005 : List Nat := [1, 3, 1, 1, 3, 4, 2, 6]
def baseStart_304005 : Nat := 118140960795 + 304005 * 2 ^ 59
def prefixEnd_304005 : Nat := 4983230072969 + 3 ^ 40 * 304005 * 2
def baseEnd_304005 : Nat := 23126027610398268553987

theorem tailTrace_304005 : CollatzResearch.WordTrace tailWord_304005 prefixEnd_304005 23126027610398268553987 := by
  unfold tailWord_304005
  simp only [CollatzResearch.WordTrace]
  refine ⟨11087973263649279765553469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7391982175766186510368979 11087973263649279765553469)
  ·
    refine ⟨4157989973868479912082551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11087973263649279765553469 4157989973868479912082551)
    ·
      refine ⟨6236984960802719868123827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4157989973868479912082551 6236984960802719868123827)
      ·
        refine ⟨9355477441204079802185741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6236984960802719868123827 9355477441204079802185741)
        ·
          refine ⟨3508304040451529925819653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9355477441204079802185741 3508304040451529925819653)
          ·
            refine ⟨657807007584661861091185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3508304040451529925819653 657807007584661861091185)
            ·
              refine ⟨493355255688496395818389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 657807007584661861091185 493355255688496395818389)
              ·
                refine ⟨23126027610398268553987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 493355255688496395818389 23126027610398268553987)
                ·
                  rfl

theorem cell21_304005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 6].length) (baseStart_304005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304005 prefixEnd_304005 := by exact prefixLift 304005
  have htrace : WordTrace (prefixWord ++ tailWord_304005) baseStart_304005 baseEnd_304005 := by
    simpa [prefixWord, tailWord_304005, baseEnd_304005] using wordTrace_append hprefix tailTrace_304005
  have hstable : (prefixWord ++ tailWord_304005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304005).length < 2 ^ (prefixWord ++ tailWord_304005).sum := by decide
  have hdescent : baseEnd_304005 < baseStart_304005 := by decide
  rcases family_descends (prefixWord ++ tailWord_304005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304008 : List Nat := [2, 1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_304008 : Nat := 118140960795 + 304008 * 2 ^ 59
def prefixEnd_304008 : Nat := 4983230072969 + 3 ^ 40 * 304008 * 2
def baseEnd_304008 : Nat := 69378767472067467111955

theorem tailTrace_304008 : CollatzResearch.WordTrace tailWord_304008 prefixEnd_304008 69378767472067467111955 := by
  unfold tailWord_304008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5544041341319205638956339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7392055121758940851941785 5544041341319205638956339)
  ·
    refine ⟨8316062011978808458434509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5544041341319205638956339 8316062011978808458434509)
    ·
      refine ⟨3118523254492053171912941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8316062011978808458434509 3118523254492053171912941)
      ·
        refine ⟨1169446220434519939467353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3118523254492053171912941 1169446220434519939467353)
        ·
          refine ⟨877084665325889954600515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1169446220434519939467353 877084665325889954600515)
          ·
            refine ⟨1315626997988834931900773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877084665325889954600515 1315626997988834931900773)
            ·
              refine ⟨246680062122906549731395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1315626997988834931900773 246680062122906549731395)
              ·
                refine ⟨370020093184359824597093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246680062122906549731395 370020093184359824597093)
                ·
                  refine ⟨69378767472067467111955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370020093184359824597093 69378767472067467111955)
                  ·
                    rfl

theorem cell21_304008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_304008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304008 prefixEnd_304008 := by exact prefixLift 304008
  have htrace : WordTrace (prefixWord ++ tailWord_304008) baseStart_304008 baseEnd_304008 := by
    simpa [prefixWord, tailWord_304008, baseEnd_304008] using wordTrace_append hprefix tailTrace_304008
  have hstable : (prefixWord ++ tailWord_304008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304008).length < 2 ^ (prefixWord ++ tailWord_304008).sum := by decide
  have hdescent : baseEnd_304008 < baseStart_304008 := by decide
  rcases family_descends (prefixWord ++ tailWord_304008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304045 : List Nat := [1, 5, 2, 3, 2, 1, 2, 2, 3]
def baseStart_304045 : Nat := 118140960795 + 304045 * 2 ^ 59
def prefixEnd_304045 : Nat := 4983230072969 + 3 ^ 40 * 304045 * 2
def baseEnd_304045 : Nat := 69387211376163624995213

theorem tailTrace_304045 : CollatzResearch.WordTrace tailWord_304045 prefixEnd_304045 69387211376163624995213 := by
  unfold tailWord_304045
  simp only [CollatzResearch.WordTrace]
  refine ⟨11089432183504366597009589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7392954789002911064673059 11089432183504366597009589)
  ·
    refine ⟨1039634267203534368469649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11089432183504366597009589 1039634267203534368469649)
    ·
      refine ⟨779725700402650776352237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1039634267203534368469649 779725700402650776352237)
      ·
        refine ⟨292397137650994041132089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 779725700402650776352237 292397137650994041132089)
        ·
          refine ⟨219297853238245530849067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292397137650994041132089 219297853238245530849067)
          ·
            refine ⟨328946779857368296273601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219297853238245530849067 328946779857368296273601)
            ·
              refine ⟨246710084893026222205201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328946779857368296273601 246710084893026222205201)
              ·
                refine ⟨185032563669769666653901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246710084893026222205201 185032563669769666653901)
                ·
                  refine ⟨69387211376163624995213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185032563669769666653901 69387211376163624995213)
                  ·
                    rfl

theorem cell21_304045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_304045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304045 prefixEnd_304045 := by exact prefixLift 304045
  have htrace : WordTrace (prefixWord ++ tailWord_304045) baseStart_304045 baseEnd_304045 := by
    simpa [prefixWord, tailWord_304045, baseEnd_304045] using wordTrace_append hprefix tailTrace_304045
  have hstable : (prefixWord ++ tailWord_304045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304045).length < 2 ^ (prefixWord ++ tailWord_304045).sum := by decide
  have hdescent : baseEnd_304045 < baseStart_304045 := by decide
  rcases family_descends (prefixWord ++ tailWord_304045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304053 : List Nat := [1, 3, 3, 2, 1, 1, 3, 4, 3]
def baseStart_304053 : Nat := 118140960795 + 304053 * 2 ^ 59
def prefixEnd_304053 : Nat := 4983230072969 + 3 ^ 40 * 304053 * 2
def baseEnd_304053 : Nat := 69389037085157388861863

theorem tailTrace_304053 : CollatzResearch.WordTrace tailWord_304053 prefixEnd_304053 69389037085157388861863 := by
  unfold tailWord_304053
  simp only [CollatzResearch.WordTrace]
  refine ⟨11089723967475383963300813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7393149311650255975533875 11089723967475383963300813)
  ·
    refine ⟨4158646487803268986237805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11089723967475383963300813 4158646487803268986237805)
    ·
      refine ⟨1559492432926225869839177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4158646487803268986237805 1559492432926225869839177)
      ·
        refine ⟨1169619324694669402379383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1559492432926225869839177 1169619324694669402379383)
        ·
          refine ⟨1754428987042004103569075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1169619324694669402379383 1754428987042004103569075)
          ·
            refine ⟨2631643480563006155353613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754428987042004103569075 2631643480563006155353613)
            ·
              refine ⟨986866305211127308257605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2631643480563006155353613 986866305211127308257605)
              ·
                refine ⟨185037432227086370298301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 986866305211127308257605 185037432227086370298301)
                ·
                  refine ⟨69389037085157388861863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185037432227086370298301 69389037085157388861863)
                  ·
                    rfl

theorem cell21_304053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_304053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304053 prefixEnd_304053 := by exact prefixLift 304053
  have htrace : WordTrace (prefixWord ++ tailWord_304053) baseStart_304053 baseEnd_304053 := by
    simpa [prefixWord, tailWord_304053, baseEnd_304053] using wordTrace_append hprefix tailTrace_304053
  have hstable : (prefixWord ++ tailWord_304053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304053).length < 2 ^ (prefixWord ++ tailWord_304053).sum := by decide
  have hdescent : baseEnd_304053 < baseStart_304053 := by decide
  rcases family_descends (prefixWord ++ tailWord_304053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304081 : List Nat := [1, 2, 2, 1, 2, 1, 7, 5]
def baseStart_304081 : Nat := 118140960795 + 304081 * 2 ^ 59
def prefixEnd_304081 : Nat := 4983230072969 + 3 ^ 40 * 304081 * 2
def baseEnd_304081 : Nat := 23131809022211854131713

theorem tailTrace_304081 : CollatzResearch.WordTrace tailWord_304081 prefixEnd_304081 23131809022211854131713 := by
  unfold tailWord_304081
  simp only [CollatzResearch.WordTrace]
  refine ⟨11090745211373944745320097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7393830140915963163546731 11090745211373944745320097)
  ·
    refine ⟨8318058908530458558990073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11090745211373944745320097 8318058908530458558990073)
    ·
      refine ⟨6238544181397843919242555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8318058908530458558990073 6238544181397843919242555)
      ·
        refine ⟨9357816272096765878863833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6238544181397843919242555 9357816272096765878863833)
        ·
          refine ⟨7018362204072574409147875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9357816272096765878863833 7018362204072574409147875)
          ·
            refine ⟨10527543306108861613721813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7018362204072574409147875 10527543306108861613721813)
            ·
              refine ⟨246739296236926444071605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10527543306108861613721813 246739296236926444071605)
              ·
                refine ⟨23131809022211854131713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 246739296236926444071605 23131809022211854131713)
                ·
                  rfl

theorem cell21_304081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 5].length) (baseStart_304081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304081 prefixEnd_304081 := by exact prefixLift 304081
  have htrace : WordTrace (prefixWord ++ tailWord_304081) baseStart_304081 baseEnd_304081 := by
    simpa [prefixWord, tailWord_304081, baseEnd_304081] using wordTrace_append hprefix tailTrace_304081
  have hstable : (prefixWord ++ tailWord_304081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304081).length < 2 ^ (prefixWord ++ tailWord_304081).sum := by decide
  have hdescent : baseEnd_304081 < baseStart_304081 := by decide
  rcases family_descends (prefixWord ++ tailWord_304081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304098 : List Nat := [3, 3, 3, 1, 1, 2, 8]
def baseStart_304098 : Nat := 118140960795 + 304098 * 2 ^ 59
def prefixEnd_304098 : Nat := 4983230072969 + 3 ^ 40 * 304098 * 2
def baseEnd_304098 : Nat := 7711034077583034512419

theorem tailTrace_304098 : CollatzResearch.WordTrace tailWord_304098 prefixEnd_304098 7711034077583034512419 := by
  unfold tailWord_304098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2772841313078089162172237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7394243501541571099125965 2772841313078089162172237)
  ·
    refine ⟨1039815492404283435814589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2772841313078089162172237 1039815492404283435814589)
    ·
      refine ⟨389930809651606288430471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1039815492404283435814589 389930809651606288430471)
      ·
        refine ⟨584896214477409432645707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389930809651606288430471 584896214477409432645707)
        ·
          refine ⟨877344321716114148968561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584896214477409432645707 877344321716114148968561)
          ·
            refine ⟨658008241287085611726421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 877344321716114148968561 658008241287085611726421)
            ·
              refine ⟨7711034077583034512419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 658008241287085611726421 7711034077583034512419)
              ·
                rfl

theorem cell21_304098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 8].length) (baseStart_304098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304098 prefixEnd_304098 := by exact prefixLift 304098
  have htrace : WordTrace (prefixWord ++ tailWord_304098) baseStart_304098 baseEnd_304098 := by
    simpa [prefixWord, tailWord_304098, baseEnd_304098] using wordTrace_append hprefix tailTrace_304098
  have hstable : (prefixWord ++ tailWord_304098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304098).length < 2 ^ (prefixWord ++ tailWord_304098).sum := by decide
  have hdescent : baseEnd_304098 < baseStart_304098 := by decide
  rcases family_descends (prefixWord ++ tailWord_304098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304101 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 4]
def baseStart_304101 : Nat := 118140960795 + 304101 * 2 ^ 59
def prefixEnd_304101 : Nat := 4983230072969 + 3 ^ 40 * 304101 * 2
def baseEnd_304101 : Nat := 69399991339119972061765

theorem tailTrace_304101 : CollatzResearch.WordTrace tailWord_304101 prefixEnd_304101 69399991339119972061765 := by
  unfold tailWord_304101
  simp only [CollatzResearch.WordTrace]
  refine ⟨11091474671301488161048157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7394316447534325440698771 11091474671301488161048157)
  ·
    refine ⟨4159303001738058060393059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11091474671301488161048157 4159303001738058060393059)
    ·
      refine ⟨6238954502607087090589589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4159303001738058060393059 6238954502607087090589589)
      ·
        refine ⟨292450992309707207371387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6238954502607087090589589 292450992309707207371387)
        ·
          refine ⟨438676488464560811057081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292450992309707207371387 438676488464560811057081)
          ·
            refine ⟨329007366348420608292811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 438676488464560811057081 329007366348420608292811)
            ·
              refine ⟨493511049522630912439217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329007366348420608292811 493511049522630912439217)
              ·
                refine ⟨370133287141973184329413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 493511049522630912439217 370133287141973184329413)
                ·
                  refine ⟨69399991339119972061765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370133287141973184329413 69399991339119972061765)
                  ·
                    rfl

theorem cell21_304101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_304101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304101 prefixEnd_304101 := by exact prefixLift 304101
  have htrace : WordTrace (prefixWord ++ tailWord_304101) baseStart_304101 baseEnd_304101 := by
    simpa [prefixWord, tailWord_304101, baseEnd_304101] using wordTrace_append hprefix tailTrace_304101
  have hstable : (prefixWord ++ tailWord_304101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304101).length < 2 ^ (prefixWord ++ tailWord_304101).sum := by decide
  have hdescent : baseEnd_304101 < baseStart_304101 := by decide
  rcases family_descends (prefixWord ++ tailWord_304101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304233 : List Nat := [1, 2, 1, 1, 1, 8, 1, 6]
def baseStart_304233 : Nat := 118140960795 + 304233 * 2 ^ 59
def prefixEnd_304233 : Nat := 4983230072969 + 3 ^ 40 * 304233 * 2
def baseEnd_304233 : Nat := 23143371845839025287165

theorem tailTrace_304233 : CollatzResearch.WordTrace tailWord_304233 prefixEnd_304233 23143371845839025287165 := by
  unfold tailWord_304233
  simp only [CollatzResearch.WordTrace]
  refine ⟨11096289106823274704853353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7397526071215516469902235 11096289106823274704853353)
  ·
    refine ⟨8322216830117456028640015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11096289106823274704853353 8322216830117456028640015)
    ·
      refine ⟨12483325245176184042960023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8322216830117456028640015 12483325245176184042960023)
      ·
        refine ⟨18724987867764276064440035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12483325245176184042960023 18724987867764276064440035)
        ·
          refine ⟨28087481801646414096660053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18724987867764276064440035 28087481801646414096660053)
          ·
            refine ⟨329150177363043915195235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 28087481801646414096660053 329150177363043915195235)
            ·
              refine ⟨493725266044565872792853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329150177363043915195235 493725266044565872792853)
              ·
                refine ⟨23143371845839025287165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 493725266044565872792853 23143371845839025287165)
                ·
                  rfl

theorem cell21_304233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 6].length) (baseStart_304233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304233 prefixEnd_304233 := by exact prefixLift 304233
  have htrace : WordTrace (prefixWord ++ tailWord_304233) baseStart_304233 baseEnd_304233 := by
    simpa [prefixWord, tailWord_304233, baseEnd_304233] using wordTrace_append hprefix tailTrace_304233
  have hstable : (prefixWord ++ tailWord_304233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304233).length < 2 ^ (prefixWord ++ tailWord_304233).sum := by decide
  have hdescent : baseEnd_304233 < baseStart_304233 := by decide
  rcases family_descends (prefixWord ++ tailWord_304233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304247 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 5]
def baseStart_304247 : Nat := 118140960795 + 304247 * 2 ^ 59
def prefixEnd_304247 : Nat := 4983230072969 + 3 ^ 40 * 304247 * 2
def baseEnd_304247 : Nat := 69433310528256162628133

theorem tailTrace_304247 : CollatzResearch.WordTrace tailWord_304247 prefixEnd_304247 69433310528256162628133 := by
  unfold tailWord_304247
  simp only [CollatzResearch.WordTrace]
  refine ⟨11096799728772555095862995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7397866485848370063908663 11096799728772555095862995)
  ·
    refine ⟨16645199593158832643794493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11096799728772555095862995 16645199593158832643794493)
    ·
      refine ⟨6241949847434562241422935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16645199593158832643794493 6241949847434562241422935)
      ·
        refine ⟨9362924771151843362134403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6241949847434562241422935 9362924771151843362134403)
        ·
          refine ⟨14044387156727765043201605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9362924771151843362134403 14044387156727765043201605)
          ·
            refine ⟨2633322591886455945600301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14044387156727765043201605 2633322591886455945600301)
            ·
              refine ⟨987495971957420979600113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2633322591886455945600301 987495971957420979600113)
              ·
                refine ⟨740621978968065734700085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987495971957420979600113 740621978968065734700085)
                ·
                  refine ⟨69433310528256162628133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 740621978968065734700085 69433310528256162628133)
                  ·
                    rfl

theorem cell21_304247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_304247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304247 prefixEnd_304247 := by exact prefixLift 304247
  have htrace : WordTrace (prefixWord ++ tailWord_304247) baseStart_304247 baseEnd_304247 := by
    simpa [prefixWord, tailWord_304247, baseEnd_304247] using wordTrace_append hprefix tailTrace_304247
  have hstable : (prefixWord ++ tailWord_304247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304247).length < 2 ^ (prefixWord ++ tailWord_304247).sum := by decide
  have hdescent : baseEnd_304247 < baseStart_304247 := by decide
  rcases family_descends (prefixWord ++ tailWord_304247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304416 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_304416 : Nat := 118140960795 + 304416 * 2 ^ 59
def prefixEnd_304416 : Nat := 4983230072969 + 3 ^ 40 * 304416 * 2
def baseEnd_304416 : Nat := 69471878630749424311121

theorem tailTrace_304416 : CollatzResearch.WordTrace tailWord_304416 prefixEnd_304416 69471878630749424311121 := by
  unfold tailWord_304416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5551481832580148479382551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7401975776773531305843401 5551481832580148479382551)
  ·
    refine ⟨8327222748870222719073827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5551481832580148479382551 8327222748870222719073827)
    ·
      refine ⟨12490834123305334078610741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8327222748870222719073827 12490834123305334078610741)
      ·
        refine ⟨1171015699059875069869757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12490834123305334078610741 1171015699059875069869757)
        ·
          refine ⟨439130887147453151201159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1171015699059875069869757 439130887147453151201159)
          ·
            refine ⟨658696330721179726801739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439130887147453151201159 658696330721179726801739)
            ·
              refine ⟨988044496081769590202609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658696330721179726801739 988044496081769590202609)
              ·
                refine ⟨741033372061327192651957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988044496081769590202609 741033372061327192651957)
                ·
                  refine ⟨69471878630749424311121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741033372061327192651957 69471878630749424311121)
                  ·
                    rfl

theorem cell21_304416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_304416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304416 prefixEnd_304416 := by exact prefixLift 304416
  have htrace : WordTrace (prefixWord ++ tailWord_304416) baseStart_304416 baseEnd_304416 := by
    simpa [prefixWord, tailWord_304416, baseEnd_304416] using wordTrace_append hprefix tailTrace_304416
  have hstable : (prefixWord ++ tailWord_304416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304416).length < 2 ^ (prefixWord ++ tailWord_304416).sum := by decide
  have hdescent : baseEnd_304416 < baseStart_304416 := by decide
  rcases family_descends (prefixWord ++ tailWord_304416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304433 : List Nat := [1, 2, 2, 3, 3, 2, 2, 3, 3]
def baseStart_304433 : Nat := 118140960795 + 304433 * 2 ^ 59
def prefixEnd_304433 : Nat := 4983230072969 + 3 ^ 40 * 304433 * 2
def baseEnd_304433 : Nat := 69475758262361172527753

theorem tailTrace_304433 : CollatzResearch.WordTrace tailWord_304433 prefixEnd_304433 69475758262361172527753 := by
  unfold tailWord_304433
  simp only [CollatzResearch.WordTrace]
  refine ⟨11103583706098708862133953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7402389137399139241422635 11103583706098708862133953)
  ·
    refine ⟨8327687779574031646600465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11103583706098708862133953 8327687779574031646600465)
    ·
      refine ⟨6245765834680523734950349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8327687779574031646600465 6245765834680523734950349)
      ·
        refine ⟨2342162188005196400606381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6245765834680523734950349 2342162188005196400606381)
        ·
          refine ⟨878310820501948650227393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2342162188005196400606381 878310820501948650227393)
          ·
            refine ⟨658733115376461487670545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878310820501948650227393 658733115376461487670545)
            ·
              refine ⟨494049836532346115752909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658733115376461487670545 494049836532346115752909)
              ·
                refine ⟨185268688699629793407341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 494049836532346115752909 185268688699629793407341)
                ·
                  refine ⟨69475758262361172527753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185268688699629793407341 69475758262361172527753)
                  ·
                    rfl

theorem cell21_304433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_304433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304433 prefixEnd_304433 := by exact prefixLift 304433
  have htrace : WordTrace (prefixWord ++ tailWord_304433) baseStart_304433 baseEnd_304433 := by
    simpa [prefixWord, tailWord_304433, baseEnd_304433] using wordTrace_append hprefix tailTrace_304433
  have hstable : (prefixWord ++ tailWord_304433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304433).length < 2 ^ (prefixWord ++ tailWord_304433).sum := by decide
  have hdescent : baseEnd_304433 < baseStart_304433 := by decide
  rcases family_descends (prefixWord ++ tailWord_304433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304444 : List Nat := [2, 2, 2, 2, 1, 4, 8]
def baseStart_304444 : Nat := 118140960795 + 304444 * 2 ^ 59
def prefixEnd_304444 : Nat := 4983230072969 + 3 ^ 40 * 304444 * 2
def baseEnd_304444 : Nat := 7719807623580844204933

theorem tailTrace_304444 : CollatzResearch.WordTrace tailWord_304444 prefixEnd_304444 7719807623580844204933 := by
  unfold tailWord_304444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5551992454529428870392193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7402656606039238493856257 5551992454529428870392193)
  ·
    refine ⟨4163994340897071652794145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5551992454529428870392193 4163994340897071652794145)
    ·
      refine ⟨3122995755672803739595609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4163994340897071652794145 3122995755672803739595609)
      ·
        refine ⟨2342246816754602804696707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3122995755672803739595609 2342246816754602804696707)
        ·
          refine ⟨3513370225131904207045061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342246816754602804696707 3513370225131904207045061)
          ·
            refine ⟨658756917212232038820949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3513370225131904207045061 658756917212232038820949)
            ·
              refine ⟨7719807623580844204933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 658756917212232038820949 7719807623580844204933)
              ·
                rfl

theorem cell21_304444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 8].length) (baseStart_304444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304444 prefixEnd_304444 := by exact prefixLift 304444
  have htrace : WordTrace (prefixWord ++ tailWord_304444) baseStart_304444 baseEnd_304444 := by
    simpa [prefixWord, tailWord_304444, baseEnd_304444] using wordTrace_append hprefix tailTrace_304444
  have hstable : (prefixWord ++ tailWord_304444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304444).length < 2 ^ (prefixWord ++ tailWord_304444).sum := by decide
  have hdescent : baseEnd_304444 < baseStart_304444 := by decide
  rcases family_descends (prefixWord ++ tailWord_304444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304447 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 4]
def baseStart_304447 : Nat := 118140960795 + 304447 * 2 ^ 59
def prefixEnd_304447 : Nat := 4983230072969 + 3 ^ 40 * 304447 * 2
def baseEnd_304447 : Nat := 69478953253100259294391

theorem tailTrace_304447 : CollatzResearch.WordTrace tailWord_304447 prefixEnd_304447 69478953253100259294391 := by
  unfold tailWord_304447
  simp only [CollatzResearch.WordTrace]
  refine ⟨11104094328047989253143595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7402729552031992835429063 11104094328047989253143595)
  ·
    refine ⟨16656141492071983879715393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11104094328047989253143595 16656141492071983879715393)
    ·
      refine ⟨12492106119053987909786545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16656141492071983879715393 12492106119053987909786545)
      ·
        refine ⟨9369079589290490932339909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12492106119053987909786545 9369079589290490932339909)
        ·
          refine ⟨1756702422991967049813733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9369079589290490932339909 1756702422991967049813733)
          ·
            refine ⟨329381704310993821840075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1756702422991967049813733 329381704310993821840075)
            ·
              refine ⟨494072556466490732760113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329381704310993821840075 494072556466490732760113)
              ·
                refine ⟨370554417349868049570085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494072556466490732760113 370554417349868049570085)
                ·
                  refine ⟨69478953253100259294391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370554417349868049570085 69478953253100259294391)
                  ·
                    rfl

theorem cell21_304447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 4].length) (baseStart_304447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304447 prefixEnd_304447 := by exact prefixLift 304447
  have htrace : WordTrace (prefixWord ++ tailWord_304447) baseStart_304447 baseEnd_304447 := by
    simpa [prefixWord, tailWord_304447, baseEnd_304447] using wordTrace_append hprefix tailTrace_304447
  have hstable : (prefixWord ++ tailWord_304447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304447).length < 2 ^ (prefixWord ++ tailWord_304447).sum := by decide
  have hdescent : baseEnd_304447 < baseStart_304447 := by decide
  rcases family_descends (prefixWord ++ tailWord_304447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304470 : List Nat := [5, 2, 3, 1, 2, 1, 2, 5]
def baseStart_304470 : Nat := 118140960795 + 304470 * 2 ^ 59
def prefixEnd_304470 : Nat := 4983230072969 + 3 ^ 40 * 304470 * 2
def baseEnd_304470 : Nat := 23161400722152443470337

theorem tailTrace_304470 : CollatzResearch.WordTrace tailWord_304470 prefixEnd_304470 23161400722152443470337 := by
  unfold tailWord_304470
  simp only [CollatzResearch.WordTrace]
  refine ⟨694058325435291511326929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7403288804643109454153909 694058325435291511326929)
  ·
    refine ⟨520543744076468633495197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 694058325435291511326929 520543744076468633495197)
    ·
      refine ⟨195203904028675737560699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 520543744076468633495197 195203904028675737560699)
      ·
        refine ⟨292805856043013606341049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195203904028675737560699 292805856043013606341049)
        ·
          refine ⟨219604392032260204755787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292805856043013606341049 219604392032260204755787)
          ·
            refine ⟨329406588048390307133681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219604392032260204755787 329406588048390307133681)
            ·
              refine ⟨247054941036292730350261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329406588048390307133681 247054941036292730350261)
              ·
                refine ⟨23161400722152443470337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247054941036292730350261 23161400722152443470337)
                ·
                  rfl

theorem cell21_304470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_304470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304470 prefixEnd_304470 := by exact prefixLift 304470
  have htrace : WordTrace (prefixWord ++ tailWord_304470) baseStart_304470 baseEnd_304470 := by
    simpa [prefixWord, tailWord_304470, baseEnd_304470] using wordTrace_append hprefix tailTrace_304470
  have hstable : (prefixWord ++ tailWord_304470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304470).length < 2 ^ (prefixWord ++ tailWord_304470).sum := by decide
  have hdescent : baseEnd_304470 < baseStart_304470 := by decide
  rcases family_descends (prefixWord ++ tailWord_304470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304509 : List Nat := [1, 4, 1, 1, 2, 2, 5, 2, 3]
def baseStart_304509 : Nat := 118140960795 + 304509 * 2 ^ 59
def prefixEnd_304509 : Nat := 4983230072969 + 3 ^ 40 * 304509 * 2
def baseEnd_304509 : Nat := 69493102497801929260931

theorem tailTrace_304509 : CollatzResearch.WordTrace tailWord_304509 prefixEnd_304509 69493102497801929260931 := by
  unfold tailWord_304509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106355653823373841900581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7404237102548915894600387 11106355653823373841900581)
  ·
    refine ⟨2082441685091882595356359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11106355653823373841900581 2082441685091882595356359)
    ·
      refine ⟨3123662527637823893034539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082441685091882595356359 3123662527637823893034539)
      ·
        refine ⟨4685493791456735839551809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123662527637823893034539 4685493791456735839551809)
        ·
          refine ⟨3514120343592551879663857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4685493791456735839551809 3514120343592551879663857)
          ·
            refine ⟨2635590257694413909747893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3514120343592551879663857 2635590257694413909747893)
            ·
              refine ⟨247086586658851304038865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2635590257694413909747893 247086586658851304038865)
              ·
                refine ⟨185314939994138478029149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247086586658851304038865 185314939994138478029149)
                ·
                  refine ⟨69493102497801929260931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185314939994138478029149 69493102497801929260931)
                  ·
                    rfl

theorem cell21_304509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_304509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304509 prefixEnd_304509 := by exact prefixLift 304509
  have htrace : WordTrace (prefixWord ++ tailWord_304509) baseStart_304509 baseEnd_304509 := by
    simpa [prefixWord, tailWord_304509, baseEnd_304509] using wordTrace_append hprefix tailTrace_304509
  have hstable : (prefixWord ++ tailWord_304509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304509).length < 2 ^ (prefixWord ++ tailWord_304509).sum := by decide
  have hdescent : baseEnd_304509 < baseStart_304509 := by decide
  rcases family_descends (prefixWord ++ tailWord_304509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304520 : List Nat := [2, 1, 3, 3, 1, 2, 1, 8]
def baseStart_304520 : Nat := 118140960795 + 304520 * 2 ^ 59
def prefixEnd_304520 : Nat := 4983230072969 + 3 ^ 40 * 304520 * 2
def baseEnd_304520 : Nat := 23165204282556118192525

theorem tailTrace_304520 : CollatzResearch.WordTrace tailWord_304520 prefixEnd_304520 23165204282556118192525 := by
  unfold tailWord_304520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553378428391761360275507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7404504571189015147034009 5553378428391761360275507)
  ·
    refine ⟨8330067642587642040413261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5553378428391761360275507 8330067642587642040413261)
    ·
      refine ⟨3123775365970365765154973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8330067642587642040413261 3123775365970365765154973)
      ·
        refine ⟨1171415762238887161933115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3123775365970365765154973 1171415762238887161933115)
        ·
          refine ⟨1757123643358330742899673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171415762238887161933115 1757123643358330742899673)
          ·
            refine ⟨1317842732518748057174755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1757123643358330742899673 1317842732518748057174755)
            ·
              refine ⟨1976764098778122085762133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317842732518748057174755 1976764098778122085762133)
              ·
                refine ⟨23165204282556118192525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1976764098778122085762133 23165204282556118192525)
                ·
                  rfl

theorem cell21_304520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_304520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304520 prefixEnd_304520 := by exact prefixLift 304520
  have htrace : WordTrace (prefixWord ++ tailWord_304520) baseStart_304520 baseEnd_304520 := by
    simpa [prefixWord, tailWord_304520, baseEnd_304520] using wordTrace_append hprefix tailTrace_304520
  have hstable : (prefixWord ++ tailWord_304520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304520).length < 2 ^ (prefixWord ++ tailWord_304520).sum := by decide
  have hdescent : baseEnd_304520 < baseStart_304520 := by decide
  rcases family_descends (prefixWord ++ tailWord_304520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304661 : List Nat := [1, 3, 2, 1, 3, 4, 1, 3, 3]
def baseStart_304661 : Nat := 118140960795 + 304661 * 2 ^ 59
def prefixEnd_304661 : Nat := 4983230072969 + 3 ^ 40 * 304661 * 2
def baseEnd_304661 : Nat := 69527790968683442727287

theorem tailTrace_304661 : CollatzResearch.WordTrace tailWord_304661 prefixEnd_304661 69527790968683442727287 := by
  unfold tailWord_304661
  simp only [CollatzResearch.WordTrace]
  refine ⟨11111899549272703801433837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7407933032848469200955891 11111899549272703801433837)
  ·
    refine ⟨4166962330977263925537689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11111899549272703801433837 4166962330977263925537689)
    ·
      refine ⟨3125221748232947944153267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4166962330977263925537689 3125221748232947944153267)
      ·
        refine ⟨4687832622349421916229901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125221748232947944153267 4687832622349421916229901)
        ·
          refine ⟨1757937233381033218586213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4687832622349421916229901 1757937233381033218586213)
          ·
            refine ⟨329613231258943728484915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1757937233381033218586213 329613231258943728484915)
            ·
              refine ⟨494419846888415592727373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329613231258943728484915 494419846888415592727373)
              ·
                refine ⟨185407442583155847272765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 494419846888415592727373 185407442583155847272765)
                ·
                  refine ⟨69527790968683442727287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185407442583155847272765 69527790968683442727287)
                  ·
                    rfl

theorem cell21_304661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_304661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304661 prefixEnd_304661 := by exact prefixLift 304661
  have htrace : WordTrace (prefixWord ++ tailWord_304661) baseStart_304661 baseEnd_304661 := by
    simpa [prefixWord, tailWord_304661, baseEnd_304661] using wordTrace_append hprefix tailTrace_304661
  have hstable : (prefixWord ++ tailWord_304661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304661).length < 2 ^ (prefixWord ++ tailWord_304661).sum := by decide
  have hdescent : baseEnd_304661 < baseStart_304661 := by decide
  rcases family_descends (prefixWord ++ tailWord_304661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304672 : List Nat := [2, 1, 1, 6, 1, 1, 9]
def baseStart_304672 : Nat := 118140960795 + 304672 * 2 ^ 59
def prefixEnd_304672 : Nat := 4983230072969 + 3 ^ 40 * 304672 * 2
def baseEnd_304672 : Nat := 7725589035394429782659

theorem tailTrace_304672 : CollatzResearch.WordTrace tailWord_304672 prefixEnd_304672 7725589035394429782659 := by
  unfold tailWord_304672
  simp only [CollatzResearch.WordTrace]
  refine ⟨5556150376116426340042135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7408200501488568453389513 5556150376116426340042135)
  ·
    refine ⟨8334225564174639510063203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5556150376116426340042135 8334225564174639510063203)
    ·
      refine ⟨12501338346261959265094805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8334225564174639510063203 12501338346261959265094805)
      ·
        refine ⟨586000234981029340551319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12501338346261959265094805 586000234981029340551319)
        ·
          refine ⟨879000352471544010826979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586000234981029340551319 879000352471544010826979)
          ·
            refine ⟨1318500528707316016240469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879000352471544010826979 1318500528707316016240469)
            ·
              refine ⟨7725589035394429782659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1318500528707316016240469 7725589035394429782659)
              ·
                rfl

theorem cell21_304672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 9].length) (baseStart_304672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304672 prefixEnd_304672 := by exact prefixLift 304672
  have htrace : WordTrace (prefixWord ++ tailWord_304672) baseStart_304672 baseEnd_304672 := by
    simpa [prefixWord, tailWord_304672, baseEnd_304672] using wordTrace_append hprefix tailTrace_304672
  have hstable : (prefixWord ++ tailWord_304672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304672).length < 2 ^ (prefixWord ++ tailWord_304672).sum := by decide
  have hdescent : baseEnd_304672 < baseStart_304672 := by decide
  rcases family_descends (prefixWord ++ tailWord_304672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304765 : List Nat := [1, 4, 1, 1, 4, 2, 3, 5]
def baseStart_304765 : Nat := 118140960795 + 304765 * 2 ^ 59
def prefixEnd_304765 : Nat := 4983230072969 + 3 ^ 40 * 304765 * 2
def baseEnd_304765 : Nat := 23183841728534124331247

theorem tailTrace_304765 : CollatzResearch.WordTrace tailWord_304765 prefixEnd_304765 23183841728534124331247 := by
  unfold tailWord_304765
  simp only [CollatzResearch.WordTrace]
  refine ⟨11115692740895929563219749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7410461827263953042146499 11115692740895929563219749)
  ·
    refine ⟨2084192388917986793103703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11115692740895929563219749 2084192388917986793103703)
    ·
      refine ⟨3126288583376980189655555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2084192388917986793103703 3126288583376980189655555)
      ·
        refine ⟨4689432875065470284483333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3126288583376980189655555 4689432875065470284483333)
        ·
          refine ⟨879268664074775678340625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4689432875065470284483333 879268664074775678340625)
          ·
            refine ⟨659451498056081758755469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879268664074775678340625 659451498056081758755469)
            ·
              refine ⟨247294311771030659533301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 659451498056081758755469 247294311771030659533301)
              ·
                refine ⟨23183841728534124331247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247294311771030659533301 23183841728534124331247)
                ·
                  rfl

theorem cell21_304765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 5].length) (baseStart_304765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304765 prefixEnd_304765 := by exact prefixLift 304765
  have htrace : WordTrace (prefixWord ++ tailWord_304765) baseStart_304765 baseEnd_304765 := by
    simpa [prefixWord, tailWord_304765, baseEnd_304765] using wordTrace_append hprefix tailTrace_304765
  have hstable : (prefixWord ++ tailWord_304765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304765).length < 2 ^ (prefixWord ++ tailWord_304765).sum := by decide
  have hdescent : baseEnd_304765 < baseStart_304765 := by decide
  rcases family_descends (prefixWord ++ tailWord_304765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304793 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 4]
def baseStart_304793 : Nat := 118140960795 + 304793 * 2 ^ 59
def prefixEnd_304793 : Nat := 4983230072969 + 3 ^ 40 * 304793 * 2
def baseEnd_304793 : Nat := 69557915167080546527017

theorem tailTrace_304793 : CollatzResearch.WordTrace tailWord_304793 prefixEnd_304793 69557915167080546527017 := by
  unfold tailWord_304793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11116713984794490345239033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7411142656529660230159355 11116713984794490345239033)
  ·
    refine ⟨8337535488595867758929275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11116713984794490345239033 8337535488595867758929275)
    ·
      refine ⟨12506303232893801638393913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8337535488595867758929275 12506303232893801638393913)
      ·
        refine ⟨9379727424670351228795435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12506303232893801638393913 9379727424670351228795435)
        ·
          refine ⟨14069591137005526843193153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9379727424670351228795435 14069591137005526843193153)
          ·
            refine ⟨10552193352754145132394865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14069591137005526843193153 10552193352754145132394865)
            ·
              refine ⟨7914145014565608849296149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10552193352754145132394865 7914145014565608849296149)
              ·
                refine ⟨370975547557762914810757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7914145014565608849296149 370975547557762914810757)
                ·
                  refine ⟨69557915167080546527017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 370975547557762914810757 69557915167080546527017)
                  ·
                    rfl

theorem cell21_304793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_304793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304793 prefixEnd_304793 := by exact prefixLift 304793
  have htrace : WordTrace (prefixWord ++ tailWord_304793) baseStart_304793 baseEnd_304793 := by
    simpa [prefixWord, tailWord_304793, baseEnd_304793] using wordTrace_append hprefix tailTrace_304793
  have hstable : (prefixWord ++ tailWord_304793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304793).length < 2 ^ (prefixWord ++ tailWord_304793).sum := by decide
  have hdescent : baseEnd_304793 < baseStart_304793 := by decide
  rcases family_descends (prefixWord ++ tailWord_304793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304796 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_304796 : Nat := 118140960795 + 304796 * 2 ^ 59
def prefixEnd_304796 : Nat := 4983230072969 + 3 ^ 40 * 304796 * 2
def baseEnd_304796 : Nat := 69558599807953207977011

theorem tailTrace_304796 : CollatzResearch.WordTrace tailWord_304796 prefixEnd_304796 69558599807953207977011 := by
  unfold tailWord_304796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5558411701891810928799121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7411215602522414571732161 5558411701891810928799121)
  ·
    refine ⟨4168808776418858196599341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5558411701891810928799121 4168808776418858196599341)
    ·
      refine ⟨1563303291157071823724753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4168808776418858196599341 1563303291157071823724753)
      ·
        refine ⟨1172477468367803867793565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1563303291157071823724753 1172477468367803867793565)
        ·
          refine ⟨439679050637926450422587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1172477468367803867793565 439679050637926450422587)
          ·
            refine ⟨659518575956889675633881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439679050637926450422587 659518575956889675633881)
            ·
              refine ⟨494638931967667256725411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659518575956889675633881 494638931967667256725411)
              ·
                refine ⟨741958397951500885088117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494638931967667256725411 741958397951500885088117)
                ·
                  refine ⟨69558599807953207977011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741958397951500885088117 69558599807953207977011)
                  ·
                    rfl

theorem cell21_304796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_304796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304796 prefixEnd_304796 := by exact prefixLift 304796
  have htrace : WordTrace (prefixWord ++ tailWord_304796) baseStart_304796 baseEnd_304796 := by
    simpa [prefixWord, tailWord_304796, baseEnd_304796] using wordTrace_append hprefix tailTrace_304796
  have hstable : (prefixWord ++ tailWord_304796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304796).length < 2 ^ (prefixWord ++ tailWord_304796).sum := by decide
  have hdescent : baseEnd_304796 < baseStart_304796 := by decide
  rcases family_descends (prefixWord ++ tailWord_304796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304861 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 4]
def baseStart_304861 : Nat := 118140960795 + 304861 * 2 ^ 59
def prefixEnd_304861 : Nat := 4983230072969 + 3 ^ 40 * 304861 * 2
def baseEnd_304861 : Nat := 69573433693527539393545

theorem tailTrace_304861 : CollatzResearch.WordTrace tailWord_304861 prefixEnd_304861 69573433693527539393545 := by
  unfold tailWord_304861
  simp only [CollatzResearch.WordTrace]
  refine ⟨11119194148548137958714437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7412796099032091972476291 11119194148548137958714437)
  ·
    refine ⟨2084848902852775867258957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11119194148548137958714437 2084848902852775867258957)
    ·
      refine ⟨781818338569790950222109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2084848902852775867258957 781818338569790950222109)
      ·
        refine ⟨293181876963671606333291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 781818338569790950222109 293181876963671606333291)
        ·
          refine ⟨439772815445507409499937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293181876963671606333291 439772815445507409499937)
          ·
            refine ⟨329829611584130557124953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439772815445507409499937 329829611584130557124953)
            ·
              refine ⟨247372208688097917843715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329829611584130557124953 247372208688097917843715)
              ·
                refine ⟨371058313032146876765573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247372208688097917843715 371058313032146876765573)
                ·
                  refine ⟨69573433693527539393545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371058313032146876765573 69573433693527539393545)
                  ·
                    rfl

theorem cell21_304861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_304861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304861 prefixEnd_304861 := by exact prefixLift 304861
  have htrace : WordTrace (prefixWord ++ tailWord_304861) baseStart_304861 baseEnd_304861 := by
    simpa [prefixWord, tailWord_304861, baseEnd_304861] using wordTrace_append hprefix tailTrace_304861
  have hstable : (prefixWord ++ tailWord_304861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304861).length < 2 ^ (prefixWord ++ tailWord_304861).sum := by decide
  have hdescent : baseEnd_304861 < baseStart_304861 := by decide
  rcases family_descends (prefixWord ++ tailWord_304861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304883 : List Nat := [1, 1, 1, 2, 2, 3, 4, 7]
def baseStart_304883 : Nat := 118140960795 + 304883 * 2 ^ 59
def prefixEnd_304883 : Nat := 4983230072969 + 3 ^ 40 * 304883 * 2
def baseEnd_304883 : Nat := 23192818131086796675611

theorem tailTrace_304883 : CollatzResearch.WordTrace tailWord_304883 prefixEnd_304883 23192818131086796675611 := by
  unfold tailWord_304883
  simp only [CollatzResearch.WordTrace]
  refine ⟨11119996554468435716015303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7413331036312290477343535 11119996554468435716015303)
  ·
    refine ⟨16679994831702653574022955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11119996554468435716015303 16679994831702653574022955)
    ·
      refine ⟨25019992247553980361034433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16679994831702653574022955 25019992247553980361034433)
      ·
        refine ⟨18764994185665485270775825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25019992247553980361034433 18764994185665485270775825)
        ·
          refine ⟨14073745639249113953081869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18764994185665485270775825 14073745639249113953081869)
          ·
            refine ⟨5277654614718417732405701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14073745639249113953081869 5277654614718417732405701)
            ·
              refine ⟨989560240259703324826069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5277654614718417732405701 989560240259703324826069)
              ·
                refine ⟨23192818131086796675611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 989560240259703324826069 23192818131086796675611)
                ·
                  rfl

theorem cell21_304883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 7].length) (baseStart_304883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304883 prefixEnd_304883 := by exact prefixLift 304883
  have htrace : WordTrace (prefixWord ++ tailWord_304883) baseStart_304883 baseEnd_304883 := by
    simpa [prefixWord, tailWord_304883, baseEnd_304883] using wordTrace_append hprefix tailTrace_304883
  have hstable : (prefixWord ++ tailWord_304883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304883).length < 2 ^ (prefixWord ++ tailWord_304883).sum := by decide
  have hdescent : baseEnd_304883 < baseStart_304883 := by decide
  rcases family_descends (prefixWord ++ tailWord_304883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304903 : List Nat := [1, 1, 4, 4, 2, 1, 2, 2, 4]
def baseStart_304903 : Nat := 118140960795 + 304903 * 2 ^ 59
def prefixEnd_304903 : Nat := 4983230072969 + 3 ^ 40 * 304903 * 2
def baseEnd_304903 : Nat := 69583018665744799693459

theorem tailTrace_304903 : CollatzResearch.WordTrace tailWord_304903 prefixEnd_304903 69583018665744799693459 := by
  unfold tailWord_304903
  simp only [CollatzResearch.WordTrace]
  refine ⟨11120726014395979131743363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7413817342930652754495575 11120726014395979131743363)
  ·
    refine ⟨16681089021593968697615045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11120726014395979131743363 16681089021593968697615045)
    ·
      refine ⟨3127704191548869130802821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16681089021593968697615045 3127704191548869130802821)
      ·
        refine ⟨586444535915412962025529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3127704191548869130802821 586444535915412962025529)
        ·
          refine ⟨439833401936559721519147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586444535915412962025529 439833401936559721519147)
          ·
            refine ⟨659750102904839582278721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439833401936559721519147 659750102904839582278721)
            ·
              refine ⟨494812577178629686709041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659750102904839582278721 494812577178629686709041)
              ·
                refine ⟨371109432883972265031781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494812577178629686709041 371109432883972265031781)
                ·
                  refine ⟨69583018665744799693459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371109432883972265031781 69583018665744799693459)
                  ·
                    rfl

theorem cell21_304903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 4].length) (baseStart_304903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304903 prefixEnd_304903 := by exact prefixLift 304903
  have htrace : WordTrace (prefixWord ++ tailWord_304903) baseStart_304903 baseEnd_304903 := by
    simpa [prefixWord, tailWord_304903, baseEnd_304903] using wordTrace_append hprefix tailTrace_304903
  have hstable : (prefixWord ++ tailWord_304903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304903).length < 2 ^ (prefixWord ++ tailWord_304903).sum := by decide
  have hdescent : baseEnd_304903 < baseStart_304903 := by decide
  rcases family_descends (prefixWord ++ tailWord_304903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304909 : List Nat := [1, 7, 2, 1, 2, 1, 1, 6]
def baseStart_304909 : Nat := 118140960795 + 304909 * 2 ^ 59
def prefixEnd_304909 : Nat := 4983230072969 + 3 ^ 40 * 304909 * 2
def baseEnd_304909 : Nat := 23194795982496707531149

theorem tailTrace_304909 : CollatzResearch.WordTrace tailWord_304909 prefixEnd_304909 23194795982496707531149 := by
  unfold tailWord_304909
  simp only [CollatzResearch.WordTrace]
  refine ⟨11120944852374242156461781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7413963234916161437641187 11120944852374242156461781)
  ·
    refine ⟨260647144977521300542073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11120944852374242156461781 260647144977521300542073)
    ·
      refine ⟨195485358733140975406555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260647144977521300542073 195485358733140975406555)
      ·
        refine ⟨293228038099711463109833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195485358733140975406555 293228038099711463109833)
        ·
          refine ⟨219921028574783597332375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293228038099711463109833 219921028574783597332375)
          ·
            refine ⟨329881542862175395998563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219921028574783597332375 329881542862175395998563)
            ·
              refine ⟨494822314293263093997845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329881542862175395998563 494822314293263093997845)
              ·
                refine ⟨23194795982496707531149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 494822314293263093997845 23194795982496707531149)
                ·
                  rfl

theorem cell21_304909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 6].length) (baseStart_304909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_304909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_304909 prefixEnd_304909 := by exact prefixLift 304909
  have htrace : WordTrace (prefixWord ++ tailWord_304909) baseStart_304909 baseEnd_304909 := by
    simpa [prefixWord, tailWord_304909, baseEnd_304909] using wordTrace_append hprefix tailTrace_304909
  have hstable : (prefixWord ++ tailWord_304909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304909).length < 2 ^ (prefixWord ++ tailWord_304909).sum := by decide
  have hdescent : baseEnd_304909 < baseStart_304909 := by decide
  rcases family_descends (prefixWord ++ tailWord_304909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305021 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 4]
def baseStart_305021 : Nat := 118140960795 + 305021 * 2 ^ 59
def prefixEnd_305021 : Nat := 4983230072969 + 3 ^ 40 * 305021 * 2
def baseEnd_305021 : Nat := 69609947873402816726551

theorem tailTrace_305021 : CollatzResearch.WordTrace tailWord_305021 prefixEnd_305021 69609947873402816726551 := by
  unfold tailWord_305021
  simp only [CollatzResearch.WordTrace]
  refine ⟨11125029827968485284538917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7416686551978990189692611 11125029827968485284538917)
  ·
    refine ⟨2085943092744090990851047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11125029827968485284538917 2085943092744090990851047)
    ·
      refine ⟨3128914639116136486276571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2085943092744090990851047 3128914639116136486276571)
      ·
        refine ⟨4693371958674204729414857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3128914639116136486276571 4693371958674204729414857)
        ·
          refine ⟨3520028969005653547061143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4693371958674204729414857 3520028969005653547061143)
          ·
            refine ⟨5280043453508480320591715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520028969005653547061143 5280043453508480320591715)
            ·
              refine ⟨7920065180262720480887573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5280043453508480320591715 7920065180262720480887573)
              ·
                refine ⟨371253055324815022541605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7920065180262720480887573 371253055324815022541605)
                ·
                  refine ⟨69609947873402816726551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371253055324815022541605 69609947873402816726551)
                  ·
                    rfl

theorem cell21_305021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_305021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305021 prefixEnd_305021 := by exact prefixLift 305021
  have htrace : WordTrace (prefixWord ++ tailWord_305021) baseStart_305021 baseEnd_305021 := by
    simpa [prefixWord, tailWord_305021, baseEnd_305021] using wordTrace_append hprefix tailTrace_305021
  have hstable : (prefixWord ++ tailWord_305021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305021).length < 2 ^ (prefixWord ++ tailWord_305021).sum := by decide
  have hdescent : baseEnd_305021 < baseStart_305021 := by decide
  rcases family_descends (prefixWord ++ tailWord_305021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305024 : List Nat := [2, 1, 1, 2, 1, 2, 7, 2, 3]
def baseStart_305024 : Nat := 118140960795 + 305024 * 2 ^ 59
def prefixEnd_305024 : Nat := 4983230072969 + 3 ^ 40 * 305024 * 2
def baseEnd_305024 : Nat := 69610632514275478176545

theorem tailTrace_305024 : CollatzResearch.WordTrace tailWord_305024 prefixEnd_305024 69610632514275478176545 := by
  unfold tailWord_305024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5562569623478808398449063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7416759497971744531265417 5562569623478808398449063)
  ·
    refine ⟨8343854435218212597673595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5562569623478808398449063 8343854435218212597673595)
    ·
      refine ⟨12515781652827318896510393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8343854435218212597673595 12515781652827318896510393)
      ·
        refine ⟨9386836239620489172382795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12515781652827318896510393 9386836239620489172382795)
        ·
          refine ⟨14080254359430733758574193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9386836239620489172382795 14080254359430733758574193)
          ·
            refine ⟨10560190769573050318930645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14080254359430733758574193 10560190769573050318930645)
            ·
              refine ⟨247504471161868366849937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10560190769573050318930645 247504471161868366849937)
              ·
                refine ⟨185628353371401275137453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247504471161868366849937 185628353371401275137453)
                ·
                  refine ⟨69610632514275478176545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185628353371401275137453 69610632514275478176545)
                  ·
                    rfl

theorem cell21_305024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_305024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305024 prefixEnd_305024 := by exact prefixLift 305024
  have htrace : WordTrace (prefixWord ++ tailWord_305024) baseStart_305024 baseEnd_305024 := by
    simpa [prefixWord, tailWord_305024, baseEnd_305024] using wordTrace_append hprefix tailTrace_305024
  have hstable : (prefixWord ++ tailWord_305024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305024).length < 2 ^ (prefixWord ++ tailWord_305024).sum := by decide
  have hdescent : baseEnd_305024 < baseStart_305024 := by decide
  rcases family_descends (prefixWord ++ tailWord_305024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305052 : List Nat := [2, 2, 3, 3, 1, 1, 2, 7]
def baseStart_305052 : Nat := 118140960795 + 305052 * 2 ^ 59
def prefixEnd_305052 : Nat := 4983230072969 + 3 ^ 40 * 305052 * 2
def baseEnd_305052 : Nat := 23205674165251217236607

theorem tailTrace_305052 : CollatzResearch.WordTrace tailWord_305052 prefixEnd_305052 23205674165251217236607 := by
  unfold tailWord_305052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563080245428088789458705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7417440327237451719278273 5563080245428088789458705)
  ·
    refine ⟨4172310184071066592094029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5563080245428088789458705 4172310184071066592094029)
    ·
      refine ⟨1564616319026649972035261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4172310184071066592094029 1564616319026649972035261)
      ·
        refine ⟨586731119634993739513223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1564616319026649972035261 586731119634993739513223)
        ·
          refine ⟨880096679452490609269835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586731119634993739513223 880096679452490609269835)
          ·
            refine ⟨1320145019178735913904753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880096679452490609269835 1320145019178735913904753)
            ·
              refine ⟨990108764384051935428565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1320145019178735913904753 990108764384051935428565)
              ·
                refine ⟨23205674165251217236607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 990108764384051935428565 23205674165251217236607)
                ·
                  rfl

theorem cell21_305052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_305052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305052 prefixEnd_305052 := by exact prefixLift 305052
  have htrace : WordTrace (prefixWord ++ tailWord_305052) baseStart_305052 baseEnd_305052 := by
    simpa [prefixWord, tailWord_305052, baseEnd_305052] using wordTrace_append hprefix tailTrace_305052
  have hstable : (prefixWord ++ tailWord_305052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305052).length < 2 ^ (prefixWord ++ tailWord_305052).sum := by decide
  have hdescent : baseEnd_305052 < baseStart_305052 := by decide
  rcases family_descends (prefixWord ++ tailWord_305052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305117 : List Nat := [1, 4, 3, 1, 3, 1, 2, 3, 3]
def baseStart_305117 : Nat := 118140960795 + 305117 * 2 ^ 59
def prefixEnd_305117 : Nat := 4983230072969 + 3 ^ 40 * 305117 * 2
def baseEnd_305117 : Nat := 69631856381327983126355

theorem tailTrace_305117 : CollatzResearch.WordTrace tailWord_305117 prefixEnd_305117 69631856381327983126355 := by
  unfold tailWord_305117
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128531235620693680033605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7419020823747129120022403 11128531235620693680033605)
  ·
    refine ⟨2086599606678880065006301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11128531235620693680033605 2086599606678880065006301)
    ·
      refine ⟨782474852504580024377363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2086599606678880065006301 782474852504580024377363)
      ·
        refine ⟨1173712278756870036566045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782474852504580024377363 1173712278756870036566045)
        ·
          refine ⟨440142104533826263712267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1173712278756870036566045 440142104533826263712267)
          ·
            refine ⟨660213156800739395568401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440142104533826263712267 660213156800739395568401)
            ·
              refine ⟨495159867600554546676301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660213156800739395568401 495159867600554546676301)
              ·
                refine ⟨185684950350207955003613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 495159867600554546676301 185684950350207955003613)
                ·
                  refine ⟨69631856381327983126355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185684950350207955003613 69631856381327983126355)
                  ·
                    rfl

theorem cell21_305117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_305117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305117 prefixEnd_305117 := by exact prefixLift 305117
  have htrace : WordTrace (prefixWord ++ tailWord_305117) baseStart_305117 baseEnd_305117 := by
    simpa [prefixWord, tailWord_305117, baseEnd_305117] using wordTrace_append hprefix tailTrace_305117
  have hstable : (prefixWord ++ tailWord_305117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305117).length < 2 ^ (prefixWord ++ tailWord_305117).sum := by decide
  have hdescent : baseEnd_305117 < baseStart_305117 := by decide
  rcases family_descends (prefixWord ++ tailWord_305117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305162 : List Nat := [3, 1, 2, 2, 5, 1, 2, 5]
def baseStart_305162 : Nat := 118140960795 + 305162 * 2 ^ 59
def prefixEnd_305162 : Nat := 4983230072969 + 3 ^ 40 * 305162 * 2
def baseEnd_305162 : Nat := 23214041998139301625421

theorem tailTrace_305162 : CollatzResearch.WordTrace tailWord_305162 prefixEnd_305162 23214041998139301625421 := by
  unfold tailWord_305162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782543130114416591355435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7420115013638444243614493 2782543130114416591355435)
  ·
    refine ⟨4173814695171624887033153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2782543130114416591355435 4173814695171624887033153)
    ·
      refine ⟨3130361021378718665274865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4173814695171624887033153 3130361021378718665274865)
      ·
        refine ⟨2347770766034038998956149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3130361021378718665274865 2347770766034038998956149)
        ·
          refine ⟨220103509315691156152139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2347770766034038998956149 220103509315691156152139)
          ·
            refine ⟨330155263973536734228209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220103509315691156152139 330155263973536734228209)
            ·
              refine ⟨247616447980152550671157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330155263973536734228209 247616447980152550671157)
              ·
                refine ⟨23214041998139301625421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247616447980152550671157 23214041998139301625421)
                ·
                  rfl

theorem cell21_305162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_305162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305162 prefixEnd_305162 := by exact prefixLift 305162
  have htrace : WordTrace (prefixWord ++ tailWord_305162) baseStart_305162 baseEnd_305162 := by
    simpa [prefixWord, tailWord_305162, baseEnd_305162] using wordTrace_append hprefix tailTrace_305162
  have hstable : (prefixWord ++ tailWord_305162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305162).length < 2 ^ (prefixWord ++ tailWord_305162).sum := by decide
  have hdescent : baseEnd_305162 < baseStart_305162 := by decide
  rcases family_descends (prefixWord ++ tailWord_305162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305252 : List Nat := [2, 3, 1, 1, 2, 1, 6, 2, 3]
def baseStart_305252 : Nat := 118140960795 + 305252 * 2 ^ 59
def prefixEnd_305252 : Nat := 4983230072969 + 3 ^ 40 * 305252 * 2
def baseEnd_305252 : Nat := 69662665220597748376079

theorem tailTrace_305252 : CollatzResearch.WordTrace tailWord_305252 prefixEnd_305252 69662665220597748376079 := by
  unfold tailWord_305252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5566727545065805868099005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7422303393421074490798673 5566727545065805868099005)
  ·
    refine ⟨2087522829399677200537127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5566727545065805868099005 2087522829399677200537127)
    ·
      refine ⟨3131284244099515800805691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2087522829399677200537127 3131284244099515800805691)
      ·
        refine ⟨4696926366149273701208537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131284244099515800805691 4696926366149273701208537)
        ·
          refine ⟨3522694774611955275906403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4696926366149273701208537 3522694774611955275906403)
          ·
            refine ⟨5284042161917932913859605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3522694774611955275906403 5284042161917932913859605)
            ·
              refine ⟨247689476339903105337169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5284042161917932913859605 247689476339903105337169)
              ·
                refine ⟨185767107254927329002877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247689476339903105337169 185767107254927329002877)
                ·
                  refine ⟨69662665220597748376079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185767107254927329002877 69662665220597748376079)
                  ·
                    rfl

theorem cell21_305252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_305252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305252 prefixEnd_305252 := by exact prefixLift 305252
  have htrace : WordTrace (prefixWord ++ tailWord_305252) baseStart_305252 baseEnd_305252 := by
    simpa [prefixWord, tailWord_305252, baseEnd_305252] using wordTrace_append hprefix tailTrace_305252
  have hstable : (prefixWord ++ tailWord_305252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305252).length < 2 ^ (prefixWord ++ tailWord_305252).sum := by decide
  have hdescent : baseEnd_305252 < baseStart_305252 := by decide
  rcases family_descends (prefixWord ++ tailWord_305252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305263 : List Nat := [1, 1, 2, 1, 3, 4, 3, 6]
def baseStart_305263 : Nat := 118140960795 + 305263 * 2 ^ 59
def prefixEnd_305263 : Nat := 4983230072969 + 3 ^ 40 * 305263 * 2
def baseEnd_305263 : Nat := 23221725190154724564241

theorem tailTrace_305263 : CollatzResearch.WordTrace tailWord_305263 prefixEnd_305263 23221725190154724564241 := by
  unfold tailWord_305263
  simp only [CollatzResearch.WordTrace]
  refine ⟨11133856293091760614848443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7422570862061173743232295 11133856293091760614848443)
  ·
    refine ⟨16700784439637640922272665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11133856293091760614848443 16700784439637640922272665)
    ·
      refine ⟨12525588329728230691704499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16700784439637640922272665 12525588329728230691704499)
      ·
        refine ⟨18788382494592346037556749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12525588329728230691704499 18788382494592346037556749)
        ·
          refine ⟨7045643435472129764083781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18788382494592346037556749 7045643435472129764083781)
          ·
            refine ⟨1321058144151024330765709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7045643435472129764083781 1321058144151024330765709)
            ·
              refine ⟨495396804056634124037141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1321058144151024330765709 495396804056634124037141)
              ·
                refine ⟨23221725190154724564241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 495396804056634124037141 23221725190154724564241)
                ·
                  rfl

theorem cell21_305263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 6].length) (baseStart_305263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305263 prefixEnd_305263 := by exact prefixLift 305263
  have htrace : WordTrace (prefixWord ++ tailWord_305263) baseStart_305263 baseEnd_305263 := by
    simpa [prefixWord, tailWord_305263, baseEnd_305263] using wordTrace_append hprefix tailTrace_305263
  have hstable : (prefixWord ++ tailWord_305263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305263).length < 2 ^ (prefixWord ++ tailWord_305263).sum := by decide
  have hdescent : baseEnd_305263 < baseStart_305263 := by decide
  rcases family_descends (prefixWord ++ tailWord_305263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305300 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_305300 : Nat := 118140960795 + 305300 * 2 ^ 59
def prefixEnd_305300 : Nat := 4983230072969 + 3 ^ 40 * 305300 * 2
def baseEnd_305300 : Nat := 69673619474560331575981

theorem tailTrace_305300 : CollatzResearch.WordTrace tailWord_305300 prefixEnd_305300 69673619474560331575981 := by
  unfold tailWord_305300
  simp only [CollatzResearch.WordTrace]
  refine ⟨5567602896978857966972677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7423470529305143955963569 5567602896978857966972677)
  ·
    refine ⟨1043925543183535868807377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5567602896978857966972677 1043925543183535868807377)
    ·
      refine ⟨782944157387651901605533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1043925543183535868807377 782944157387651901605533)
      ·
        refine ⟨293604059020369463102075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 782944157387651901605533 293604059020369463102075)
        ·
          refine ⟨440406088530554194653113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293604059020369463102075 440406088530554194653113)
          ·
            refine ⟨330304566397915645989835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440406088530554194653113 330304566397915645989835)
            ·
              refine ⟨495456849596873468984753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330304566397915645989835 495456849596873468984753)
              ·
                refine ⟨371592637197655101738565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495456849596873468984753 371592637197655101738565)
                ·
                  refine ⟨69673619474560331575981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 371592637197655101738565 69673619474560331575981)
                  ·
                    rfl

theorem cell21_305300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_305300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305300 prefixEnd_305300 := by exact prefixLift 305300
  have htrace : WordTrace (prefixWord ++ tailWord_305300) baseStart_305300 baseEnd_305300 := by
    simpa [prefixWord, tailWord_305300, baseEnd_305300] using wordTrace_append hprefix tailTrace_305300
  have hstable : (prefixWord ++ tailWord_305300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305300).length < 2 ^ (prefixWord ++ tailWord_305300).sum := by decide
  have hdescent : baseEnd_305300 < baseStart_305300 := by decide
  rcases family_descends (prefixWord ++ tailWord_305300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305311 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 5]
def baseStart_305311 : Nat := 118140960795 + 305311 * 2 ^ 59
def prefixEnd_305311 : Nat := 4983230072969 + 3 ^ 40 * 305311 * 2
def baseEnd_305311 : Nat := 69676129824426756892625

theorem tailTrace_305311 : CollatzResearch.WordTrace tailWord_305311 prefixEnd_305311 69676129824426756892625 := by
  unfold tailWord_305311
  simp only [CollatzResearch.WordTrace]
  refine ⟨11135606996917864812595787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7423737997945243208397191 11135606996917864812595787)
  ·
    refine ⟨16703410495376797218893681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11135606996917864812595787 16703410495376797218893681)
    ·
      refine ⟨12527557871532597914170261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16703410495376797218893681 12527557871532597914170261)
      ·
        refine ⟨587229275228090527226731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12527557871532597914170261 587229275228090527226731)
        ·
          refine ⟨880843912842135790840097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587229275228090527226731 880843912842135790840097)
          ·
            refine ⟨660632934631601843130073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880843912842135790840097 660632934631601843130073)
            ·
              refine ⟨495474700973701382347555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660632934631601843130073 495474700973701382347555)
              ·
                refine ⟨743212051460552073521333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495474700973701382347555 743212051460552073521333)
                ·
                  refine ⟨69676129824426756892625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 743212051460552073521333 69676129824426756892625)
                  ·
                    rfl

theorem cell21_305311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 5].length) (baseStart_305311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305311 prefixEnd_305311 := by exact prefixLift 305311
  have htrace : WordTrace (prefixWord ++ tailWord_305311) baseStart_305311 baseEnd_305311 := by
    simpa [prefixWord, tailWord_305311, baseEnd_305311] using wordTrace_append hprefix tailTrace_305311
  have hstable : (prefixWord ++ tailWord_305311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305311).length < 2 ^ (prefixWord ++ tailWord_305311).sum := by decide
  have hdescent : baseEnd_305311 < baseStart_305311 := by decide
  rcases family_descends (prefixWord ++ tailWord_305311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305370 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_305370 : Nat := 118140960795 + 305370 * 2 ^ 59
def prefixEnd_305370 : Nat := 4983230072969 + 3 ^ 40 * 305370 * 2
def baseEnd_305370 : Nat := 69689594428255765409171

theorem tailTrace_305370 : CollatzResearch.WordTrace tailWord_305370 prefixEnd_305370 69689594428255765409171 := by
  unfold tailWord_305370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2784439725926029472248391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7425172602469411925995709 2784439725926029472248391)
  ·
    refine ⟨4176659588889044208372587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2784439725926029472248391 4176659588889044208372587)
    ·
      refine ⟨6264989383333566312558881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4176659588889044208372587 6264989383333566312558881)
      ·
        refine ⟨4698742037500174734419161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6264989383333566312558881 4698742037500174734419161)
        ·
          refine ⟨3524056528125131050814371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4698742037500174734419161 3524056528125131050814371)
          ·
            refine ⟨5286084792187696576221557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524056528125131050814371 5286084792187696576221557)
            ·
              refine ⟨495570449267596554020771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5286084792187696576221557 495570449267596554020771)
              ·
                refine ⟨743355673901394831031157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495570449267596554020771 743355673901394831031157)
                ·
                  refine ⟨69689594428255765409171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 743355673901394831031157 69689594428255765409171)
                  ·
                    rfl

theorem cell21_305370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_305370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305370 prefixEnd_305370 := by exact prefixLift 305370
  have htrace : WordTrace (prefixWord ++ tailWord_305370) baseStart_305370 baseEnd_305370 := by
    simpa [prefixWord, tailWord_305370, baseEnd_305370] using wordTrace_append hprefix tailTrace_305370
  have hstable : (prefixWord ++ tailWord_305370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305370).length < 2 ^ (prefixWord ++ tailWord_305370).sum := by decide
  have hdescent : baseEnd_305370 < baseStart_305370 := by decide
  rcases family_descends (prefixWord ++ tailWord_305370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305415 : List Nat := [1, 1, 4, 5, 10]
def baseStart_305415 : Nat := 118140960795 + 305415 * 2 ^ 59
def prefixEnd_305415 : Nat := 4983230072969 + 3 ^ 40 * 305415 * 2
def baseEnd_305415 : Nat := 860492148658588730359

theorem tailTrace_305415 : CollatzResearch.WordTrace tailWord_305415 prefixEnd_305415 860492148658588730359 := by
  unfold tailWord_305415
  simp only [CollatzResearch.WordTrace]
  refine ⟨11139400188541090574381699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7426266792360727049587799 11139400188541090574381699)
  ·
    refine ⟨16709100282811635861572549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11139400188541090574381699 16709100282811635861572549)
    ·
      refine ⟨3132956303027181724044853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16709100282811635861572549 3132956303027181724044853)
      ·
        refine ⟨293714653408798286629205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3132956303027181724044853 293714653408798286629205)
        ·
          refine ⟨860492148658588730359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 293714653408798286629205 860492148658588730359)
          ·
            rfl

theorem cell21_305415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 10].length) (baseStart_305415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305415 prefixEnd_305415 := by exact prefixLift 305415
  have htrace : WordTrace (prefixWord ++ tailWord_305415) baseStart_305415 baseEnd_305415 := by
    simpa [prefixWord, tailWord_305415, baseEnd_305415] using wordTrace_append hprefix tailTrace_305415
  have hstable : (prefixWord ++ tailWord_305415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305415).length < 2 ^ (prefixWord ++ tailWord_305415).sum := by decide
  have hdescent : baseEnd_305415 < baseStart_305415 := by decide
  rcases family_descends (prefixWord ++ tailWord_305415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305539 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 5]
def baseStart_305539 : Nat := 118140960795 + 305539 * 2 ^ 59
def prefixEnd_305539 : Nat := 4983230072969 + 3 ^ 40 * 305539 * 2
def baseEnd_305539 : Nat := 69728162530749027092159

theorem tailTrace_305539 : CollatzResearch.WordTrace tailWord_305539 prefixEnd_305539 69728162530749027092159 := by
  unfold tailWord_305539
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143922840091859751895671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7429281893394573167930447 11143922840091859751895671)
  ·
    refine ⟨16715884260137789627843507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11143922840091859751895671 16715884260137789627843507)
    ·
      refine ⟨25073826390206684441765261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16715884260137789627843507 25073826390206684441765261)
      ·
        refine ⟨9402684896327506665661973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25073826390206684441765261 9402684896327506665661973)
        ·
          refine ⟨440750854515351874952905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9402684896327506665661973 440750854515351874952905)
          ·
            refine ⟨330563140886513906214679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440750854515351874952905 330563140886513906214679)
            ·
              refine ⟨495844711329770859322019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330563140886513906214679 495844711329770859322019)
              ·
                refine ⟨743767066994656288983029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495844711329770859322019 743767066994656288983029)
                ·
                  refine ⟨69728162530749027092159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 743767066994656288983029 69728162530749027092159)
                  ·
                    rfl

theorem cell21_305539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 5].length) (baseStart_305539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305539 prefixEnd_305539 := by exact prefixLift 305539
  have htrace : WordTrace (prefixWord ++ tailWord_305539) baseStart_305539 baseEnd_305539 := by
    simpa [prefixWord, tailWord_305539, baseEnd_305539] using wordTrace_append hprefix tailTrace_305539
  have hstable : (prefixWord ++ tailWord_305539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305539).length < 2 ^ (prefixWord ++ tailWord_305539).sum := by decide
  have hdescent : baseEnd_305539 < baseStart_305539 := by decide
  rcases family_descends (prefixWord ++ tailWord_305539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305646 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_305646 : Nat := 118140960795 + 305646 * 2 ^ 59
def prefixEnd_305646 : Nat := 4983230072969 + 3 ^ 40 * 305646 * 2
def baseEnd_305646 : Nat := 69752581388540618808607

theorem tailTrace_305646 : CollatzResearch.WordTrace tailWord_305646 prefixEnd_305646 69752581388540618808607 := by
  unfold tailWord_305646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393478181338027128255099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7431883633802811350693861 1393478181338027128255099)
  ·
    refine ⟨2090217272007040692382649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1393478181338027128255099 2090217272007040692382649)
    ·
      refine ⟨1567662954005280519286987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2090217272007040692382649 1567662954005280519286987)
      ·
        refine ⟨2351494431007920778930481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567662954005280519286987 2351494431007920778930481)
        ·
          refine ⟨1763620823255940584197861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351494431007920778930481 1763620823255940584197861)
          ·
            refine ⟨330678904360488859537099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1763620823255940584197861 330678904360488859537099)
            ·
              refine ⟨496018356540733289305649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330678904360488859537099 496018356540733289305649)
              ·
                refine ⟨372013767405549966979237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496018356540733289305649 372013767405549966979237)
                ·
                  refine ⟨69752581388540618808607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372013767405549966979237 69752581388540618808607)
                  ·
                    rfl

theorem cell21_305646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_305646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305646 prefixEnd_305646 := by exact prefixLift 305646
  have htrace : WordTrace (prefixWord ++ tailWord_305646) baseStart_305646 baseEnd_305646 := by
    simpa [prefixWord, tailWord_305646, baseEnd_305646] using wordTrace_append hprefix tailTrace_305646
  have hstable : (prefixWord ++ tailWord_305646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305646).length < 2 ^ (prefixWord ++ tailWord_305646).sum := by decide
  have hdescent : baseEnd_305646 < baseStart_305646 := by decide
  rcases family_descends (prefixWord ++ tailWord_305646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305657 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 5]
def baseStart_305657 : Nat := 118140960795 + 305657 * 2 ^ 59
def prefixEnd_305657 : Nat := 4983230072969 + 3 ^ 40 * 305657 * 2
def baseEnd_305657 : Nat := 69755091738407044125251

theorem tailTrace_305657 : CollatzResearch.WordTrace tailWord_305657 prefixEnd_305657 69755091738407044125251 := by
  unfold tailWord_305657
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148226653664365904691225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7432151102442910603127483 11148226653664365904691225)
  ·
    refine ⟨8361169990248274428518419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11148226653664365904691225 8361169990248274428518419)
    ·
      refine ⟨12541754985372411642777629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8361169990248274428518419 12541754985372411642777629)
      ·
        refine ⟨4703158119514654366041611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12541754985372411642777629 4703158119514654366041611)
        ·
          refine ⟨7054737179271981549062417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703158119514654366041611 7054737179271981549062417)
          ·
            refine ⟨5291052884453986161796813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7054737179271981549062417 5291052884453986161796813)
            ·
              refine ⟨1984144831670244810673805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5291052884453986161796813 1984144831670244810673805)
              ·
                refine ⟨744054311876341804002677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1984144831670244810673805 744054311876341804002677)
                ·
                  refine ⟨69755091738407044125251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 744054311876341804002677 69755091738407044125251)
                  ·
                    rfl

theorem cell21_305657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_305657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305657 prefixEnd_305657 := by exact prefixLift 305657
  have htrace : WordTrace (prefixWord ++ tailWord_305657) baseStart_305657 baseEnd_305657 := by
    simpa [prefixWord, tailWord_305657, baseEnd_305657] using wordTrace_append hprefix tailTrace_305657
  have hstable : (prefixWord ++ tailWord_305657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305657).length < 2 ^ (prefixWord ++ tailWord_305657).sum := by decide
  have hdescent : baseEnd_305657 < baseStart_305657 := by decide
  rcases family_descends (prefixWord ++ tailWord_305657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305677 : List Nat := [1, 7, 1, 1, 1, 2, 1, 7]
def baseStart_305677 : Nat := 118140960795 + 305677 * 2 ^ 59
def prefixEnd_305677 : Nat := 4983230072969 + 3 ^ 40 * 305677 * 2
def baseEnd_305677 : Nat := 23253218670297151263959

theorem tailTrace_305677 : CollatzResearch.WordTrace tailWord_305677 prefixEnd_305677 23253218670297151263959 := by
  unfold tailWord_305677
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148956113591909320419285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7432637409061272880279523 11148956113591909320419285)
  ·
    refine ⟨261303658912310374697327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11148956113591909320419285 261303658912310374697327)
    ·
      refine ⟨391955488368465562045991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261303658912310374697327 391955488368465562045991)
      ·
        refine ⟨587933232552698343068987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391955488368465562045991 587933232552698343068987)
        ·
          refine ⟨881899848829047514603481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587933232552698343068987 881899848829047514603481)
          ·
            refine ⟨661424886621785635952611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881899848829047514603481 661424886621785635952611)
            ·
              refine ⟨992137329932678453928917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661424886621785635952611 992137329932678453928917)
              ·
                refine ⟨23253218670297151263959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 992137329932678453928917 23253218670297151263959)
                ·
                  rfl

theorem cell21_305677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 7].length) (baseStart_305677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305677 prefixEnd_305677 := by exact prefixLift 305677
  have htrace : WordTrace (prefixWord ++ tailWord_305677) baseStart_305677 baseEnd_305677 := by
    simpa [prefixWord, tailWord_305677, baseEnd_305677] using wordTrace_append hprefix tailTrace_305677
  have hstable : (prefixWord ++ tailWord_305677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305677).length < 2 ^ (prefixWord ++ tailWord_305677).sum := by decide
  have hdescent : baseEnd_305677 < baseStart_305677 := by decide
  rcases family_descends (prefixWord ++ tailWord_305677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305688 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_305688 : Nat := 118140960795 + 305688 * 2 ^ 59
def prefixEnd_305688 : Nat := 4983230072969 + 3 ^ 40 * 305688 * 2
def baseEnd_305688 : Nat := 69762166360757879108521

theorem tailTrace_305688 : CollatzResearch.WordTrace tailWord_305688 prefixEnd_305688 69762166360757879108521 := by
  unfold tailWord_305688
  simp only [CollatzResearch.WordTrace]
  refine ⟨5574678658276029099534859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7432904877701372132713145 5574678658276029099534859)
  ·
    refine ⟨8362017987414043649302289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5574678658276029099534859 8362017987414043649302289)
    ·
      refine ⟨6271513490560532736976717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8362017987414043649302289 6271513490560532736976717)
      ·
        refine ⟨2351817558960199776366269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6271513490560532736976717 2351817558960199776366269)
        ·
          refine ⟨881931584610074916137351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2351817558960199776366269 881931584610074916137351)
          ·
            refine ⟨1322897376915112374206027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881931584610074916137351 1322897376915112374206027)
            ·
              refine ⟨1984346065372668561309041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322897376915112374206027 1984346065372668561309041)
              ·
                refine ⟨1488259549029501420981781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984346065372668561309041 1488259549029501420981781)
                ·
                  refine ⟨69762166360757879108521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1488259549029501420981781 69762166360757879108521)
                  ·
                    rfl

theorem cell21_305688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_305688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305688 prefixEnd_305688 := by exact prefixLift 305688
  have htrace : WordTrace (prefixWord ++ tailWord_305688) baseStart_305688 baseEnd_305688 := by
    simpa [prefixWord, tailWord_305688, baseEnd_305688] using wordTrace_append hprefix tailTrace_305688
  have hstable : (prefixWord ++ tailWord_305688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305688).length < 2 ^ (prefixWord ++ tailWord_305688).sum := by decide
  have hdescent : baseEnd_305688 < baseStart_305688 := by decide
  rcases family_descends (prefixWord ++ tailWord_305688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305722 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_305722 : Nat := 118140960795 + 305722 * 2 ^ 59
def prefixEnd_305722 : Nat := 4983230072969 + 3 ^ 40 * 305722 * 2
def baseEnd_305722 : Nat := 69769925623981375541785

theorem tailTrace_305722 : CollatzResearch.WordTrace tailWord_305722 prefixEnd_305722 69769925623981375541785 := by
  unfold tailWord_305722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2787649349607220501451855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7433731598952588003871613 2787649349607220501451855)
  ·
    refine ⟨4181474024410830752177783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2787649349607220501451855 4181474024410830752177783)
    ·
      refine ⟨6272211036616246128266675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4181474024410830752177783 6272211036616246128266675)
      ·
        refine ⟨9408316554924369192400013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6272211036616246128266675 9408316554924369192400013)
        ·
          refine ⟨3528118708096638447150005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9408316554924369192400013 3528118708096638447150005)
          ·
            refine ⟨330761128884059854420313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3528118708096638447150005 330761128884059854420313)
            ·
              refine ⟨248070846663044890815235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330761128884059854420313 248070846663044890815235)
              ·
                refine ⟨372106269994567336222853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248070846663044890815235 372106269994567336222853)
                ·
                  refine ⟨69769925623981375541785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372106269994567336222853 69769925623981375541785)
                  ·
                    rfl

theorem cell21_305722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_305722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305722 prefixEnd_305722 := by exact prefixLift 305722
  have htrace : WordTrace (prefixWord ++ tailWord_305722) baseStart_305722 baseEnd_305722 := by
    simpa [prefixWord, tailWord_305722, baseEnd_305722] using wordTrace_append hprefix tailTrace_305722
  have hstable : (prefixWord ++ tailWord_305722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305722).length < 2 ^ (prefixWord ++ tailWord_305722).sum := by decide
  have hdescent : baseEnd_305722 < baseStart_305722 := by decide
  rcases family_descends (prefixWord ++ tailWord_305722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305846 : List Nat := [5, 1, 3, 1, 2, 2, 2, 5]
def baseStart_305846 : Nat := 118140960795 + 305846 * 2 ^ 59
def prefixEnd_305846 : Nat := 4983230072969 + 3 ^ 40 * 305846 * 2
def baseEnd_305846 : Nat := 23266074704461571824955

theorem tailTrace_305846 : CollatzResearch.WordTrace tailWord_305846 prefixEnd_305846 23266074704461571824955 := by
  unfold tailWord_305846
  simp only [CollatzResearch.WordTrace]
  refine ⟨697195003123728198957587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7436746699986434122214261 697195003123728198957587)
  ·
    refine ⟨1045792504685592298436381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697195003123728198957587 1045792504685592298436381)
    ·
      refine ⟨392172189257097111913643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1045792504685592298436381 392172189257097111913643)
      ·
        refine ⟨588258283885645667870465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392172189257097111913643 588258283885645667870465)
        ·
          refine ⟨441193712914234250902849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 588258283885645667870465 441193712914234250902849)
          ·
            refine ⟨330895284685675688177137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441193712914234250902849 330895284685675688177137)
            ·
              refine ⟨248171463514256766132853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330895284685675688177137 248171463514256766132853)
              ·
                refine ⟨23266074704461571824955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 248171463514256766132853 23266074704461571824955)
                ·
                  rfl

theorem cell21_305846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_305846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305846 prefixEnd_305846 := by exact prefixLift 305846
  have htrace : WordTrace (prefixWord ++ tailWord_305846) baseStart_305846 baseEnd_305846 := by
    simpa [prefixWord, tailWord_305846, baseEnd_305846] using wordTrace_append hprefix tailTrace_305846
  have hstable : (prefixWord ++ tailWord_305846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305846).length < 2 ^ (prefixWord ++ tailWord_305846).sum := by decide
  have hdescent : baseEnd_305846 < baseStart_305846 := by decide
  rcases family_descends (prefixWord ++ tailWord_305846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305860 : List Nat := [2, 3, 3, 1, 1, 4, 1, 3, 3]
def baseStart_305860 : Nat := 118140960795 + 305860 * 2 ^ 59
def prefixEnd_305860 : Nat := 4983230072969 + 3 ^ 40 * 305860 * 2
def baseEnd_305860 : Nat := 69801419104123802241503

theorem tailTrace_305860 : CollatzResearch.WordTrace tailWord_305860 prefixEnd_305860 69801419104123802241503 := by
  unfold tailWord_305860
  simp only [CollatzResearch.WordTrace]
  refine ⟨5577815335964465787165517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7437087114619287716220689 5577815335964465787165517)
  ·
    refine ⟨2091680750986674670187069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5577815335964465787165517 2091680750986674670187069)
    ·
      refine ⟨784380281620003001320151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2091680750986674670187069 784380281620003001320151)
      ·
        refine ⟨1176570422430004501980227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784380281620003001320151 1176570422430004501980227)
        ·
          refine ⟨1764855633645006752970341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176570422430004501980227 1764855633645006752970341)
          ·
            refine ⟨330910431308438766181939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1764855633645006752970341 330910431308438766181939)
            ·
              refine ⟨496365646962658149272909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330910431308438766181939 496365646962658149272909)
              ·
                refine ⟨186137117610996805977341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 496365646962658149272909 186137117610996805977341)
                ·
                  refine ⟨69801419104123802241503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186137117610996805977341 69801419104123802241503)
                  ·
                    rfl

theorem cell21_305860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_305860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305860 prefixEnd_305860 := by exact prefixLift 305860
  have htrace : WordTrace (prefixWord ++ tailWord_305860) baseStart_305860 baseEnd_305860 := by
    simpa [prefixWord, tailWord_305860, baseEnd_305860] using wordTrace_append hprefix tailTrace_305860
  have hstable : (prefixWord ++ tailWord_305860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305860).length < 2 ^ (prefixWord ++ tailWord_305860).sum := by decide
  have hdescent : baseEnd_305860 < baseStart_305860 := by decide
  rcases family_descends (prefixWord ++ tailWord_305860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305877 : List Nat := [1, 3, 2, 5, 1, 1, 3, 2, 3]
def baseStart_305877 : Nat := 118140960795 + 305877 * 2 ^ 59
def prefixEnd_305877 : Nat := 4983230072969 + 3 ^ 40 * 305877 * 2
def baseEnd_305877 : Nat := 69805298735735550458135

theorem tailTrace_305877 : CollatzResearch.WordTrace tailWord_305877 prefixEnd_305877 69805298735735550458135 := by
  unfold tailWord_305877
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156250712867343477699885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7437500475244895651799923 11156250712867343477699885)
  ·
    refine ⟨4183594017325253804137457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11156250712867343477699885 4183594017325253804137457)
    ·
      refine ⟨3137695512993940353103093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4183594017325253804137457 3137695512993940353103093)
      ·
        refine ⟨294158954343181908103415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3137695512993940353103093 294158954343181908103415)
        ·
          refine ⟨441238431514772862155123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294158954343181908103415 441238431514772862155123)
          ·
            refine ⟨661857647272159293232685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441238431514772862155123 661857647272159293232685)
            ·
              refine ⟨248196617727059734962257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 661857647272159293232685 248196617727059734962257)
              ·
                refine ⟨186147463295294801221693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248196617727059734962257 186147463295294801221693)
                ·
                  refine ⟨69805298735735550458135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186147463295294801221693 69805298735735550458135)
                  ·
                    rfl

theorem cell21_305877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_305877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305877 prefixEnd_305877 := by exact prefixLift 305877
  have htrace : WordTrace (prefixWord ++ tailWord_305877) baseStart_305877 baseEnd_305877 := by
    simpa [prefixWord, tailWord_305877, baseEnd_305877] using wordTrace_append hprefix tailTrace_305877
  have hstable : (prefixWord ++ tailWord_305877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305877).length < 2 ^ (prefixWord ++ tailWord_305877).sum := by decide
  have hdescent : baseEnd_305877 < baseStart_305877 := by decide
  rcases family_descends (prefixWord ++ tailWord_305877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305975 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 6]
def baseStart_305975 : Nat := 118140960795 + 305975 * 2 ^ 59
def prefixEnd_305975 : Nat := 4983230072969 + 3 ^ 40 * 305975 * 2
def baseEnd_305975 : Nat := 69827663670909157824601

theorem tailTrace_305975 : CollatzResearch.WordTrace tailWord_305975 prefixEnd_305975 69827663670909157824601 := by
  unfold tailWord_305975
  simp only [CollatzResearch.WordTrace]
  refine ⟨11159825066512306214767379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7439883377674870809844919 11159825066512306214767379)
  ·
    refine ⟨16739737599768459322151069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11159825066512306214767379 16739737599768459322151069)
    ·
      refine ⟨6277401599913172245806651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16739737599768459322151069 6277401599913172245806651)
      ·
        refine ⟨9416102399869758368709977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6277401599913172245806651 9416102399869758368709977)
        ·
          refine ⟨7062076799902318776532483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9416102399869758368709977 7062076799902318776532483)
          ·
            refine ⟨10593115199853478164798725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7062076799902318776532483 10593115199853478164798725)
            ·
              refine ⟨1986209099972527155899761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10593115199853478164798725 1986209099972527155899761)
              ·
                refine ⟨1489656824979395366924821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1986209099972527155899761 1489656824979395366924821)
                ·
                  refine ⟨69827663670909157824601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1489656824979395366924821 69827663670909157824601)
                  ·
                    rfl

theorem cell21_305975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_305975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_305975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_305975 prefixEnd_305975 := by exact prefixLift 305975
  have htrace : WordTrace (prefixWord ++ tailWord_305975) baseStart_305975 baseEnd_305975 := by
    simpa [prefixWord, tailWord_305975, baseEnd_305975] using wordTrace_append hprefix tailTrace_305975
  have hstable : (prefixWord ++ tailWord_305975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305975).length < 2 ^ (prefixWord ++ tailWord_305975).sum := by decide
  have hdescent : baseEnd_305975 < baseStart_305975 := by decide
  rcases family_descends (prefixWord ++ tailWord_305975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306009 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 4]
def baseStart_306009 : Nat := 118140960795 + 306009 * 2 ^ 59
def prefixEnd_306009 : Nat := 4983230072969 + 3 ^ 40 * 306009 * 2
def baseEnd_306009 : Nat := 69835422934132654257865

theorem tailTrace_306009 : CollatzResearch.WordTrace tailWord_306009 prefixEnd_306009 69835422934132654257865 := by
  unfold tailWord_306009
  simp only [CollatzResearch.WordTrace]
  refine ⟨11161065148389130021505081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7440710098926086681003387 11161065148389130021505081)
  ·
    refine ⟨8370798861291847516128811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11161065148389130021505081 8370798861291847516128811)
    ·
      refine ⟨12556198291937771274193217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8370798861291847516128811 12556198291937771274193217)
      ·
        refine ⟨9417148718953328455644913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12556198291937771274193217 9417148718953328455644913)
        ·
          refine ⟨7062861539214996341733685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9417148718953328455644913 7062861539214996341733685)
          ·
            refine ⟨662143269301405907037533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7062861539214996341733685 662143269301405907037533)
            ·
              refine ⟨248303725988027215139075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662143269301405907037533 248303725988027215139075)
              ·
                refine ⟨372455588982040822708613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248303725988027215139075 372455588982040822708613)
                ·
                  refine ⟨69835422934132654257865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372455588982040822708613 69835422934132654257865)
                  ·
                    rfl

theorem cell21_306009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_306009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306009 prefixEnd_306009 := by exact prefixLift 306009
  have htrace : WordTrace (prefixWord ++ tailWord_306009) baseStart_306009 baseEnd_306009 := by
    simpa [prefixWord, tailWord_306009, baseEnd_306009] using wordTrace_append hprefix tailTrace_306009
  have hstable : (prefixWord ++ tailWord_306009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306009).length < 2 ^ (prefixWord ++ tailWord_306009).sum := by decide
  have hdescent : baseEnd_306009 < baseStart_306009 := by decide
  rcases family_descends (prefixWord ++ tailWord_306009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306023 : List Nat := [1, 1, 5, 1, 2, 2, 4, 5]
def baseStart_306023 : Nat := 118140960795 + 306023 * 2 ^ 59
def prefixEnd_306023 : Nat := 4983230072969 + 3 ^ 40 * 306023 * 2
def baseEnd_306023 : Nat := 23279539308290580341501

theorem tailTrace_306023 : CollatzResearch.WordTrace tailWord_306023 prefixEnd_306023 23279539308290580341501 := by
  unfold tailWord_306023
  simp only [CollatzResearch.WordTrace]
  refine ⟨11161575770338410412514723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7441050513558940275009815 11161575770338410412514723)
  ·
    refine ⟨16742363655507615618772085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11161575770338410412514723 16742363655507615618772085)
    ·
      refine ⟨1569596592703838964259883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16742363655507615618772085 1569596592703838964259883)
      ·
        refine ⟨2354394889055758446389825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569596592703838964259883 2354394889055758446389825)
        ·
          refine ⟨1765796166791818834792369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2354394889055758446389825 1765796166791818834792369)
          ·
            refine ⟨1324347125093864126094277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1765796166791818834792369 1324347125093864126094277)
            ·
              refine ⟨248315085955099523642677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1324347125093864126094277 248315085955099523642677)
              ·
                refine ⟨23279539308290580341501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 248315085955099523642677 23279539308290580341501)
                ·
                  rfl

theorem cell21_306023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 5].length) (baseStart_306023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306023 prefixEnd_306023 := by exact prefixLift 306023
  have htrace : WordTrace (prefixWord ++ tailWord_306023) baseStart_306023 baseEnd_306023 := by
    simpa [prefixWord, tailWord_306023, baseEnd_306023] using wordTrace_append hprefix tailTrace_306023
  have hstable : (prefixWord ++ tailWord_306023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306023).length < 2 ^ (prefixWord ++ tailWord_306023).sum := by decide
  have hdescent : baseEnd_306023 < baseStart_306023 := by decide
  rcases family_descends (prefixWord ++ tailWord_306023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306051 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 6]
def baseStart_306051 : Nat := 118140960795 + 306051 * 2 ^ 59
def prefixEnd_306051 : Nat := 4983230072969 + 3 ^ 40 * 306051 * 2
def baseEnd_306051 : Nat := 69845007906349914557779

theorem tailTrace_306051 : CollatzResearch.WordTrace tailWord_306051 prefixEnd_306051 69845007906349914557779 := by
  unfold tailWord_306051
  simp only [CollatzResearch.WordTrace]
  refine ⟨11162597014236971194534007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7441731342824647463022671 11162597014236971194534007)
  ·
    refine ⟨16743895521355456791801011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11162597014236971194534007 16743895521355456791801011)
    ·
      refine ⟨25115843282033185187701517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16743895521355456791801011 25115843282033185187701517)
      ·
        refine ⟨9418441230762444445388069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25115843282033185187701517 9418441230762444445388069)
        ·
          refine ⟨1765957730767958333510263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9418441230762444445388069 1765957730767958333510263)
          ·
            refine ⟨2648936596151937500265395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765957730767958333510263 2648936596151937500265395)
            ·
              refine ⟨3973404894227906250398093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2648936596151937500265395 3973404894227906250398093)
              ·
                refine ⟨1490026835335464843899285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3973404894227906250398093 1490026835335464843899285)
                ·
                  refine ⟨69845007906349914557779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1490026835335464843899285 69845007906349914557779)
                  ·
                    rfl

theorem cell21_306051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_306051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306051 prefixEnd_306051 := by exact prefixLift 306051
  have htrace : WordTrace (prefixWord ++ tailWord_306051) baseStart_306051 baseEnd_306051 := by
    simpa [prefixWord, tailWord_306051, baseEnd_306051] using wordTrace_append hprefix tailTrace_306051
  have hstable : (prefixWord ++ tailWord_306051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306051).length < 2 ^ (prefixWord ++ tailWord_306051).sum := by decide
  have hdescent : baseEnd_306051 < baseStart_306051 := by decide
  rcases family_descends (prefixWord ++ tailWord_306051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306130 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_306130 : Nat := 118140960795 + 306130 * 2 ^ 59
def prefixEnd_306130 : Nat := 4983230072969 + 3 ^ 40 * 306130 * 2
def baseEnd_306130 : Nat := 69863036782663332740951

theorem tailTrace_306130 : CollatzResearch.WordTrace tailWord_306130 prefixEnd_306130 69863036782663332740951 := by
  unfold tailWord_306130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2791369595237691921664961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7443652253967178457773229 2791369595237691921664961)
  ·
    refine ⟨2093527196428268941248721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2791369595237691921664961 2093527196428268941248721)
    ·
      refine ⟨1570145397321201705936541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2093527196428268941248721 1570145397321201705936541)
      ·
        refine ⟨588804523995450639726203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1570145397321201705936541 588804523995450639726203)
        ·
          refine ⟨883206785993175959589305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588804523995450639726203 883206785993175959589305)
          ·
            refine ⟨662405089494881969691979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883206785993175959589305 662405089494881969691979)
            ·
              refine ⟨993607634242322954537969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662405089494881969691979 993607634242322954537969)
              ·
                refine ⟨745205725681742215903477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 993607634242322954537969 745205725681742215903477)
                ·
                  refine ⟨69863036782663332740951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 745205725681742215903477 69863036782663332740951)
                  ·
                    rfl

theorem cell21_306130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_306130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306130 prefixEnd_306130 := by exact prefixLift 306130
  have htrace : WordTrace (prefixWord ++ tailWord_306130) baseStart_306130 baseEnd_306130 := by
    simpa [prefixWord, tailWord_306130, baseEnd_306130] using wordTrace_append hprefix tailTrace_306130
  have hstable : (prefixWord ++ tailWord_306130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306130).length < 2 ^ (prefixWord ++ tailWord_306130).sum := by decide
  have hdescent : baseEnd_306130 < baseStart_306130 := by decide
  rcases family_descends (prefixWord ++ tailWord_306130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306161 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 4]
def baseStart_306161 : Nat := 118140960795 + 306161 * 2 ^ 59
def prefixEnd_306161 : Nat := 4983230072969 + 3 ^ 40 * 306161 * 2
def baseEnd_306161 : Nat := 69870111405014167724221

theorem tailTrace_306161 : CollatzResearch.WordTrace tailWord_306161 prefixEnd_306161 69870111405014167724221 := by
  unfold tailWord_306161
  simp only [CollatzResearch.WordTrace]
  refine ⟨11166609043838459981038337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7444406029225639987358891 11166609043838459981038337)
  ·
    refine ⟨8374956782878844985778753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11166609043838459981038337 8374956782878844985778753)
    ·
      refine ⟨6281217587159133739334065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8374956782878844985778753 6281217587159133739334065)
      ·
        refine ⟨4710913190369350304500549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6281217587159133739334065 4710913190369350304500549)
        ·
          refine ⟨883296223194253182093853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4710913190369350304500549 883296223194253182093853)
          ·
            refine ⟨331236083697844943285195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 883296223194253182093853 331236083697844943285195)
            ·
              refine ⟨496854125546767414927793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331236083697844943285195 496854125546767414927793)
              ·
                refine ⟨372640594160075561195845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496854125546767414927793 372640594160075561195845)
                ·
                  refine ⟨69870111405014167724221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372640594160075561195845 69870111405014167724221)
                  ·
                    rfl

theorem cell21_306161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_306161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306161 prefixEnd_306161 := by exact prefixLift 306161
  have htrace : WordTrace (prefixWord ++ tailWord_306161) baseStart_306161 baseEnd_306161 := by
    simpa [prefixWord, tailWord_306161, baseEnd_306161] using wordTrace_append hprefix tailTrace_306161
  have hstable : (prefixWord ++ tailWord_306161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306161).length < 2 ^ (prefixWord ++ tailWord_306161).sum := by decide
  have hdescent : baseEnd_306161 < baseStart_306161 := by decide
  rcases family_descends (prefixWord ++ tailWord_306161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306237 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 4]
def baseStart_306237 : Nat := 118140960795 + 306237 * 2 ^ 59
def prefixEnd_306237 : Nat := 4983230072969 + 3 ^ 40 * 306237 * 2
def baseEnd_306237 : Nat := 69887455640454924457399

theorem tailTrace_306237 : CollatzResearch.WordTrace tailWord_306237 prefixEnd_306237 69887455640454924457399 := by
  unfold tailWord_306237
  simp only [CollatzResearch.WordTrace]
  refine ⟨11169380991563124960804965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7446253994375416640536643 11169380991563124960804965)
  ·
    refine ⟨2094258935918085930150931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11169380991563124960804965 2094258935918085930150931)
    ·
      refine ⟨3141388403877128895226397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2094258935918085930150931 3141388403877128895226397)
      ·
        refine ⟨1178020651453923335709899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3141388403877128895226397 1178020651453923335709899)
        ·
          refine ⟨1767030977180885003564849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178020651453923335709899 1767030977180885003564849)
          ·
            refine ⟨1325273232885663752673637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1767030977180885003564849 1325273232885663752673637)
            ·
              refine ⟨248488731166061953626307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1325273232885663752673637 248488731166061953626307)
              ·
                refine ⟨372733096749092930439461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248488731166061953626307 372733096749092930439461)
                ·
                  refine ⟨69887455640454924457399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372733096749092930439461 69887455640454924457399)
                  ·
                    rfl

theorem cell21_306237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_306237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306237 prefixEnd_306237 := by exact prefixLift 306237
  have htrace : WordTrace (prefixWord ++ tailWord_306237) baseStart_306237 baseEnd_306237 := by
    simpa [prefixWord, tailWord_306237, baseEnd_306237] using wordTrace_append hprefix tailTrace_306237
  have hstable : (prefixWord ++ tailWord_306237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306237).length < 2 ^ (prefixWord ++ tailWord_306237).sum := by decide
  have hdescent : baseEnd_306237 < baseStart_306237 := by decide
  rcases family_descends (prefixWord ++ tailWord_306237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306248 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_306248 : Nat := 118140960795 + 306248 * 2 ^ 59
def prefixEnd_306248 : Nat := 4983230072969 + 3 ^ 40 * 306248 * 2
def baseEnd_306248 : Nat := 69889965990321349774043

theorem tailTrace_306248 : CollatzResearch.WordTrace tailWord_306248 prefixEnd_306248 69889965990321349774043 := by
  unfold tailWord_306248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5584891097261636919727699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7446521463015515892970265 5584891097261636919727699)
  ·
    refine ⟨8377336645892455379591549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5584891097261636919727699 8377336645892455379591549)
    ·
      refine ⟨3141501242209670767346831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8377336645892455379591549 3141501242209670767346831)
      ·
        refine ⟨4712251863314506151020247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3141501242209670767346831 4712251863314506151020247)
        ·
          refine ⟨7068377794971759226530371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4712251863314506151020247 7068377794971759226530371)
          ·
            refine ⟨10602566692457638839795557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068377794971759226530371 10602566692457638839795557)
            ·
              refine ⟨1987981254835807282461667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10602566692457638839795557 1987981254835807282461667)
              ·
                refine ⟨2981971882253710923692501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987981254835807282461667 2981971882253710923692501)
                ·
                  refine ⟨69889965990321349774043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2981971882253710923692501 69889965990321349774043)
                  ·
                    rfl

theorem cell21_306248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_306248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306248 prefixEnd_306248 := by exact prefixLift 306248
  have htrace : WordTrace (prefixWord ++ tailWord_306248) baseStart_306248 baseEnd_306248 := by
    simpa [prefixWord, tailWord_306248, baseEnd_306248] using wordTrace_append hprefix tailTrace_306248
  have hstable : (prefixWord ++ tailWord_306248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306248).length < 2 ^ (prefixWord ++ tailWord_306248).sum := by decide
  have hdescent : baseEnd_306248 < baseStart_306248 := by decide
  rcases family_descends (prefixWord ++ tailWord_306248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306302 : List Nat := [4, 2, 4, 1, 1, 1, 3, 5]
def baseStart_306302 : Nat := 118140960795 + 306302 * 2 ^ 59
def prefixEnd_306302 : Nat := 4983230072969 + 3 ^ 40 * 306302 * 2
def baseEnd_306302 : Nat := 23300763175343085291311

theorem tailTrace_306302 : CollatzResearch.WordTrace tailWord_306302 prefixEnd_306302 23300763175343085291311 := by
  unfold tailWord_306302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396468967040955132740145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7447834490885094041280773 1396468967040955132740145)
  ·
    refine ⟨1047351725280716349555109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1396468967040955132740145 1047351725280716349555109)
    ·
      refine ⟨196378448490134315541583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1047351725280716349555109 196378448490134315541583)
      ·
        refine ⟨294567672735201473312375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196378448490134315541583 294567672735201473312375)
        ·
          refine ⟨441851509102802209968563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294567672735201473312375 441851509102802209968563)
          ·
            refine ⟨662777263654203314952845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441851509102802209968563 662777263654203314952845)
            ·
              refine ⟨248541473870326243107317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662777263654203314952845 248541473870326243107317)
              ·
                refine ⟨23300763175343085291311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 248541473870326243107317 23300763175343085291311)
                ·
                  rfl

theorem cell21_306302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_306302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306302 prefixEnd_306302 := by exact prefixLift 306302
  have htrace : WordTrace (prefixWord ++ tailWord_306302) baseStart_306302 baseEnd_306302 := by
    simpa [prefixWord, tailWord_306302, baseEnd_306302] using wordTrace_append hprefix tailTrace_306302
  have hstable : (prefixWord ++ tailWord_306302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306302).length < 2 ^ (prefixWord ++ tailWord_306302).sum := by decide
  have hdescent : baseEnd_306302 < baseStart_306302 := by decide
  rcases family_descends (prefixWord ++ tailWord_306302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306341 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 5]
def baseStart_306341 : Nat := 118140960795 + 306341 * 2 ^ 59
def prefixEnd_306341 : Nat := 4983230072969 + 3 ^ 40 * 306341 * 2
def baseEnd_306341 : Nat := 69911189857373854723853

theorem tailTrace_306341 : CollatzResearch.WordTrace tailWord_306341 prefixEnd_306341 69911189857373854723853 := by
  unfold tailWord_306341
  simp only [CollatzResearch.WordTrace]
  refine ⟨11173174183186350722590877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7448782788790900481727251 11173174183186350722590877)
  ·
    refine ⟨4189940318694881520971579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11173174183186350722590877 4189940318694881520971579)
    ·
      refine ⟨6284910478042322281457369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4189940318694881520971579 6284910478042322281457369)
      ·
        refine ⟨4713682858531741711093027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6284910478042322281457369 4713682858531741711093027)
        ·
          refine ⟨7070524287797612566639541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4713682858531741711093027 7070524287797612566639541)
          ·
            refine ⟨662861651981026178122457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7070524287797612566639541 662861651981026178122457)
            ·
              refine ⟨497146238985769633591843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662861651981026178122457 497146238985769633591843)
              ·
                refine ⟨745719358478654450387765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497146238985769633591843 745719358478654450387765)
                ·
                  refine ⟨69911189857373854723853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 745719358478654450387765 69911189857373854723853)
                  ·
                    rfl

theorem cell21_306341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_306341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306341 prefixEnd_306341 := by exact prefixLift 306341
  have htrace : WordTrace (prefixWord ++ tailWord_306341) baseStart_306341 baseEnd_306341 := by
    simpa [prefixWord, tailWord_306341, baseEnd_306341] using wordTrace_append hprefix tailTrace_306341
  have hstable : (prefixWord ++ tailWord_306341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306341).length < 2 ^ (prefixWord ++ tailWord_306341).sum := by decide
  have hdescent : baseEnd_306341 < baseStart_306341 := by decide
  rcases family_descends (prefixWord ++ tailWord_306341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306355 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 4]
def baseStart_306355 : Nat := 118140960795 + 306355 * 2 ^ 59
def prefixEnd_306355 : Nat := 4983230072969 + 3 ^ 40 * 306355 * 2
def baseEnd_306355 : Nat := 69914384848112941490491

theorem tailTrace_306355 : CollatzResearch.WordTrace tailWord_306355 prefixEnd_306355 69914384848112941490491 := by
  unfold tailWord_306355
  simp only [CollatzResearch.WordTrace]
  refine ⟨11173684805135631113600519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7449123203423754075733679 11173684805135631113600519)
  ·
    refine ⟨16760527207703446670400779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11173684805135631113600519 16760527207703446670400779)
    ·
      refine ⟨25140790811555170005601169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16760527207703446670400779 25140790811555170005601169)
      ·
        refine ⟨18855593108666377504200877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25140790811555170005601169 18855593108666377504200877)
        ·
          refine ⟨7070847415749891564075329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18855593108666377504200877 7070847415749891564075329)
          ·
            refine ⟨5303135561812418673056497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7070847415749891564075329 5303135561812418673056497)
            ·
              refine ⟨3977351671359314004792373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5303135561812418673056497 3977351671359314004792373)
              ·
                refine ⟨372876719189935687949285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3977351671359314004792373 372876719189935687949285)
                ·
                  refine ⟨69914384848112941490491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 372876719189935687949285 69914384848112941490491)
                  ·
                    rfl

theorem cell21_306355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 4].length) (baseStart_306355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306355 prefixEnd_306355 := by exact prefixLift 306355
  have htrace : WordTrace (prefixWord ++ tailWord_306355) baseStart_306355 baseEnd_306355 := by
    simpa [prefixWord, tailWord_306355, baseEnd_306355] using wordTrace_append hprefix tailTrace_306355
  have hstable : (prefixWord ++ tailWord_306355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306355).length < 2 ^ (prefixWord ++ tailWord_306355).sum := by decide
  have hdescent : baseEnd_306355 < baseStart_306355 := by decide
  rcases family_descends (prefixWord ++ tailWord_306355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306620 : List Nat := [2, 2, 2, 4, 2, 2, 2, 2, 3]
def baseStart_306620 : Nat := 118140960795 + 306620 * 2 ^ 59
def prefixEnd_306620 : Nat := 4983230072969 + 3 ^ 40 * 306620 * 2
def baseEnd_306620 : Nat := 69974861458531369573283

theorem tailTrace_306620 : CollatzResearch.WordTrace tailWord_306620 prefixEnd_306620 69974861458531369573283 := by
  unfold tailWord_306620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591675074587790685998657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7455566766117054247998209 5591675074587790685998657)
  ·
    refine ⟨4193756305940843014498993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5591675074587790685998657 4193756305940843014498993)
    ·
      refine ⟨3145317229455632260874245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4193756305940843014498993 3145317229455632260874245)
      ·
        refine ⟨589746980522931048913921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3145317229455632260874245 589746980522931048913921)
        ·
          refine ⟨442310235392198286685441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589746980522931048913921 442310235392198286685441)
          ·
            refine ⟨331732676544148715014081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442310235392198286685441 331732676544148715014081)
            ·
              refine ⟨248799507408111536260561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331732676544148715014081 248799507408111536260561)
              ·
                refine ⟨186599630556083652195421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248799507408111536260561 186599630556083652195421)
                ·
                  refine ⟨69974861458531369573283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186599630556083652195421 69974861458531369573283)
                  ·
                    rfl

theorem cell21_306620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_306620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306620 prefixEnd_306620 := by exact prefixLift 306620
  have htrace : WordTrace (prefixWord ++ tailWord_306620) baseStart_306620 baseEnd_306620 := by
    simpa [prefixWord, tailWord_306620, baseEnd_306620] using wordTrace_append hprefix tailTrace_306620
  have hstable : (prefixWord ++ tailWord_306620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306620).length < 2 ^ (prefixWord ++ tailWord_306620).sum := by decide
  have hdescent : baseEnd_306620 < baseStart_306620 := by decide
  rcases family_descends (prefixWord ++ tailWord_306620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306673 : List Nat := [1, 2, 2, 2, 3, 3, 8]
def baseStart_306673 : Nat := 118140960795 + 306673 * 2 ^ 59
def prefixEnd_306673 : Nat := 4983230072969 + 3 ^ 40 * 306673 * 2
def baseEnd_306673 : Nat := 7776328531179450576649

theorem tailTrace_306673 : CollatzResearch.WordTrace tailWord_306673 prefixEnd_306673 7776328531179450576649 := by
  unfold tailWord_306673
  simp only [CollatzResearch.WordTrace]
  refine ⟨11185283217983571423676673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7456855478655714282451115 11185283217983571423676673)
  ·
    refine ⟨8388962413487678567757505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11185283217983571423676673 8388962413487678567757505)
    ·
      refine ⟨6291721810115758925818129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8388962413487678567757505 6291721810115758925818129)
      ·
        refine ⟨4718791357586819194363597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6291721810115758925818129 4718791357586819194363597)
        ·
          refine ⟨1769546759095057197886349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4718791357586819194363597 1769546759095057197886349)
          ·
            refine ⟨663580034660646449207381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1769546759095057197886349 663580034660646449207381)
            ·
              refine ⟨7776328531179450576649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 663580034660646449207381 7776328531179450576649)
              ·
                rfl

theorem cell21_306673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 8].length) (baseStart_306673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306673 prefixEnd_306673 := by exact prefixLift 306673
  have htrace : WordTrace (prefixWord ++ tailWord_306673) baseStart_306673 baseEnd_306673 := by
    simpa [prefixWord, tailWord_306673, baseEnd_306673] using wordTrace_append hprefix tailTrace_306673
  have hstable : (prefixWord ++ tailWord_306673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306673).length < 2 ^ (prefixWord ++ tailWord_306673).sum := by decide
  have hdescent : baseEnd_306673 < baseStart_306673 := by decide
  rcases family_descends (prefixWord ++ tailWord_306673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306763 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 7]
def baseStart_306763 : Nat := 118140960795 + 306763 * 2 ^ 59
def prefixEnd_306763 : Nat := 4983230072969 + 3 ^ 40 * 306763 * 2
def baseEnd_306763 : Nat := 70007496006794898689657

theorem tailTrace_306763 : CollatzResearch.WordTrace tailWord_306763 prefixEnd_306763 70007496006794898689657 := by
  unfold tailWord_306763
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188565787657516794452943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7459043858438344529635295 11188565787657516794452943)
  ·
    refine ⟨16782848681486275191679415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11188565787657516794452943 16782848681486275191679415)
    ·
      refine ⟨25174273022229412787519123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16782848681486275191679415 25174273022229412787519123)
      ·
        refine ⟨37761409533344119181278685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25174273022229412787519123 37761409533344119181278685)
        ·
          refine ⟨14160528575004044692979507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37761409533344119181278685 14160528575004044692979507)
          ·
            refine ⟨21240792862506067039469261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14160528575004044692979507 21240792862506067039469261)
            ·
              refine ⟨7965297323439775139800973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21240792862506067039469261 7965297323439775139800973)
              ·
                refine ⟨2986986496289915677425365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7965297323439775139800973 2986986496289915677425365)
                ·
                  refine ⟨70007496006794898689657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2986986496289915677425365 70007496006794898689657)
                  ·
                    rfl

theorem cell21_306763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_306763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306763 prefixEnd_306763 := by exact prefixLift 306763
  have htrace : WordTrace (prefixWord ++ tailWord_306763) baseStart_306763 baseEnd_306763 := by
    simpa [prefixWord, tailWord_306763, baseEnd_306763] using wordTrace_append hprefix tailTrace_306763
  have hstable : (prefixWord ++ tailWord_306763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306763).length < 2 ^ (prefixWord ++ tailWord_306763).sum := by decide
  have hdescent : baseEnd_306763 < baseStart_306763 := by decide
  rcases family_descends (prefixWord ++ tailWord_306763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306862 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_306862 : Nat := 118140960795 + 306862 * 2 ^ 59
def prefixEnd_306862 : Nat := 4983230072969 + 3 ^ 40 * 306862 * 2
def baseEnd_306862 : Nat := 70030089155592726539455

theorem tailTrace_306862 : CollatzResearch.WordTrace tailWord_306862 prefixEnd_306862 70030089155592726539455 := by
  unfold tailWord_306862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399022076787357087788355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7461451076199237801537893 1399022076787357087788355)
  ·
    refine ⟨2098533115181035631682533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1399022076787357087788355 2098533115181035631682533)
    ·
      refine ⟨393474959096444180940475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2098533115181035631682533 393474959096444180940475)
      ·
        refine ⟨590212438644666271410713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393474959096444180940475 590212438644666271410713)
        ·
          refine ⟨442659328983499703558035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 590212438644666271410713 442659328983499703558035)
          ·
            refine ⟨663988993475249555337053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442659328983499703558035 663988993475249555337053)
            ·
              refine ⟨248995872553218583251395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 663988993475249555337053 248995872553218583251395)
              ·
                refine ⟨373493808829827874877093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248995872553218583251395 373493808829827874877093)
                ·
                  refine ⟨70030089155592726539455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373493808829827874877093 70030089155592726539455)
                  ·
                    rfl

theorem cell21_306862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_306862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306862 prefixEnd_306862 := by exact prefixLift 306862
  have htrace : WordTrace (prefixWord ++ tailWord_306862) baseStart_306862 baseEnd_306862 := by
    simpa [prefixWord, tailWord_306862, baseEnd_306862] using wordTrace_append hprefix tailTrace_306862
  have hstable : (prefixWord ++ tailWord_306862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306862).length < 2 ^ (prefixWord ++ tailWord_306862).sum := by decide
  have hdescent : baseEnd_306862 < baseStart_306862 := by decide
  rcases family_descends (prefixWord ++ tailWord_306862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306882 : List Nat := [3, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_306882 : Nat := 118140960795 + 306882 * 2 ^ 59
def prefixEnd_306882 : Nat := 4983230072969 + 3 ^ 40 * 306882 * 2
def baseEnd_306882 : Nat := 70034653428077136206081

theorem tailTrace_306882 : CollatzResearch.WordTrace tailWord_306882 prefixEnd_306882 70034653428077136206081 := by
  unfold tailWord_306882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2798226518556600029508725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7461937382817600078689933 2798226518556600029508725)
  ·
    refine ⟨262333736114681252766443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2798226518556600029508725 262333736114681252766443)
    ·
      refine ⟨393500604172021879149665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262333736114681252766443 393500604172021879149665)
      ·
        refine ⟨295125453129016409362249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393500604172021879149665 295125453129016409362249)
        ·
          refine ⟨221344089846762307021687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295125453129016409362249 221344089846762307021687)
          ·
            refine ⟨332016134770143460532531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221344089846762307021687 332016134770143460532531)
            ·
              refine ⟨498024202155215190798797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332016134770143460532531 498024202155215190798797)
              ·
                refine ⟨186759075808205696549549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 498024202155215190798797 186759075808205696549549)
                ·
                  refine ⟨70034653428077136206081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186759075808205696549549 70034653428077136206081)
                  ·
                    rfl

theorem cell21_306882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_306882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306882 prefixEnd_306882 := by exact prefixLift 306882
  have htrace : WordTrace (prefixWord ++ tailWord_306882) baseStart_306882 baseEnd_306882 := by
    simpa [prefixWord, tailWord_306882, baseEnd_306882] using wordTrace_append hprefix tailTrace_306882
  have hstable : (prefixWord ++ tailWord_306882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306882).length < 2 ^ (prefixWord ++ tailWord_306882).sum := by decide
  have hdescent : baseEnd_306882 < baseStart_306882 := by decide
  rcases family_descends (prefixWord ++ tailWord_306882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306977 : List Nat := [1, 2, 3, 2, 1, 3, 3, 6]
def baseStart_306977 : Nat := 118140960795 + 306977 * 2 ^ 59
def prefixEnd_306977 : Nat := 4983230072969 + 3 ^ 40 * 306977 * 2
def baseEnd_306977 : Nat := 23352111240792694040851

theorem tailTrace_306977 : CollatzResearch.WordTrace tailWord_306977 prefixEnd_306977 23352111240792694040851 := by
  unfold tailWord_306977
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196371008882231342743185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7464247339254820895162123 11196371008882231342743185)
  ·
    refine ⟨8397278256661673507057389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11196371008882231342743185 8397278256661673507057389)
    ·
      refine ⟨3148979346248127565146521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8397278256661673507057389 3148979346248127565146521)
      ·
        refine ⟨2361734509686095673859891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3148979346248127565146521 2361734509686095673859891)
        ·
          refine ⟨3542601764529143510789837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2361734509686095673859891 3542601764529143510789837)
          ·
            refine ⟨1328475661698428816546189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3542601764529143510789837 1328475661698428816546189)
            ·
              refine ⟨498178373136910806204821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1328475661698428816546189 498178373136910806204821)
              ·
                refine ⟨23352111240792694040851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 498178373136910806204821 23352111240792694040851)
                ·
                  rfl

theorem cell21_306977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 6].length) (baseStart_306977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306977 prefixEnd_306977 := by exact prefixLift 306977
  have htrace : WordTrace (prefixWord ++ tailWord_306977) baseStart_306977 baseEnd_306977 := by
    simpa [prefixWord, tailWord_306977, baseEnd_306977] using wordTrace_append hprefix tailTrace_306977
  have hstable : (prefixWord ++ tailWord_306977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306977).length < 2 ^ (prefixWord ++ tailWord_306977).sum := by decide
  have hdescent : baseEnd_306977 < baseStart_306977 := by decide
  rcases family_descends (prefixWord ++ tailWord_306977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306991 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 5]
def baseStart_306991 : Nat := 118140960795 + 306991 * 2 ^ 59
def prefixEnd_306991 : Nat := 4983230072969 + 3 ^ 40 * 306991 * 2
def baseEnd_306991 : Nat := 70059528713117168889191

theorem tailTrace_306991 : CollatzResearch.WordTrace tailWord_306991 prefixEnd_306991 70059528713117168889191 := by
  unfold tailWord_306991
  simp only [CollatzResearch.WordTrace]
  refine ⟨11196881630831511733752827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7464587753887674489168551 11196881630831511733752827)
  ·
    refine ⟨16795322446247267600629241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11196881630831511733752827 16795322446247267600629241)
    ·
      refine ⟨12596491834685450700471931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16795322446247267600629241 12596491834685450700471931)
      ·
        refine ⟨18894737752028176050707897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12596491834685450700471931 18894737752028176050707897)
        ·
          refine ⟨14171053314021132038030923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18894737752028176050707897 14171053314021132038030923)
          ·
            refine ⟨21256579971031698057046385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14171053314021132038030923 21256579971031698057046385)
            ·
              refine ⟨15942434978273773542784789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21256579971031698057046385 15942434978273773542784789)
              ·
                refine ⟨747301639606583134818037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15942434978273773542784789 747301639606583134818037)
                ·
                  refine ⟨70059528713117168889191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 747301639606583134818037 70059528713117168889191)
                  ·
                    rfl

theorem cell21_306991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_306991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306991 prefixEnd_306991 := by exact prefixLift 306991
  have htrace : WordTrace (prefixWord ++ tailWord_306991) baseStart_306991 baseEnd_306991 := by
    simpa [prefixWord, tailWord_306991, baseEnd_306991] using wordTrace_append hprefix tailTrace_306991
  have hstable : (prefixWord ++ tailWord_306991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306991).length < 2 ^ (prefixWord ++ tailWord_306991).sum := by decide
  have hdescent : baseEnd_306991 < baseStart_306991 := by decide
  rcases family_descends (prefixWord ++ tailWord_306991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306994 : List Nat := [3, 2, 1, 1, 3, 3, 3, 5]
def baseStart_306994 : Nat := 118140960795 + 306994 * 2 ^ 59
def prefixEnd_306994 : Nat := 4983230072969 + 3 ^ 40 * 306994 * 2
def baseEnd_306994 : Nat := 23353404451329943446395

theorem tailTrace_306994 : CollatzResearch.WordTrace tailWord_306994 prefixEnd_306994 23353404451329943446395 := by
  unfold tailWord_306994
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799247762455160811528009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7464660699880428830741357 2799247762455160811528009)
  ·
    refine ⟨2099435821841370608646007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2799247762455160811528009 2099435821841370608646007)
    ·
      refine ⟨3149153732762055912969011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2099435821841370608646007 3149153732762055912969011)
      ·
        refine ⟨4723730599143083869453517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3149153732762055912969011 4723730599143083869453517)
        ·
          refine ⟨1771398974678656451045069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4723730599143083869453517 1771398974678656451045069)
          ·
            refine ⟨664274615504496169141901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1771398974678656451045069 664274615504496169141901)
            ·
              refine ⟨249102980814186063428213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 664274615504496169141901 249102980814186063428213)
              ·
                refine ⟨23353404451329943446395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249102980814186063428213 23353404451329943446395)
                ·
                  rfl

theorem cell21_306994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_306994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_306994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_306994 prefixEnd_306994 := by exact prefixLift 306994
  have htrace : WordTrace (prefixWord ++ tailWord_306994) baseStart_306994 baseEnd_306994 := by
    simpa [prefixWord, tailWord_306994, baseEnd_306994] using wordTrace_append hprefix tailTrace_306994
  have hstable : (prefixWord ++ tailWord_306994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306994).length < 2 ^ (prefixWord ++ tailWord_306994).sum := by decide
  have hdescent : baseEnd_306994 < baseStart_306994 := by decide
  rcases family_descends (prefixWord ++ tailWord_306994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307014 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_307014 : Nat := 118140960795 + 307014 * 2 ^ 59
def prefixEnd_307014 : Nat := 4983230072969 + 3 ^ 40 * 307014 * 2
def baseEnd_307014 : Nat := 70064777626474240005811

theorem tailTrace_307014 : CollatzResearch.WordTrace tailWord_307014 prefixEnd_307014 70064777626474240005811 := by
  unfold tailWord_307014
  simp only [CollatzResearch.WordTrace]
  refine ⟨349928765929630833182503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7465147006498791107893397 349928765929630833182503)
  ·
    refine ⟨524893148894446249773755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349928765929630833182503 524893148894446249773755)
    ·
      refine ⟨787339723341669374660633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524893148894446249773755 787339723341669374660633)
      ·
        refine ⟨590504792506252030995475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787339723341669374660633 590504792506252030995475)
        ·
          refine ⟨885757188759378046493213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590504792506252030995475 885757188759378046493213)
          ·
            refine ⟨332158945784766767434955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 885757188759378046493213 332158945784766767434955)
            ·
              refine ⟨498238418677150151152433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332158945784766767434955 498238418677150151152433)
              ·
                refine ⟨373678814007862613364325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498238418677150151152433 373678814007862613364325)
                ·
                  refine ⟨70064777626474240005811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 373678814007862613364325 70064777626474240005811)
                  ·
                    rfl

theorem cell21_307014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_307014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307014 prefixEnd_307014 := by exact prefixLift 307014
  have htrace : WordTrace (prefixWord ++ tailWord_307014) baseStart_307014 baseEnd_307014 := by
    simpa [prefixWord, tailWord_307014, baseEnd_307014] using wordTrace_append hprefix tailTrace_307014
  have hstable : (prefixWord ++ tailWord_307014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307014).length < 2 ^ (prefixWord ++ tailWord_307014).sum := by decide
  have hdescent : baseEnd_307014 < baseStart_307014 := by decide
  rcases family_descends (prefixWord ++ tailWord_307014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307025 : List Nat := [1, 2, 2, 1, 5, 1, 2, 4, 3]
def baseStart_307025 : Nat := 118140960795 + 307025 * 2 ^ 59
def prefixEnd_307025 : Nat := 4983230072969 + 3 ^ 40 * 307025 * 2
def baseEnd_307025 : Nat := 70067287976340665322455

theorem tailTrace_307025 : CollatzResearch.WordTrace tailWord_307025 prefixEnd_307025 70067287976340665322455 := by
  unfold tailWord_307025
  simp only [CollatzResearch.WordTrace]
  refine ⟨11198121712708335540490529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7465414475138890360327019 11198121712708335540490529)
  ·
    refine ⟨8398591284531251655367897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11198121712708335540490529 8398591284531251655367897)
    ·
      refine ⟨6298943463398438741525923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8398591284531251655367897 6298943463398438741525923)
      ·
        refine ⟨9448415195097658112288885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6298943463398438741525923 9448415195097658112288885)
        ·
          refine ⟨885788924540405448027083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9448415195097658112288885 885788924540405448027083)
          ·
            refine ⟨1328683386810608172040625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885788924540405448027083 1328683386810608172040625)
            ·
              refine ⟨996512540107956129030469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328683386810608172040625 996512540107956129030469)
              ·
                refine ⟨186846101270241774193213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 996512540107956129030469 186846101270241774193213)
                ·
                  refine ⟨70067287976340665322455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 186846101270241774193213 70067287976340665322455)
                  ·
                    rfl

theorem cell21_307025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_307025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307025 prefixEnd_307025 := by exact prefixLift 307025
  have htrace : WordTrace (prefixWord ++ tailWord_307025) baseStart_307025 baseEnd_307025 := by
    simpa [prefixWord, tailWord_307025, baseEnd_307025] using wordTrace_append hprefix tailTrace_307025
  have hstable : (prefixWord ++ tailWord_307025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307025).length < 2 ^ (prefixWord ++ tailWord_307025).sum := by decide
  have hdescent : baseEnd_307025 < baseStart_307025 := by decide
  rcases family_descends (prefixWord ++ tailWord_307025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307070 : List Nat := [4, 2, 3, 1, 1, 1, 9]
def baseStart_307070 : Nat := 118140960795 + 307070 * 2 ^ 59
def prefixEnd_307070 : Nat := 4983230072969 + 3 ^ 40 * 307070 * 2
def baseEnd_307070 : Nat := 7786395287714509674707

theorem tailTrace_307070 : CollatzResearch.WordTrace tailWord_307070 prefixEnd_307070 7786395287714509674707 := by
  unfold tailWord_307070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399970374693163528234833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7466508665030205483919109 1399970374693163528234833)
  ·
    refine ⟨1049977781019872646176125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1399970374693163528234833 1049977781019872646176125)
    ·
      refine ⟨393741667882452242316047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1049977781019872646176125 393741667882452242316047)
      ·
        refine ⟨590612501823678363474071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393741667882452242316047 590612501823678363474071)
        ·
          refine ⟨885918752735517545211107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590612501823678363474071 885918752735517545211107)
          ·
            refine ⟨1328878129103276317816661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885918752735517545211107 1328878129103276317816661)
            ·
              refine ⟨7786395287714509674707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1328878129103276317816661 7786395287714509674707)
              ·
                rfl

theorem cell21_307070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 9].length) (baseStart_307070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307070 prefixEnd_307070 := by exact prefixLift 307070
  have htrace : WordTrace (prefixWord ++ tailWord_307070) baseStart_307070 baseEnd_307070 := by
    simpa [prefixWord, tailWord_307070, baseEnd_307070] using wordTrace_append hprefix tailTrace_307070
  have hstable : (prefixWord ++ tailWord_307070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307070).length < 2 ^ (prefixWord ++ tailWord_307070).sum := by decide
  have hdescent : baseEnd_307070 < baseStart_307070 := by decide
  rcases family_descends (prefixWord ++ tailWord_307070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307143 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 5]
def baseStart_307143 : Nat := 118140960795 + 307143 * 2 ^ 59
def prefixEnd_307143 : Nat := 4983230072969 + 3 ^ 40 * 307143 * 2
def baseEnd_307143 : Nat := 70094217183998682355547

theorem tailTrace_307143 : CollatzResearch.WordTrace tailWord_307143 prefixEnd_307143 70094217183998682355547 := by
  unfold tailWord_307143
  simp only [CollatzResearch.WordTrace]
  refine ⟨11202425526280841693286083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7468283684187227795524055 11202425526280841693286083)
  ·
    refine ⟨16803638289421262539929125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11202425526280841693286083 16803638289421262539929125)
    ·
      refine ⟨3150682179266486726236711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16803638289421262539929125 3150682179266486726236711)
      ·
        refine ⟨4726023268899730089355067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150682179266486726236711 4726023268899730089355067)
        ·
          refine ⟨7089034903349595134032601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726023268899730089355067 7089034903349595134032601)
          ·
            refine ⟨5316776177512196350524451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7089034903349595134032601 5316776177512196350524451)
            ·
              refine ⟨7975164266268294525786677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5316776177512196350524451 7975164266268294525786677)
              ·
                refine ⟨747671649962652611792501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7975164266268294525786677 747671649962652611792501)
                ·
                  refine ⟨70094217183998682355547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 747671649962652611792501 70094217183998682355547)
                  ·
                    rfl

theorem cell21_307143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_307143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307143 prefixEnd_307143 := by exact prefixLift 307143
  have htrace : WordTrace (prefixWord ++ tailWord_307143) baseStart_307143 baseEnd_307143 := by
    simpa [prefixWord, tailWord_307143, baseEnd_307143] using wordTrace_append hprefix tailTrace_307143
  have hstable : (prefixWord ++ tailWord_307143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307143).length < 2 ^ (prefixWord ++ tailWord_307143).sum := by decide
  have hdescent : baseEnd_307143 < baseStart_307143 := by decide
  rcases family_descends (prefixWord ++ tailWord_307143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307219 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 5]
def baseStart_307219 : Nat := 118140960795 + 307219 * 2 ^ 59
def prefixEnd_307219 : Nat := 4983230072969 + 3 ^ 40 * 307219 * 2
def baseEnd_307219 : Nat := 70111561419439439088725

theorem tailTrace_307219 : CollatzResearch.WordTrace tailWord_307219 prefixEnd_307219 70111561419439439088725 := by
  unfold tailWord_307219
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205197474005506673052711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7470131649337004448701807 11205197474005506673052711)
  ·
    refine ⟨16807796211008260009579067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11205197474005506673052711 16807796211008260009579067)
    ·
      refine ⟨25211694316512390014368601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16807796211008260009579067 25211694316512390014368601)
      ·
        refine ⟨18908770737384292510776451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25211694316512390014368601 18908770737384292510776451)
        ·
          refine ⟨28363156106076438766164677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18908770737384292510776451 28363156106076438766164677)
          ·
            refine ⟨5318091769889332268655877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28363156106076438766164677 5318091769889332268655877)
            ·
              refine ⟨997142206854249800372977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5318091769889332268655877 997142206854249800372977)
              ·
                refine ⟨747856655140687350279733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997142206854249800372977 747856655140687350279733)
                ·
                  refine ⟨70111561419439439088725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 747856655140687350279733 70111561419439439088725)
                  ·
                    rfl

theorem cell21_307219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_307219 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307219 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307219 prefixEnd_307219 := by exact prefixLift 307219
  have htrace : WordTrace (prefixWord ++ tailWord_307219) baseStart_307219 baseEnd_307219 := by
    simpa [prefixWord, tailWord_307219, baseEnd_307219] using wordTrace_append hprefix tailTrace_307219
  have hstable : (prefixWord ++ tailWord_307219).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307219).length < 2 ^ (prefixWord ++ tailWord_307219).sum := by decide
  have hdescent : baseEnd_307219 < baseStart_307219 := by decide
  rcases family_descends (prefixWord ++ tailWord_307219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307239 : List Nat := [1, 1, 7, 1, 3, 1, 7]
def baseStart_307239 : Nat := 118140960795 + 307239 * 2 ^ 59
def prefixEnd_307239 : Nat := 4983230072969 + 3 ^ 40 * 307239 * 2
def baseEnd_307239 : Nat := 7790680632435983195039

theorem tailTrace_307239 : CollatzResearch.WordTrace tailWord_307239 prefixEnd_307239 7790680632435983195039 := by
  unfold tailWord_307239
  simp only [CollatzResearch.WordTrace]
  refine ⟨11205926933933050088780771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7470617955955366725853847 11205926933933050088780771)
  ·
    refine ⟨16808890400899575133171157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11205926933933050088780771 16808890400899575133171157)
    ·
      refine ⟨393958368771083792183699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16808890400899575133171157 393958368771083792183699)
      ·
        refine ⟨590937553156625688275549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393958368771083792183699 590937553156625688275549)
        ·
          refine ⟨221601582433734633103331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 590937553156625688275549 221601582433734633103331)
          ·
            refine ⟨332402373650601949654997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221601582433734633103331 332402373650601949654997)
            ·
              refine ⟨7790680632435983195039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 332402373650601949654997 7790680632435983195039)
              ·
                rfl

theorem cell21_307239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 7].length) (baseStart_307239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307239 prefixEnd_307239 := by exact prefixLift 307239
  have htrace : WordTrace (prefixWord ++ tailWord_307239) baseStart_307239 baseEnd_307239 := by
    simpa [prefixWord, tailWord_307239, baseEnd_307239] using wordTrace_append hprefix tailTrace_307239
  have hstable : (prefixWord ++ tailWord_307239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307239).length < 2 ^ (prefixWord ++ tailWord_307239).sum := by decide
  have hdescent : baseEnd_307239 < baseStart_307239 := by decide
  rcases family_descends (prefixWord ++ tailWord_307239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307250 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_307250 : Nat := 118140960795 + 307250 * 2 ^ 59
def prefixEnd_307250 : Nat := 4983230072969 + 3 ^ 40 * 307250 * 2
def baseEnd_307250 : Nat := 70118636041790274071995

theorem tailTrace_307250 : CollatzResearch.WordTrace tailWord_307250 prefixEnd_307250 70118636041790274071995 := by
  unfold tailWord_307250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2801582034223299741857801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7470885424595465978287469 2801582034223299741857801)
  ·
    refine ⟨2101186525667474806393351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2801582034223299741857801 2101186525667474806393351)
    ·
      refine ⟨3151779788501212209590027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2101186525667474806393351 3151779788501212209590027)
      ·
        refine ⟨4727669682751818314385041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3151779788501212209590027 4727669682751818314385041)
        ·
          refine ⟨3545752262063863735788781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4727669682751818314385041 3545752262063863735788781)
          ·
            refine ⟨1329657098273948900920793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3545752262063863735788781 1329657098273948900920793)
            ·
              refine ⟨997242823705461675690595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1329657098273948900920793 997242823705461675690595)
              ·
                refine ⟨1495864235558192513535893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997242823705461675690595 1495864235558192513535893)
                ·
                  refine ⟨70118636041790274071995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1495864235558192513535893 70118636041790274071995)
                  ·
                    rfl

theorem cell21_307250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_307250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307250 prefixEnd_307250 := by exact prefixLift 307250
  have htrace : WordTrace (prefixWord ++ tailWord_307250) baseStart_307250 baseEnd_307250 := by
    simpa [prefixWord, tailWord_307250, baseEnd_307250] using wordTrace_append hprefix tailTrace_307250
  have hstable : (prefixWord ++ tailWord_307250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307250).length < 2 ^ (prefixWord ++ tailWord_307250).sum := by decide
  have hdescent : baseEnd_307250 < baseStart_307250 := by decide
  rcases family_descends (prefixWord ++ tailWord_307250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307264 : List Nat := [2, 1, 1, 2, 2, 4, 1, 8]
def baseStart_307264 : Nat := 118140960795 + 307264 * 2 ^ 59
def prefixEnd_307264 : Nat := 4983230072969 + 3 ^ 40 * 307264 * 2
def baseEnd_307264 : Nat := 23373943677509786946211

theorem tailTrace_307264 : CollatzResearch.WordTrace tailWord_307264 prefixEnd_307264 23373943677509786946211 := by
  unfold tailWord_307264
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603419379421239679220423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7471225839228319572293897 5603419379421239679220423)
  ·
    refine ⟨8405129069131859518830635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5603419379421239679220423 8405129069131859518830635)
    ·
      refine ⟨12607693603697789278245953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8405129069131859518830635 12607693603697789278245953)
      ·
        refine ⟨9455770202773341958684465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12607693603697789278245953 9455770202773341958684465)
        ·
          refine ⟨7091827652080006469013349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9455770202773341958684465 7091827652080006469013349)
          ·
            refine ⟨1329717684765001212940003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7091827652080006469013349 1329717684765001212940003)
            ·
              refine ⟨1994576527147501819410005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329717684765001212940003 1994576527147501819410005)
              ·
                refine ⟨23373943677509786946211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1994576527147501819410005 23373943677509786946211)
                ·
                  rfl

theorem cell21_307264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_307264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307264 prefixEnd_307264 := by exact prefixLift 307264
  have htrace : WordTrace (prefixWord ++ tailWord_307264) baseStart_307264 baseEnd_307264 := by
    simpa [prefixWord, tailWord_307264, baseEnd_307264] using wordTrace_append hprefix tailTrace_307264
  have hstable : (prefixWord ++ tailWord_307264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307264).length < 2 ^ (prefixWord ++ tailWord_307264).sum := by decide
  have hdescent : baseEnd_307264 < baseStart_307264 := by decide
  rcases family_descends (prefixWord ++ tailWord_307264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307298 : List Nat := [3, 3, 2, 2, 3, 8]
def baseStart_307298 : Nat := 118140960795 + 307298 * 2 ^ 59
def prefixEnd_307298 : Nat := 4983230072969 + 3 ^ 40 * 307298 * 2
def baseEnd_307298 : Nat := 2597392233176031750811

theorem tailTrace_307298 : CollatzResearch.WordTrace tailWord_307298 prefixEnd_307298 2597392233176031750811 := by
  unfold tailWord_307298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802019710179825791294637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7472052560479535443452365 2802019710179825791294637)
  ·
    refine ⟨1050757391317434671735489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2802019710179825791294637 1050757391317434671735489)
    ·
      refine ⟨788068043488076003801617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050757391317434671735489 788068043488076003801617)
      ·
        refine ⟨591051032616057002851213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 788068043488076003801617 591051032616057002851213)
        ·
          refine ⟨221644137231021376069205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 591051032616057002851213 221644137231021376069205)
          ·
            refine ⟨2597392233176031750811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 221644137231021376069205 2597392233176031750811)
            ·
              rfl

theorem cell21_307298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 8].length) (baseStart_307298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307298 prefixEnd_307298 := by exact prefixLift 307298
  have htrace : WordTrace (prefixWord ++ tailWord_307298) baseStart_307298 baseEnd_307298 := by
    simpa [prefixWord, tailWord_307298, baseEnd_307298] using wordTrace_append hprefix tailTrace_307298
  have hstable : (prefixWord ++ tailWord_307298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307298).length < 2 ^ (prefixWord ++ tailWord_307298).sum := by decide
  have hdescent : baseEnd_307298 < baseStart_307298 := by decide
  rcases family_descends (prefixWord ++ tailWord_307298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307416 : List Nat := [2, 1, 2, 2, 4, 1, 9]
def baseStart_307416 : Nat := 118140960795 + 307416 * 2 ^ 59
def prefixEnd_307416 : Nat := 4983230072969 + 3 ^ 40 * 307416 * 2
def baseEnd_307416 : Nat := 7795168833712319367221

theorem tailTrace_307416 : CollatzResearch.WordTrace tailWord_307416 prefixEnd_307416 7795168833712319367221 := by
  unfold tailWord_307416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5606191327145904658987051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7474921769527872878649401 5606191327145904658987051)
  ·
    refine ⟨8409286990718856988480577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5606191327145904658987051 8409286990718856988480577)
    ·
      refine ⟨6306965243039142741360433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8409286990718856988480577 6306965243039142741360433)
      ·
        refine ⟨4730223932279357056020325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6306965243039142741360433 4730223932279357056020325)
        ·
          refine ⟨886916987302379448003811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4730223932279357056020325 886916987302379448003811)
          ·
            refine ⟨1330375480953569172005717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886916987302379448003811 1330375480953569172005717)
            ·
              refine ⟨7795168833712319367221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1330375480953569172005717 7795168833712319367221)
              ·
                rfl

theorem cell21_307416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 9].length) (baseStart_307416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307416 prefixEnd_307416 := by exact prefixLift 307416
  have htrace : WordTrace (prefixWord ++ tailWord_307416) baseStart_307416 baseEnd_307416 := by
    simpa [prefixWord, tailWord_307416, baseEnd_307416] using wordTrace_append hprefix tailTrace_307416
  have hstable : (prefixWord ++ tailWord_307416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307416).length < 2 ^ (prefixWord ++ tailWord_307416).sum := by decide
  have hdescent : baseEnd_307416 < baseStart_307416 := by decide
  rcases family_descends (prefixWord ++ tailWord_307416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307461 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 6]
def baseStart_307461 : Nat := 118140960795 + 307461 * 2 ^ 59
def prefixEnd_307461 : Nat := 4983230072969 + 3 ^ 40 * 307461 * 2
def baseEnd_307461 : Nat := 70166789116500796054897

theorem tailTrace_307461 : CollatzResearch.WordTrace tailWord_307461 prefixEnd_307461 70166789116500796054897 := by
  unfold tailWord_307461
  simp only [CollatzResearch.WordTrace]
  refine ⟨11214023939128782003362237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7476015959419188002241491 11214023939128782003362237)
  ·
    refine ⟨4205258977173293251260839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11214023939128782003362237 4205258977173293251260839)
    ·
      refine ⟨6307888465759939876891259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4205258977173293251260839 6307888465759939876891259)
      ·
        refine ⟨9461832698639909815336889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6307888465759939876891259 9461832698639909815336889)
        ·
          refine ⟨7096374523979932361502667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9461832698639909815336889 7096374523979932361502667)
          ·
            refine ⟨10644561785969898542254001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7096374523979932361502667 10644561785969898542254001)
            ·
              refine ⟨7983421339477423906690501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10644561785969898542254001 7983421339477423906690501)
              ·
                refine ⟨1496891501152016982504469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7983421339477423906690501 1496891501152016982504469)
                ·
                  refine ⟨70166789116500796054897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1496891501152016982504469 70166789116500796054897)
                  ·
                    rfl

theorem cell21_307461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_307461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307461 prefixEnd_307461 := by exact prefixLift 307461
  have htrace : WordTrace (prefixWord ++ tailWord_307461) baseStart_307461 baseEnd_307461 := by
    simpa [prefixWord, tailWord_307461, baseEnd_307461] using wordTrace_append hprefix tailTrace_307461
  have hstable : (prefixWord ++ tailWord_307461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307461).length < 2 ^ (prefixWord ++ tailWord_307461).sum := by decide
  have hdescent : baseEnd_307461 < baseStart_307461 := by decide
  rcases family_descends (prefixWord ++ tailWord_307461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307509 : List Nat := [1, 3, 3, 1, 2, 1, 5, 5]
def baseStart_307509 : Nat := 118140960795 + 307509 * 2 ^ 59
def prefixEnd_307509 : Nat := 4983230072969 + 3 ^ 40 * 307509 * 2
def baseEnd_307509 : Nat := 23392581123487793084933

theorem tailTrace_307509 : CollatzResearch.WordTrace tailWord_307509 prefixEnd_307509 23392581123487793084933 := by
  unfold tailWord_307509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11215774642954886201109581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7477183095303257467406387 11215774642954886201109581)
  ·
    refine ⟨4205915491108082325416093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11215774642954886201109581 4205915491108082325416093)
    ·
      refine ⟨1577218309165530872031035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4205915491108082325416093 1577218309165530872031035)
      ·
        refine ⟨2365827463748296308046553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577218309165530872031035 2365827463748296308046553)
        ·
          refine ⟨1774370597811222231034915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2365827463748296308046553 1774370597811222231034915)
          ·
            refine ⟨2661555896716833346552373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774370597811222231034915 2661555896716833346552373)
            ·
              refine ⟨249520865317203126239285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2661555896716833346552373 249520865317203126239285)
              ·
                refine ⟨23392581123487793084933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249520865317203126239285 23392581123487793084933)
                ·
                  rfl

theorem cell21_307509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 5].length) (baseStart_307509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307509 prefixEnd_307509 := by exact prefixLift 307509
  have htrace : WordTrace (prefixWord ++ tailWord_307509) baseStart_307509 baseEnd_307509 := by
    simpa [prefixWord, tailWord_307509, baseEnd_307509] using wordTrace_append hprefix tailTrace_307509
  have hstable : (prefixWord ++ tailWord_307509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307509).length < 2 ^ (prefixWord ++ tailWord_307509).sum := by decide
  have hdescent : baseEnd_307509 < baseStart_307509 := by decide
  rcases family_descends (prefixWord ++ tailWord_307509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307540 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_307540 : Nat := 118140960795 + 307540 * 2 ^ 59
def prefixEnd_307540 : Nat := 4983230072969 + 3 ^ 40 * 307540 * 2
def baseEnd_307540 : Nat := 70184817992814214238069

theorem tailTrace_307540 : CollatzResearch.WordTrace tailWord_307540 prefixEnd_307540 70184817992814214238069 := by
  unfold tailWord_307540
  simp only [CollatzResearch.WordTrace]
  refine ⟨5608452652921289247744037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7477936870561718996992049 5608452652921289247744037)
  ·
    refine ⟨1051584872422741733952007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5608452652921289247744037 1051584872422741733952007)
    ·
      refine ⟨1577377308634112600928011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051584872422741733952007 1577377308634112600928011)
      ·
        refine ⟨2366065962951168901392017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577377308634112600928011 2366065962951168901392017)
        ·
          refine ⟨1774549472213376676044013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2366065962951168901392017 1774549472213376676044013)
          ·
            refine ⟨665456052080016253516505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1774549472213376676044013 665456052080016253516505)
            ·
              refine ⟨499092039060012190137379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665456052080016253516505 499092039060012190137379)
              ·
                refine ⟨748638058590018285206069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499092039060012190137379 748638058590018285206069)
                ·
                  refine ⟨70184817992814214238069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 748638058590018285206069 70184817992814214238069)
                  ·
                    rfl

theorem cell21_307540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_307540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307540 prefixEnd_307540 := by exact prefixLift 307540
  have htrace : WordTrace (prefixWord ++ tailWord_307540) baseStart_307540 baseEnd_307540 := by
    simpa [prefixWord, tailWord_307540, baseEnd_307540] using wordTrace_append hprefix tailTrace_307540
  have hstable : (prefixWord ++ tailWord_307540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307540).length < 2 ^ (prefixWord ++ tailWord_307540).sum := by decide
  have hdescent : baseEnd_307540 < baseStart_307540 := by decide
  rcases family_descends (prefixWord ++ tailWord_307540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307568 : List Nat := [2, 1, 1, 1, 4, 4, 1, 7]
def baseStart_307568 : Nat := 118140960795 + 307568 * 2 ^ 59
def prefixEnd_307568 : Nat := 4983230072969 + 3 ^ 40 * 307568 * 2
def baseEnd_307568 : Nat := 23397069324764129257115

theorem tailTrace_307568 : CollatzResearch.WordTrace tailWord_307568 prefixEnd_307568 23397069324764129257115 := by
  unfold tailWord_307568
  simp only [CollatzResearch.WordTrace]
  refine ⟨5608963274870569638753679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7478617699827426185004905 5608963274870569638753679)
  ·
    refine ⟨8413444912305854458130519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5608963274870569638753679 8413444912305854458130519)
    ·
      refine ⟨12620167368458781687195779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8413444912305854458130519 12620167368458781687195779)
      ·
        refine ⟨18930251052688172530793669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12620167368458781687195779 18930251052688172530793669)
        ·
          refine ⟨3549422072379032349523813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18930251052688172530793669 3549422072379032349523813)
          ·
            refine ⟨665516638571068565535715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3549422072379032349523813 665516638571068565535715)
            ·
              refine ⟨998274957856602848303573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665516638571068565535715 998274957856602848303573)
              ·
                refine ⟨23397069324764129257115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 998274957856602848303573 23397069324764129257115)
                ·
                  rfl

theorem cell21_307568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_307568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307568 prefixEnd_307568 := by exact prefixLift 307568
  have htrace : WordTrace (prefixWord ++ tailWord_307568) baseStart_307568 baseEnd_307568 := by
    simpa [prefixWord, tailWord_307568, baseEnd_307568] using wordTrace_append hprefix tailTrace_307568
  have hstable : (prefixWord ++ tailWord_307568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307568).length < 2 ^ (prefixWord ++ tailWord_307568).sum := by decide
  have hdescent : baseEnd_307568 < baseStart_307568 := by decide
  rcases family_descends (prefixWord ++ tailWord_307568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307585 : List Nat := [1, 2, 4, 3, 1, 3, 7]
def baseStart_307585 : Nat := 118140960795 + 307585 * 2 ^ 59
def prefixEnd_307585 : Nat := 4983230072969 + 3 ^ 40 * 307585 * 2
def baseEnd_307585 : Nat := 7799454178433792887553

theorem tailTrace_307585 : CollatzResearch.WordTrace tailWord_307585 prefixEnd_307585 7799454178433792887553 := by
  unfold tailWord_307585
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218546590679551180876209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7479031060453034120584139 11218546590679551180876209)
  ·
    refine ⟨8413909943009663385657157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11218546590679551180876209 8413909943009663385657157)
    ·
      refine ⟨1577608114314311884810717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8413909943009663385657157 1577608114314311884810717)
      ·
        refine ⟨591603042867866956804019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1577608114314311884810717 591603042867866956804019)
        ·
          refine ⟨887404564301800435206029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591603042867866956804019 887404564301800435206029)
          ·
            refine ⟨332776711613175163202261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 887404564301800435206029 332776711613175163202261)
            ·
              refine ⟨7799454178433792887553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 332776711613175163202261 7799454178433792887553)
              ·
                rfl

theorem cell21_307585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 7].length) (baseStart_307585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307585 prefixEnd_307585 := by exact prefixLift 307585
  have htrace : WordTrace (prefixWord ++ tailWord_307585) baseStart_307585 baseEnd_307585 := by
    simpa [prefixWord, tailWord_307585, baseEnd_307585] using wordTrace_append hprefix tailTrace_307585
  have hstable : (prefixWord ++ tailWord_307585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307585).length < 2 ^ (prefixWord ++ tailWord_307585).sum := by decide
  have hdescent : baseEnd_307585 < baseStart_307585 := by decide
  rcases family_descends (prefixWord ++ tailWord_307585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307644 : List Nat := [2, 2, 2, 4, 1, 10]
def baseStart_307644 : Nat := 118140960795 + 307644 * 2 ^ 59
def prefixEnd_307644 : Nat := 4983230072969 + 3 ^ 40 * 307644 * 2
def baseEnd_307644 : Nat := 2600316748508634981649

theorem tailTrace_307644 : CollatzResearch.WordTrace tailWord_307644 prefixEnd_307644 2600316748508634981649 := by
  unfold tailWord_307644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610349248732902128636993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7480465664977202838182657 5610349248732902128636993)
  ·
    refine ⟨4207761936549676596477745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5610349248732902128636993 4207761936549676596477745)
    ·
      refine ⟨3155821452412257447358309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4207761936549676596477745 3155821452412257447358309)
      ·
        refine ⟨591716522327298271379683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3155821452412257447358309 591716522327298271379683)
        ·
          refine ⟨887574783490947407069525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591716522327298271379683 887574783490947407069525)
          ·
            refine ⟨2600316748508634981649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 887574783490947407069525 2600316748508634981649)
            ·
              rfl

theorem cell21_307644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 10].length) (baseStart_307644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307644 prefixEnd_307644 := by exact prefixLift 307644
  have htrace : WordTrace (prefixWord ++ tailWord_307644) baseStart_307644 baseEnd_307644 := by
    simpa [prefixWord, tailWord_307644, baseEnd_307644] using wordTrace_append hprefix tailTrace_307644
  have hstable : (prefixWord ++ tailWord_307644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307644).length < 2 ^ (prefixWord ++ tailWord_307644).sum := by decide
  have hdescent : baseEnd_307644 < baseStart_307644 := by decide
  rcases family_descends (prefixWord ++ tailWord_307644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307692 : List Nat := [2, 2, 1, 1, 2, 1, 6, 3, 3]
def baseStart_307692 : Nat := 118140960795 + 307692 * 2 ^ 59
def prefixEnd_307692 : Nat := 4983230072969 + 3 ^ 40 * 307692 * 2
def baseEnd_307692 : Nat := 70219506463695727704425

theorem tailTrace_307692 : CollatzResearch.WordTrace tailWord_307692 prefixEnd_307692 70219506463695727704425 := by
  unfold tailWord_307692
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611224600645954227510665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7481632800861272303347553 5611224600645954227510665)
  ·
    refine ⟨4208418450484465670632999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5611224600645954227510665 4208418450484465670632999)
    ·
      refine ⟨6312627675726698505949499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208418450484465670632999 6312627675726698505949499)
      ·
        refine ⟨9468941513590047758924249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6312627675726698505949499 9468941513590047758924249)
        ·
          refine ⟨7101706135192535819193187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9468941513590047758924249 7101706135192535819193187)
          ·
            refine ⟨10652559202788803728789781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7101706135192535819193187 10652559202788803728789781)
            ·
              refine ⟨499338712630725174787021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10652559202788803728789781 499338712630725174787021)
              ·
                refine ⟨187252017236521940545133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499338712630725174787021 187252017236521940545133)
                ·
                  refine ⟨70219506463695727704425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187252017236521940545133 70219506463695727704425)
                  ·
                    rfl

theorem cell21_307692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_307692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307692 prefixEnd_307692 := by exact prefixLift 307692
  have htrace : WordTrace (prefixWord ++ tailWord_307692) baseStart_307692 baseEnd_307692 := by
    simpa [prefixWord, tailWord_307692, baseEnd_307692] using wordTrace_append hprefix tailTrace_307692
  have hstable : (prefixWord ++ tailWord_307692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307692).length < 2 ^ (prefixWord ++ tailWord_307692).sum := by decide
  have hdescent : baseEnd_307692 < baseStart_307692 := by decide
  rcases family_descends (prefixWord ++ tailWord_307692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307723 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 4]
def baseStart_307723 : Nat := 118140960795 + 307723 * 2 ^ 59
def prefixEnd_307723 : Nat := 4983230072969 + 3 ^ 40 * 307723 * 2
def baseEnd_307723 : Nat := 70226581086046562687695

theorem tailTrace_307723 : CollatzResearch.WordTrace tailWord_307723 prefixEnd_307723 70226581086046562687695 := by
  unfold tailWord_307723
  simp only [CollatzResearch.WordTrace]
  refine ⟨11223579864179600749399823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7482386576119733832933215 11223579864179600749399823)
  ·
    refine ⟨16835369796269401124099735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11223579864179600749399823 16835369796269401124099735)
    ·
      refine ⟨25253054694404101686149603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16835369796269401124099735 25253054694404101686149603)
      ·
        refine ⟨37879582041606152529224405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25253054694404101686149603 37879582041606152529224405)
        ·
          refine ⟨887802704100144199903697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37879582041606152529224405 887802704100144199903697)
          ·
            refine ⟨665852028075108149927773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887802704100144199903697 665852028075108149927773)
            ·
              refine ⟨249694510528165556222915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 665852028075108149927773 249694510528165556222915)
              ·
                refine ⟨374541765792248334334373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249694510528165556222915 374541765792248334334373)
                ·
                  refine ⟨70226581086046562687695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374541765792248334334373 70226581086046562687695)
                  ·
                    rfl

theorem cell21_307723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 4].length) (baseStart_307723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307723 prefixEnd_307723 := by exact prefixLift 307723
  have htrace : WordTrace (prefixWord ++ tailWord_307723) baseStart_307723 baseEnd_307723 := by
    simpa [prefixWord, tailWord_307723, baseEnd_307723] using wordTrace_append hprefix tailTrace_307723
  have hstable : (prefixWord ++ tailWord_307723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307723).length < 2 ^ (prefixWord ++ tailWord_307723).sum := by decide
  have hdescent : baseEnd_307723 < baseStart_307723 := by decide
  rcases family_descends (prefixWord ++ tailWord_307723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307765 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 6]
def baseStart_307765 : Nat := 118140960795 + 307765 * 2 ^ 59
def prefixEnd_307765 : Nat := 4983230072969 + 3 ^ 40 * 307765 * 2
def baseEnd_307765 : Nat := 70236166058263822987609

theorem tailTrace_307765 : CollatzResearch.WordTrace tailWord_307765 prefixEnd_307765 70236166058263822987609 := by
  unfold tailWord_307765
  simp only [CollatzResearch.WordTrace]
  refine ⟨11225111730027441922428749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7483407820018294614952499 11225111730027441922428749)
  ·
    refine ⟨4209416898760290720910781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11225111730027441922428749 4209416898760290720910781)
    ·
      refine ⟨1578531337035109020341543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4209416898760290720910781 1578531337035109020341543)
      ·
        refine ⟨2367797005552663530512315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578531337035109020341543 2367797005552663530512315)
        ·
          refine ⟨3551695508328995295768473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367797005552663530512315 3551695508328995295768473)
          ·
            refine ⟨2663771631246746471826355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3551695508328995295768473 2663771631246746471826355)
            ·
              refine ⟨3995657446870119707739533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663771631246746471826355 3995657446870119707739533)
              ·
                refine ⟨1498371542576294890402325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3995657446870119707739533 1498371542576294890402325)
                ·
                  refine ⟨70236166058263822987609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1498371542576294890402325 70236166058263822987609)
                  ·
                    rfl

theorem cell21_307765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_307765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307765 prefixEnd_307765 := by exact prefixLift 307765
  have htrace : WordTrace (prefixWord ++ tailWord_307765) baseStart_307765 baseEnd_307765 := by
    simpa [prefixWord, tailWord_307765, baseEnd_307765] using wordTrace_append hprefix tailTrace_307765
  have hstable : (prefixWord ++ tailWord_307765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307765).length < 2 ^ (prefixWord ++ tailWord_307765).sum := by decide
  have hdescent : baseEnd_307765 < baseStart_307765 := by decide
  rcases family_descends (prefixWord ++ tailWord_307765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307774 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_307774 : Nat := 118140960795 + 307774 * 2 ^ 59
def prefixEnd_307774 : Nat := 4983230072969 + 3 ^ 40 * 307774 * 2
def baseEnd_307774 : Nat := 70238219980881807337591

theorem tailTrace_307774 : CollatzResearch.WordTrace tailWord_307774 prefixEnd_307774 70238219980881807337591 := by
  unfold tailWord_307774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403179998374354557438297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7483626657996557639670917 1403179998374354557438297)
  ·
    refine ⟨1052384998780765918078723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1403179998374354557438297 1052384998780765918078723)
    ·
      refine ⟨1578577498171148877118085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1052384998780765918078723 1578577498171148877118085)
      ·
        refine ⟨295983280907090414459641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1578577498171148877118085 295983280907090414459641)
        ·
          refine ⟨221987460680317810844731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295983280907090414459641 221987460680317810844731)
          ·
            refine ⟨332981191020476716267097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221987460680317810844731 332981191020476716267097)
            ·
              refine ⟨249735893265357537200323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332981191020476716267097 249735893265357537200323)
              ·
                refine ⟨374603839898036305800485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249735893265357537200323 374603839898036305800485)
                ·
                  refine ⟨70238219980881807337591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374603839898036305800485 70238219980881807337591)
                  ·
                    rfl

theorem cell21_307774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_307774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307774 prefixEnd_307774 := by exact prefixLift 307774
  have htrace : WordTrace (prefixWord ++ tailWord_307774) baseStart_307774 baseEnd_307774 := by
    simpa [prefixWord, tailWord_307774, baseEnd_307774] using wordTrace_append hprefix tailTrace_307774
  have hstable : (prefixWord ++ tailWord_307774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307774).length < 2 ^ (prefixWord ++ tailWord_307774).sum := by decide
  have hdescent : baseEnd_307774 < baseStart_307774 := by decide
  rcases family_descends (prefixWord ++ tailWord_307774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307796 : List Nat := [2, 4, 1, 1, 1, 3, 2, 7]
def baseStart_307796 : Nat := 118140960795 + 307796 * 2 ^ 59
def prefixEnd_307796 : Nat := 4983230072969 + 3 ^ 40 * 307796 * 2
def baseEnd_307796 : Nat := 23414413560204885990293

theorem tailTrace_307796 : CollatzResearch.WordTrace tailWord_307796 prefixEnd_307796 23414413560204885990293 := by
  unfold tailWord_307796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613121196457567108403621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7484161595276756144538161 5613121196457567108403621)
  ·
    refine ⟨1052460224335793832825679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5613121196457567108403621 1052460224335793832825679)
    ·
      refine ⟨1578690336503690749238519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1052460224335793832825679 1578690336503690749238519)
      ·
        refine ⟨2368035504755536123857779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578690336503690749238519 2368035504755536123857779)
        ·
          refine ⟨3552053257133304185786669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2368035504755536123857779 3552053257133304185786669)
          ·
            refine ⟨1332019971424989069670001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3552053257133304185786669 1332019971424989069670001)
            ·
              refine ⟨999014978568741802252501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1332019971424989069670001 999014978568741802252501)
              ·
                refine ⟨23414413560204885990293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 999014978568741802252501 23414413560204885990293)
                ·
                  rfl

theorem cell21_307796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_307796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307796 prefixEnd_307796 := by exact prefixLift 307796
  have htrace : WordTrace (prefixWord ++ tailWord_307796) baseStart_307796 baseEnd_307796 := by
    simpa [prefixWord, tailWord_307796, baseEnd_307796] using wordTrace_append hprefix tailTrace_307796
  have hstable : (prefixWord ++ tailWord_307796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307796).length < 2 ^ (prefixWord ++ tailWord_307796).sum := by decide
  have hdescent : baseEnd_307796 < baseStart_307796 := by decide
  rcases family_descends (prefixWord ++ tailWord_307796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307830 : List Nat := [5, 1, 1, 2, 3, 2, 1, 6]
def baseStart_307830 : Nat := 118140960795 + 307830 * 2 ^ 59
def prefixEnd_307830 : Nat := 4983230072969 + 3 ^ 40 * 307830 * 2
def baseEnd_307830 : Nat := 23416999981279384801381

theorem tailTrace_307830 : CollatzResearch.WordTrace tailWord_307830 prefixEnd_307830 23416999981279384801381 := by
  unfold tailWord_307830
  simp only [CollatzResearch.WordTrace]
  refine ⟨701717654674497376471559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7484988316527972015696629 701717654674497376471559)
  ·
    refine ⟨1052576482011746064707339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 701717654674497376471559 1052576482011746064707339)
    ·
      refine ⟨1578864723017619097061009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1052576482011746064707339 1578864723017619097061009)
      ·
        refine ⟨1184148542263214322795757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1578864723017619097061009 1184148542263214322795757)
        ·
          refine ⟨444055703348705371048409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1184148542263214322795757 444055703348705371048409)
          ·
            refine ⟨333041777511529028286307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444055703348705371048409 333041777511529028286307)
            ·
              refine ⟨499562666267293542429461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333041777511529028286307 499562666267293542429461)
              ·
                refine ⟨23416999981279384801381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 499562666267293542429461 23416999981279384801381)
                ·
                  rfl

theorem cell21_307830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_307830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307830 prefixEnd_307830 := by exact prefixLift 307830
  have htrace : WordTrace (prefixWord ++ tailWord_307830) baseStart_307830 baseEnd_307830 := by
    simpa [prefixWord, tailWord_307830, baseEnd_307830] using wordTrace_append hprefix tailTrace_307830
  have hstable : (prefixWord ++ tailWord_307830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307830).length < 2 ^ (prefixWord ++ tailWord_307830).sum := by decide
  have hdescent : baseEnd_307830 < baseStart_307830 := by decide
  rcases family_descends (prefixWord ++ tailWord_307830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307872 : List Nat := [2, 1, 1, 4, 4, 1, 8]
def baseStart_307872 : Nat := 118140960795 + 307872 * 2 ^ 59
def prefixEnd_307872 : Nat := 4983230072969 + 3 ^ 40 * 307872 * 2
def baseEnd_307872 : Nat := 7806731657339490522673

theorem tailTrace_307872 : CollatzResearch.WordTrace tailWord_307872 prefixEnd_307872 7806731657339490522673 := by
  unfold tailWord_307872
  simp only [CollatzResearch.WordTrace]
  refine ⟨5614507170319899598286935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7486009560426532797715913 5614507170319899598286935)
  ·
    refine ⟨8421760755479849397430403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5614507170319899598286935 8421760755479849397430403)
    ·
      refine ⟨12632641133219774096145605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8421760755479849397430403 12632641133219774096145605)
      ·
        refine ⟨2368620212478707643027301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12632641133219774096145605 2368620212478707643027301)
        ·
          refine ⟨444116289839757683067619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2368620212478707643027301 444116289839757683067619)
          ·
            refine ⟨666174434759636524601429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444116289839757683067619 666174434759636524601429)
            ·
              refine ⟨7806731657339490522673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 666174434759636524601429 7806731657339490522673)
              ·
                rfl

theorem cell21_307872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 8].length) (baseStart_307872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307872 prefixEnd_307872 := by exact prefixLift 307872
  have htrace : WordTrace (prefixWord ++ tailWord_307872) baseStart_307872 baseEnd_307872 := by
    simpa [prefixWord, tailWord_307872, baseEnd_307872] using wordTrace_append hprefix tailTrace_307872
  have hstable : (prefixWord ++ tailWord_307872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307872).length < 2 ^ (prefixWord ++ tailWord_307872).sum := by decide
  have hdescent : baseEnd_307872 < baseStart_307872 := by decide
  rcases family_descends (prefixWord ++ tailWord_307872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307937 : List Nat := [1, 2, 3, 1, 4, 2, 3, 2, 3]
def baseStart_307937 : Nat := 118140960795 + 307937 * 2 ^ 59
def prefixEnd_307937 : Nat := 4983230072969 + 3 ^ 40 * 307937 * 2
def baseEnd_307937 : Nat := 70275418801629746120591

theorem tailTrace_307937 : CollatzResearch.WordTrace tailWord_307937 prefixEnd_307937 70275418801629746120591 := by
  unfold tailWord_307937
  simp only [CollatzResearch.WordTrace]
  refine ⟨11231385085404315297690065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7487590056936210198460043 11231385085404315297690065)
  ·
    refine ⟨8423538814053236473267549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11231385085404315297690065 8423538814053236473267549)
    ·
      refine ⟨3158827055269963677475331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8423538814053236473267549 3158827055269963677475331)
      ·
        refine ⟨4738240582904945516212997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3158827055269963677475331 4738240582904945516212997)
        ·
          refine ⟨888420109294677284289937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4738240582904945516212997 888420109294677284289937)
          ·
            refine ⟨666315081971007963217453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 888420109294677284289937 666315081971007963217453)
            ·
              refine ⟨249868155739127986206545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 666315081971007963217453 249868155739127986206545)
              ·
                refine ⟨187401116804345989654909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249868155739127986206545 187401116804345989654909)
                ·
                  refine ⟨70275418801629746120591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187401116804345989654909 70275418801629746120591)
                  ·
                    rfl

theorem cell21_307937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_307937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307937 prefixEnd_307937 := by exact prefixLift 307937
  have htrace : WordTrace (prefixWord ++ tailWord_307937) baseStart_307937 baseEnd_307937 := by
    simpa [prefixWord, tailWord_307937, baseEnd_307937] using wordTrace_append hprefix tailTrace_307937
  have hstable : (prefixWord ++ tailWord_307937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307937).length < 2 ^ (prefixWord ++ tailWord_307937).sum := by decide
  have hdescent : baseEnd_307937 < baseStart_307937 := by decide
  rcases family_descends (prefixWord ++ tailWord_307937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307951 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 4]
def baseStart_307951 : Nat := 118140960795 + 307951 * 2 ^ 59
def prefixEnd_307951 : Nat := 4983230072969 + 3 ^ 40 * 307951 * 2
def baseEnd_307951 : Nat := 70278613792368832887229

theorem tailTrace_307951 : CollatzResearch.WordTrace tailWord_307951 prefixEnd_307951 70278613792368832887229 := by
  unfold tailWord_307951
  simp only [CollatzResearch.WordTrace]
  refine ⟨11231895707353595688699707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7487930471569063792466471 11231895707353595688699707)
  ·
    refine ⟨16847843561030393533049561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11231895707353595688699707 16847843561030393533049561)
    ·
      refine ⟨12635882670772795149787171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16847843561030393533049561 12635882670772795149787171)
      ·
        refine ⟨18953824006159192724680757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12635882670772795149787171 18953824006159192724680757)
        ·
          refine ⟨1776921000577424317938821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18953824006159192724680757 1776921000577424317938821)
          ·
            refine ⟨333172687608267059613529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1776921000577424317938821 333172687608267059613529)
            ·
              refine ⟨249879515706200294710147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333172687608267059613529 249879515706200294710147)
              ·
                refine ⟨374819273559300442065221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249879515706200294710147 374819273559300442065221)
                ·
                  refine ⟨70278613792368832887229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374819273559300442065221 70278613792368832887229)
                  ·
                    rfl

theorem cell21_307951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 4].length) (baseStart_307951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307951 prefixEnd_307951 := by exact prefixLift 307951
  have htrace : WordTrace (prefixWord ++ tailWord_307951) baseStart_307951 baseEnd_307951 := by
    simpa [prefixWord, tailWord_307951, baseEnd_307951] using wordTrace_append hprefix tailTrace_307951
  have hstable : (prefixWord ++ tailWord_307951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307951).length < 2 ^ (prefixWord ++ tailWord_307951).sum := by decide
  have hdescent : baseEnd_307951 < baseStart_307951 := by decide
  rcases family_descends (prefixWord ++ tailWord_307951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307962 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_307962 : Nat := 118140960795 + 307962 * 2 ^ 59
def prefixEnd_307962 : Nat := 4983230072969 + 3 ^ 40 * 307962 * 2
def baseEnd_307962 : Nat := 70281124142235258203873

theorem tailTrace_307962 : CollatzResearch.WordTrace tailWord_307962 prefixEnd_307962 70281124142235258203873 := by
  unfold tailWord_307962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808074227578436141837535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7488197940209163044900093 2808074227578436141837535)
  ·
    refine ⟨4212111341367654212756303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2808074227578436141837535 4212111341367654212756303)
    ·
      refine ⟨6318167012051481319134455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212111341367654212756303 6318167012051481319134455)
      ·
        refine ⟨9477250518077221978701683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6318167012051481319134455 9477250518077221978701683)
        ·
          refine ⟨14215875777115832968052525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9477250518077221978701683 14215875777115832968052525)
          ·
            refine ⟨5330953416418437363019697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14215875777115832968052525 5330953416418437363019697)
            ·
              refine ⟨3998215062313828022264773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5330953416418437363019697 3998215062313828022264773)
              ·
                refine ⟨749665324183842754174645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3998215062313828022264773 749665324183842754174645)
                ·
                  refine ⟨70281124142235258203873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 749665324183842754174645 70281124142235258203873)
                  ·
                    rfl

theorem cell21_307962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_307962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307962 prefixEnd_307962 := by exact prefixLift 307962
  have htrace : WordTrace (prefixWord ++ tailWord_307962) baseStart_307962 baseEnd_307962 := by
    simpa [prefixWord, tailWord_307962, baseEnd_307962] using wordTrace_append hprefix tailTrace_307962
  have hstable : (prefixWord ++ tailWord_307962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307962).length < 2 ^ (prefixWord ++ tailWord_307962).sum := by decide
  have hdescent : baseEnd_307962 < baseStart_307962 := by decide
  rcases family_descends (prefixWord ++ tailWord_307962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307979 : List Nat := [1, 1, 1, 1, 5, 1, 1, 7, 3]
def baseStart_307979 : Nat := 118140960795 + 307979 * 2 ^ 59
def prefixEnd_307979 : Nat := 4983230072969 + 3 ^ 40 * 307979 * 2
def baseEnd_307979 : Nat := 70285003773847006420505

theorem tailTrace_307979 : CollatzResearch.WordTrace tailWord_307979 prefixEnd_307979 70285003773847006420505 := by
  unfold tailWord_307979
  simp only [CollatzResearch.WordTrace]
  refine ⟨11232916951252156470718991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7488611300834770980479327 11232916951252156470718991)
  ·
    refine ⟨16849375426878234706078487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11232916951252156470718991 16849375426878234706078487)
    ·
      refine ⟨25274063140317352059117731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16849375426878234706078487 25274063140317352059117731)
      ·
        refine ⟨37911094710476028088676597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25274063140317352059117731 37911094710476028088676597)
        ·
          refine ⟨3554165129107127633313431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37911094710476028088676597 3554165129107127633313431)
          ·
            refine ⟨5331247693660691449970147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3554165129107127633313431 5331247693660691449970147)
            ·
              refine ⟨7996871540491037174955221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5331247693660691449970147 7996871540491037174955221)
              ·
                refine ⟨187426676730258683788013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7996871540491037174955221 187426676730258683788013)
                ·
                  refine ⟨70285003773847006420505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187426676730258683788013 70285003773847006420505)
                  ·
                    rfl

theorem cell21_307979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 3].length) (baseStart_307979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307979 prefixEnd_307979 := by exact prefixLift 307979
  have htrace : WordTrace (prefixWord ++ tailWord_307979) baseStart_307979 baseEnd_307979 := by
    simpa [prefixWord, tailWord_307979, baseEnd_307979] using wordTrace_append hprefix tailTrace_307979
  have hstable : (prefixWord ++ tailWord_307979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307979).length < 2 ^ (prefixWord ++ tailWord_307979).sum := by decide
  have hdescent : baseEnd_307979 < baseStart_307979 := by decide
  rcases family_descends (prefixWord ++ tailWord_307979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307996 : List Nat := [2, 2, 3, 1, 1, 4, 1, 4, 3]
def baseStart_307996 : Nat := 118140960795 + 307996 * 2 ^ 59
def prefixEnd_307996 : Nat := 4983230072969 + 3 ^ 40 * 307996 * 2
def baseEnd_307996 : Nat := 70288883405458754637137

theorem tailTrace_307996 : CollatzResearch.WordTrace tailWord_307996 prefixEnd_307996 70288883405458754637137 := by
  unfold tailWord_307996
  simp only [CollatzResearch.WordTrace]
  refine ⟨5616768496095284187043921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7489024661460378916058561 5616768496095284187043921)
  ·
    refine ⟨4212576372071463140282941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5616768496095284187043921 4212576372071463140282941)
    ·
      refine ⟨1579716139526798677606103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4212576372071463140282941 1579716139526798677606103)
      ·
        refine ⟨2369574209290198016409155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579716139526798677606103 2369574209290198016409155)
        ·
          refine ⟨3554361313935297024613733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2369574209290198016409155 3554361313935297024613733)
          ·
            refine ⟨666442746362868192115075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3554361313935297024613733 666442746362868192115075)
            ·
              refine ⟨999664119544302288172613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666442746362868192115075 999664119544302288172613)
              ·
                refine ⟨187437022414556679032365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 999664119544302288172613 187437022414556679032365)
                ·
                  refine ⟨70288883405458754637137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187437022414556679032365 70288883405458754637137)
                  ·
                    rfl

theorem cell21_307996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_307996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_307996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_307996 prefixEnd_307996 := by exact prefixLift 307996
  have htrace : WordTrace (prefixWord ++ tailWord_307996) baseStart_307996 baseEnd_307996 := by
    simpa [prefixWord, tailWord_307996, baseEnd_307996] using wordTrace_append hprefix tailTrace_307996
  have hstable : (prefixWord ++ tailWord_307996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307996).length < 2 ^ (prefixWord ++ tailWord_307996).sum := by decide
  have hdescent : baseEnd_307996 < baseStart_307996 := by decide
  rcases family_descends (prefixWord ++ tailWord_307996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308013 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 5]
def baseStart_308013 : Nat := 118140960795 + 308013 * 2 ^ 59
def prefixEnd_308013 : Nat := 4983230072969 + 3 ^ 40 * 308013 * 2
def baseEnd_308013 : Nat := 70292763037070502853769

theorem tailTrace_308013 : CollatzResearch.WordTrace tailWord_308013 prefixEnd_308013 70292763037070502853769 := by
  unfold tailWord_308013
  simp only [CollatzResearch.WordTrace]
  refine ⟨11234157033128980277456693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7489438022085986851637795 11234157033128980277456693)
  ·
    refine ⟨1053202221855841901011565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11234157033128980277456693 1053202221855841901011565)
    ·
      refine ⟨394950833195940712879337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1053202221855841901011565 394950833195940712879337)
      ·
        refine ⟨296213124896955534659503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394950833195940712879337 296213124896955534659503)
        ·
          refine ⟨444319687345433301989255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296213124896955534659503 444319687345433301989255)
          ·
            refine ⟨666479531018149952983883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444319687345433301989255 666479531018149952983883)
            ·
              refine ⟨999719296527224929475825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666479531018149952983883 999719296527224929475825)
              ·
                refine ⟨749789472395418697106869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999719296527224929475825 749789472395418697106869)
                ·
                  refine ⟨70292763037070502853769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 749789472395418697106869 70292763037070502853769)
                  ·
                    rfl

theorem cell21_308013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_308013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308013 prefixEnd_308013 := by exact prefixLift 308013
  have htrace : WordTrace (prefixWord ++ tailWord_308013) baseStart_308013 baseEnd_308013 := by
    simpa [prefixWord, tailWord_308013, baseEnd_308013] using wordTrace_append hprefix tailTrace_308013
  have hstable : (prefixWord ++ tailWord_308013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308013).length < 2 ^ (prefixWord ++ tailWord_308013).sum := by decide
  have hdescent : baseEnd_308013 < baseStart_308013 := by decide
  rcases family_descends (prefixWord ++ tailWord_308013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308024 : List Nat := [2, 1, 2, 1, 3, 2, 5, 5]
def baseStart_308024 : Nat := 118140960795 + 308024 * 2 ^ 59
def prefixEnd_308024 : Nat := 4983230072969 + 3 ^ 40 * 308024 * 2
def baseEnd_308024 : Nat := 23431757795645642723471

theorem tailTrace_308024 : CollatzResearch.WordTrace tailWord_308024 prefixEnd_308024 23431757795645642723471 := by
  unfold tailWord_308024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5617279118044564578053563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7489705490726086104071417 5617279118044564578053563)
  ·
    refine ⟨8425918677066846867080345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5617279118044564578053563 8425918677066846867080345)
    ·
      refine ⟨6319439007800135150310259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8425918677066846867080345 6319439007800135150310259)
      ·
        refine ⟨9479158511700202725465389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6319439007800135150310259 9479158511700202725465389)
        ·
          refine ⟨3554684441887576022049521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9479158511700202725465389 3554684441887576022049521)
          ·
            refine ⟨2666013331415682016537141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3554684441887576022049521 2666013331415682016537141)
            ·
              refine ⟨249938749820220189050357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2666013331415682016537141 249938749820220189050357)
              ·
                refine ⟨23431757795645642723471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 249938749820220189050357 23431757795645642723471)
                ·
                  rfl

theorem cell21_308024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_308024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308024 prefixEnd_308024 := by exact prefixLift 308024
  have htrace : WordTrace (prefixWord ++ tailWord_308024) baseStart_308024 baseEnd_308024 := by
    simpa [prefixWord, tailWord_308024, baseEnd_308024] using wordTrace_append hprefix tailTrace_308024
  have hstable : (prefixWord ++ tailWord_308024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308024).length < 2 ^ (prefixWord ++ tailWord_308024).sum := by decide
  have hdescent : baseEnd_308024 < baseStart_308024 := by decide
  rcases family_descends (prefixWord ++ tailWord_308024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308055 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 5]
def baseStart_308055 : Nat := 118140960795 + 308055 * 2 ^ 59
def prefixEnd_308055 : Nat := 4983230072969 + 3 ^ 40 * 308055 * 2
def baseEnd_308055 : Nat := 70302348009287763153683

theorem tailTrace_308055 : CollatzResearch.WordTrace tailWord_308055 prefixEnd_308055 70302348009287763153683 := by
  unfold tailWord_308055
  simp only [CollatzResearch.WordTrace]
  refine ⟨11235688898976821450485619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7490459265984547633657079 11235688898976821450485619)
  ·
    refine ⟨16853533348465232175728429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11235688898976821450485619 16853533348465232175728429)
    ·
      refine ⟨6320075005674462065898161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16853533348465232175728429 6320075005674462065898161)
      ·
        refine ⟨4740056254255846549423621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6320075005674462065898161 4740056254255846549423621)
        ·
          refine ⟨888760547672971228016929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4740056254255846549423621 888760547672971228016929)
          ·
            refine ⟨666570410754728421012697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 888760547672971228016929 666570410754728421012697)
            ·
              refine ⟨499927808066046315759523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 666570410754728421012697 499927808066046315759523)
              ·
                refine ⟨749891712099069473639285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499927808066046315759523 749891712099069473639285)
                ·
                  refine ⟨70302348009287763153683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 749891712099069473639285 70302348009287763153683)
                  ·
                    rfl

theorem cell21_308055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 5].length) (baseStart_308055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308055 prefixEnd_308055 := by exact prefixLift 308055
  have htrace : WordTrace (prefixWord ++ tailWord_308055) baseStart_308055 baseEnd_308055 := by
    simpa [prefixWord, tailWord_308055, baseEnd_308055] using wordTrace_append hprefix tailTrace_308055
  have hstable : (prefixWord ++ tailWord_308055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308055).length < 2 ^ (prefixWord ++ tailWord_308055).sum := by decide
  have hdescent : baseEnd_308055 < baseStart_308055 := by decide
  rcases family_descends (prefixWord ++ tailWord_308055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308069 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 4]
def baseStart_308069 : Nat := 118140960795 + 308069 * 2 ^ 59
def prefixEnd_308069 : Nat := 4983230072969 + 3 ^ 40 * 308069 * 2
def baseEnd_308069 : Nat := 70305543000026849920321

theorem tailTrace_308069 : CollatzResearch.WordTrace tailWord_308069 prefixEnd_308069 70305543000026849920321 := by
  unfold tailWord_308069
  simp only [CollatzResearch.WordTrace]
  refine ⟨11236199520926101841495261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7490799680617401227663507 11236199520926101841495261)
  ·
    refine ⟨4213574820347288190560723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11236199520926101841495261 4213574820347288190560723)
    ·
      refine ⟨6320362230520932285841085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4213574820347288190560723 6320362230520932285841085)
      ·
        refine ⟨2370135836445349607190407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6320362230520932285841085 2370135836445349607190407)
        ·
          refine ⟨3555203754668024410785611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2370135836445349607190407 3555203754668024410785611)
          ·
            refine ⟨5332805632002036616178417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3555203754668024410785611 5332805632002036616178417)
            ·
              refine ⟨3999604224001527462133813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5332805632002036616178417 3999604224001527462133813)
              ·
                refine ⟨374962896000143199575045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3999604224001527462133813 374962896000143199575045)
                ·
                  refine ⟨70305543000026849920321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 374962896000143199575045 70305543000026849920321)
                  ·
                    rfl

theorem cell21_308069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_308069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308069 prefixEnd_308069 := by exact prefixLift 308069
  have htrace : WordTrace (prefixWord ++ tailWord_308069) baseStart_308069 baseEnd_308069 := by
    simpa [prefixWord, tailWord_308069, baseEnd_308069] using wordTrace_append hprefix tailTrace_308069
  have hstable : (prefixWord ++ tailWord_308069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308069).length < 2 ^ (prefixWord ++ tailWord_308069).sum := by decide
  have hdescent : baseEnd_308069 < baseStart_308069 := by decide
  rcases family_descends (prefixWord ++ tailWord_308069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308086 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_308086 : Nat := 118140960795 + 308086 * 2 ^ 59
def prefixEnd_308086 : Nat := 4983230072969 + 3 ^ 40 * 308086 * 2
def baseEnd_308086 : Nat := 70309422631638598136953

theorem tailTrace_308086 : CollatzResearch.WordTrace tailWord_308086 prefixEnd_308086 70309422631638598136953 := by
  unfold tailWord_308086
  simp only [CollatzResearch.WordTrace]
  refine ⟨702301222616532109054007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7491213041243009163242741 702301222616532109054007)
  ·
    refine ⟨1053451833924798163581011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 702301222616532109054007 1053451833924798163581011)
    ·
      refine ⟨1580177750887197245371517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1053451833924798163581011 1580177750887197245371517)
      ·
        refine ⟨592566656582698967014319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1580177750887197245371517 592566656582698967014319)
        ·
          refine ⟨888849984874048450521479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592566656582698967014319 888849984874048450521479)
          ·
            refine ⟨1333274977311072675782219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888849984874048450521479 1333274977311072675782219)
            ·
              refine ⟨1999912465966609013673329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333274977311072675782219 1999912465966609013673329)
              ·
                refine ⟨1499934349474956760254997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999912465966609013673329 1499934349474956760254997)
                ·
                  refine ⟨70309422631638598136953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1499934349474956760254997 70309422631638598136953)
                  ·
                    rfl

theorem cell21_308086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_308086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308086 prefixEnd_308086 := by exact prefixLift 308086
  have htrace : WordTrace (prefixWord ++ tailWord_308086) baseStart_308086 baseEnd_308086 := by
    simpa [prefixWord, tailWord_308086, baseEnd_308086] using wordTrace_append hprefix tailTrace_308086
  have hstable : (prefixWord ++ tailWord_308086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308086).length < 2 ^ (prefixWord ++ tailWord_308086).sum := by decide
  have hdescent : baseEnd_308086 < baseStart_308086 := by decide
  rcases family_descends (prefixWord ++ tailWord_308086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308207 : List Nat := [1, 1, 2, 1, 4, 3, 1, 5, 3]
def baseStart_308207 : Nat := 118140960795 + 308207 * 2 ^ 59
def prefixEnd_308207 : Nat := 4983230072969 + 3 ^ 40 * 308207 * 2
def baseEnd_308207 : Nat := 70337036480169276620039

theorem tailTrace_308207 : CollatzResearch.WordTrace tailWord_308207 prefixEnd_308207 70337036480169276620039 := by
  unfold tailWord_308207
  simp only [CollatzResearch.WordTrace]
  refine ⟨11241232794426151410018875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7494155196284100940012583 11241232794426151410018875)
  ·
    refine ⟨16861849191639227115028313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11241232794426151410018875 16861849191639227115028313)
    ·
      refine ⟨12646386893729420336271235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16861849191639227115028313 12646386893729420336271235)
      ·
        refine ⟨18969580340594130504406853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12646386893729420336271235 18969580340594130504406853)
        ·
          refine ⟨3556796313861399469576285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18969580340594130504406853 3556796313861399469576285)
          ·
            refine ⟨1333798617698024801091107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3556796313861399469576285 1333798617698024801091107)
            ·
              refine ⟨2000697926547037201636661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333798617698024801091107 2000697926547037201636661)
              ·
                refine ⟨187565430613784737653437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2000697926547037201636661 187565430613784737653437)
                ·
                  refine ⟨70337036480169276620039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187565430613784737653437 70337036480169276620039)
                  ·
                    rfl

theorem cell21_308207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 3].length) (baseStart_308207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308207 prefixEnd_308207 := by exact prefixLift 308207
  have htrace : WordTrace (prefixWord ++ tailWord_308207) baseStart_308207 baseEnd_308207 := by
    simpa [prefixWord, tailWord_308207, baseEnd_308207] using wordTrace_append hprefix tailTrace_308207
  have hstable : (prefixWord ++ tailWord_308207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308207).length < 2 ^ (prefixWord ++ tailWord_308207).sum := by decide
  have hdescent : baseEnd_308207 < baseStart_308207 := by decide
  rcases family_descends (prefixWord ++ tailWord_308207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308213 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 4]
def baseStart_308213 : Nat := 118140960795 + 308213 * 2 ^ 59
def prefixEnd_308213 : Nat := 4983230072969 + 3 ^ 40 * 308213 * 2
def baseEnd_308213 : Nat := 70338405761914599520027

theorem tailTrace_308213 : CollatzResearch.WordTrace tailWord_308213 prefixEnd_308213 70338405761914599520027 := by
  unfold tailWord_308213
  simp only [CollatzResearch.WordTrace]
  refine ⟨11241451632404414434737293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7494301088269609623158195 11241451632404414434737293)
  ·
    refine ⟨4215544362151655413026485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11241451632404414434737293 4215544362151655413026485)
    ·
      refine ⟨395207283951717694971233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4215544362151655413026485 395207283951717694971233)
      ·
        refine ⟨296405462963788271228425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395207283951717694971233 296405462963788271228425)
        ·
          refine ⟨222304097222841203421319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296405462963788271228425 222304097222841203421319)
          ·
            refine ⟨333456145834261805131979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222304097222841203421319 333456145834261805131979)
            ·
              refine ⟨500184218751392707697969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333456145834261805131979 500184218751392707697969)
              ·
                refine ⟨375138164063544530773477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500184218751392707697969 375138164063544530773477)
                ·
                  refine ⟨70338405761914599520027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375138164063544530773477 70338405761914599520027)
                  ·
                    rfl

theorem cell21_308213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_308213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308213 prefixEnd_308213 := by exact prefixLift 308213
  have htrace : WordTrace (prefixWord ++ tailWord_308213) baseStart_308213 baseEnd_308213 := by
    simpa [prefixWord, tailWord_308213, baseEnd_308213] using wordTrace_append hprefix tailTrace_308213
  have hstable : (prefixWord ++ tailWord_308213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308213).length < 2 ^ (prefixWord ++ tailWord_308213).sum := by decide
  have hdescent : baseEnd_308213 < baseStart_308213 := by decide
  rcases family_descends (prefixWord ++ tailWord_308213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308252 : List Nat := [2, 2, 3, 1, 4, 1, 1, 7]
def baseStart_308252 : Nat := 118140960795 + 308252 * 2 ^ 59
def prefixEnd_308252 : Nat := 4983230072969 + 3 ^ 40 * 308252 * 2
def baseEnd_308252 : Nat := 23449102031086399456649

theorem tailTrace_308252 : CollatzResearch.WordTrace tailWord_308252 prefixEnd_308252 23449102031086399456649 := by
  unfold tailWord_308252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621437039631562047703505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7495249386175416063604673 5621437039631562047703505)
  ·
    refine ⟨4216077779723671535777629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5621437039631562047703505 4216077779723671535777629)
    ·
      refine ⟨1581029167396376825916611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4216077779723671535777629 1581029167396376825916611)
      ·
        refine ⟨2371543751094565238874917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1581029167396376825916611 2371543751094565238874917)
        ·
          refine ⟨444664453330230982289047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2371543751094565238874917 444664453330230982289047)
          ·
            refine ⟨666996679995346473433571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444664453330230982289047 666996679995346473433571)
            ·
              refine ⟨1000495019993019710150357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666996679995346473433571 1000495019993019710150357)
              ·
                refine ⟨23449102031086399456649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1000495019993019710150357 23449102031086399456649)
                ·
                  rfl

theorem cell21_308252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_308252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308252 prefixEnd_308252 := by exact prefixLift 308252
  have htrace : WordTrace (prefixWord ++ tailWord_308252) baseStart_308252 baseEnd_308252 := by
    simpa [prefixWord, tailWord_308252, baseEnd_308252] using wordTrace_append hprefix tailTrace_308252
  have hstable : (prefixWord ++ tailWord_308252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308252).length < 2 ^ (prefixWord ++ tailWord_308252).sum := by decide
  have hdescent : baseEnd_308252 < baseStart_308252 := by decide
  rcases family_descends (prefixWord ++ tailWord_308252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308328 : List Nat := [2, 1, 4, 4, 1, 9]
def baseStart_308328 : Nat := 118140960795 + 308328 * 2 ^ 59
def prefixEnd_308328 : Nat := 4983230072969 + 3 ^ 40 * 308328 * 2
def baseEnd_308328 : Nat := 2606098160322220559375

theorem tailTrace_308328 : CollatzResearch.WordTrace tailWord_308328 prefixEnd_308328 2606098160322220559375 := by
  unfold tailWord_308328
  simp only [CollatzResearch.WordTrace]
  refine ⟨5622823013493894537586819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7497097351325192716782425 5622823013493894537586819)
  ·
    refine ⟨8434234520240841806380229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5622823013493894537586819 8434234520240841806380229)
    ·
      refine ⟨1581418972545157838696293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8434234520240841806380229 1581418972545157838696293)
      ·
        refine ⟨296516057352217094755555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1581418972545157838696293 296516057352217094755555)
        ·
          refine ⟨444774086028325642133333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296516057352217094755555 444774086028325642133333)
          ·
            refine ⟨2606098160322220559375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 444774086028325642133333 2606098160322220559375)
            ·
              rfl

theorem cell21_308328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 9].length) (baseStart_308328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308328 prefixEnd_308328 := by exact prefixLift 308328
  have htrace : WordTrace (prefixWord ++ tailWord_308328) baseStart_308328 baseEnd_308328 := by
    simpa [prefixWord, tailWord_308328, baseEnd_308328] using wordTrace_append hprefix tailTrace_308328
  have hstable : (prefixWord ++ tailWord_308328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308328).length < 2 ^ (prefixWord ++ tailWord_308328).sum := by decide
  have hdescent : baseEnd_308328 < baseStart_308328 := by decide
  rcases family_descends (prefixWord ++ tailWord_308328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308345 : List Nat := [1, 2, 1, 3, 6, 1, 1, 6]
def baseStart_308345 : Nat := 118140960795 + 308345 * 2 ^ 59
def prefixEnd_308345 : Nat := 4983230072969 + 3 ^ 40 * 308345 * 2
def baseEnd_308345 : Nat := 23456176653437234439919

theorem tailTrace_308345 : CollatzResearch.WordTrace tailWord_308345 prefixEnd_308345 23456176653437234439919 := by
  unfold tailWord_308345
  simp only [CollatzResearch.WordTrace]
  refine ⟨11246266067926200978542489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7497510711950800652361659 11246266067926200978542489)
  ·
    refine ⟨8434699550944650733906867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11246266067926200978542489 8434699550944650733906867)
    ·
      refine ⟨12652049326416976100860301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8434699550944650733906867 12652049326416976100860301)
      ·
        refine ⟨4744518497406366037822613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12652049326416976100860301 4744518497406366037822613)
        ·
          refine ⟨222399304565923408022935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4744518497406366037822613 222399304565923408022935)
          ·
            refine ⟨333598956848885112034403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222399304565923408022935 333598956848885112034403)
            ·
              refine ⟨500398435273327668051605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333598956848885112034403 500398435273327668051605)
              ·
                refine ⟨23456176653437234439919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 500398435273327668051605 23456176653437234439919)
                ·
                  rfl

theorem cell21_308345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 6].length) (baseStart_308345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308345 prefixEnd_308345 := by exact prefixLift 308345
  have htrace : WordTrace (prefixWord ++ tailWord_308345) baseStart_308345 baseEnd_308345 := by
    simpa [prefixWord, tailWord_308345, baseEnd_308345] using wordTrace_append hprefix tailTrace_308345
  have hstable : (prefixWord ++ tailWord_308345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308345).length < 2 ^ (prefixWord ++ tailWord_308345).sum := by decide
  have hdescent : baseEnd_308345 < baseStart_308345 := by decide
  rcases family_descends (prefixWord ++ tailWord_308345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308376 : List Nat := [2, 1, 2, 4, 2, 2, 2, 3, 3]
def baseStart_308376 : Nat := 118140960795 + 308376 * 2 ^ 59
def prefixEnd_308376 : Nat := 4983230072969 + 3 ^ 40 * 308376 * 2
def baseEnd_308376 : Nat := 70375604582662538303027

theorem tailTrace_308376 : CollatzResearch.WordTrace tailWord_308376 prefixEnd_308376 70375604582662538303027 := by
  unfold tailWord_308376
  simp only [CollatzResearch.WordTrace]
  refine ⟨5623698365406946636460491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7498264487209262181947321 5623698365406946636460491)
  ·
    refine ⟨8435547548110419954690737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5623698365406946636460491 8435547548110419954690737)
    ·
      refine ⟨6326660661082814966018053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8435547548110419954690737 6326660661082814966018053)
      ·
        refine ⟨1186248873953027806128385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6326660661082814966018053 1186248873953027806128385)
        ·
          refine ⟨889686655464770854596289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186248873953027806128385 889686655464770854596289)
          ·
            refine ⟨667264991598578140947217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889686655464770854596289 667264991598578140947217)
            ·
              refine ⟨500448743698933605710413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667264991598578140947217 500448743698933605710413)
              ·
                refine ⟨187668278887100102141405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 500448743698933605710413 187668278887100102141405)
                ·
                  refine ⟨70375604582662538303027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 187668278887100102141405 70375604582662538303027)
                  ·
                    rfl

theorem cell21_308376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_308376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308376 prefixEnd_308376 := by exact prefixLift 308376
  have htrace : WordTrace (prefixWord ++ tailWord_308376) baseStart_308376 baseEnd_308376 := by
    simpa [prefixWord, tailWord_308376, baseEnd_308376] using wordTrace_append hprefix tailTrace_308376
  have hstable : (prefixWord ++ tailWord_308376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308376).length < 2 ^ (prefixWord ++ tailWord_308376).sum := by decide
  have hdescent : baseEnd_308376 < baseStart_308376 := by decide
  rcases family_descends (prefixWord ++ tailWord_308376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308438 : List Nat := [5, 2, 1, 2, 3, 1, 7]
def baseStart_308438 : Nat := 118140960795 + 308438 * 2 ^ 59
def prefixEnd_308438 : Nat := 4983230072969 + 3 ^ 40 * 308438 * 2
def baseEnd_308438 : Nat := 7821083758596023141063

theorem tailTrace_308438 : CollatzResearch.WordTrace tailWord_308438 prefixEnd_308438 7821083758596023141063 := by
  unfold tailWord_308438
  simp only [CollatzResearch.WordTrace]
  refine ⟨703103628536829866354873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7499772037726185241118645 703103628536829866354873)
  ·
    refine ⟨527327721402622399766155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 703103628536829866354873 527327721402622399766155)
    ·
      refine ⟨790991582103933599649233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527327721402622399766155 790991582103933599649233)
      ·
        refine ⟨593243686577950199736925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 790991582103933599649233 593243686577950199736925)
        ·
          refine ⟨222466382466731324901347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 593243686577950199736925 222466382466731324901347)
          ·
            refine ⟨333699573700096987352021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222466382466731324901347 333699573700096987352021)
            ·
              refine ⟨7821083758596023141063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 333699573700096987352021 7821083758596023141063)
              ·
                rfl

theorem cell21_308438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 7].length) (baseStart_308438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308438 prefixEnd_308438 := by exact prefixLift 308438
  have htrace : WordTrace (prefixWord ++ tailWord_308438) baseStart_308438 baseEnd_308438 := by
    simpa [prefixWord, tailWord_308438, baseEnd_308438] using wordTrace_append hprefix tailTrace_308438
  have hstable : (prefixWord ++ tailWord_308438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308438).length < 2 ^ (prefixWord ++ tailWord_308438).sum := by decide
  have hdescent : baseEnd_308438 < baseStart_308438 := by decide
  rcases family_descends (prefixWord ++ tailWord_308438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308466 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_308466 : Nat := 118140960795 + 308466 * 2 ^ 59
def prefixEnd_308466 : Nat := 4983230072969 + 3 ^ 40 * 308466 * 2
def baseEnd_308466 : Nat := 70396143808842381802843

theorem tailTrace_308466 : CollatzResearch.WordTrace tailWord_308466 prefixEnd_308466 70396143808842381802843 := by
  unfold tailWord_308466
  simp only [CollatzResearch.WordTrace]
  refine ⟨2812669825121959660924313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7500452866991892429131501 2812669825121959660924313)
  ·
    refine ⟨2109502368841469745693235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2812669825121959660924313 2109502368841469745693235)
    ·
      refine ⟨3164253553262204618539853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2109502368841469745693235 3164253553262204618539853)
      ·
        refine ⟨1186595082473326731952445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3164253553262204618539853 1186595082473326731952445)
        ·
          refine ⟨444973155927497524482167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1186595082473326731952445 444973155927497524482167)
          ·
            refine ⟨667459733891246286723251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444973155927497524482167 667459733891246286723251)
            ·
              refine ⟨1001189600836869430084877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667459733891246286723251 1001189600836869430084877)
              ·
                refine ⟨375446100313826036281829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001189600836869430084877 375446100313826036281829)
                ·
                  refine ⟨70396143808842381802843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375446100313826036281829 70396143808842381802843)
                  ·
                    rfl

theorem cell21_308466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_308466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308466 prefixEnd_308466 := by exact prefixLift 308466
  have htrace : WordTrace (prefixWord ++ tailWord_308466) baseStart_308466 baseEnd_308466 := by
    simpa [prefixWord, tailWord_308466, baseEnd_308466] using wordTrace_append hprefix tailTrace_308466
  have hstable : (prefixWord ++ tailWord_308466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308466).length < 2 ^ (prefixWord ++ tailWord_308466).sum := by decide
  have hdescent : baseEnd_308466 < baseStart_308466 := by decide
  rcases family_descends (prefixWord ++ tailWord_308466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308508 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_308508 : Nat := 118140960795 + 308508 * 2 ^ 59
def prefixEnd_308508 : Nat := 4983230072969 + 3 ^ 40 * 308508 * 2
def baseEnd_308508 : Nat := 70405728781059642102757

theorem tailTrace_308508 : CollatzResearch.WordTrace tailWord_308508 prefixEnd_308508 70405728781059642102757 := by
  unfold tailWord_308508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5626105583167839908363089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7501474110890453211150785 5626105583167839908363089)
  ·
    refine ⟨4219579187375879931272317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5626105583167839908363089 4219579187375879931272317)
    ·
      refine ⟨1582342195265954974227119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4219579187375879931272317 1582342195265954974227119)
      ·
        refine ⟨2373513292898932461340679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582342195265954974227119 2373513292898932461340679)
        ·
          refine ⟨3560269939348398692011019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373513292898932461340679 3560269939348398692011019)
          ·
            refine ⟨5340404909022598038016529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3560269939348398692011019 5340404909022598038016529)
            ·
              refine ⟨4005303681766948528512397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5340404909022598038016529 4005303681766948528512397)
              ·
                refine ⟨1501988880662605698192149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4005303681766948528512397 1501988880662605698192149)
                ·
                  refine ⟨70405728781059642102757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1501988880662605698192149 70405728781059642102757)
                  ·
                    rfl

theorem cell21_308508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_308508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308508 prefixEnd_308508 := by exact prefixLift 308508
  have htrace : WordTrace (prefixWord ++ tailWord_308508) baseStart_308508 baseEnd_308508 := by
    simpa [prefixWord, tailWord_308508, baseEnd_308508] using wordTrace_append hprefix tailTrace_308508
  have hstable : (prefixWord ++ tailWord_308508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308508).length < 2 ^ (prefixWord ++ tailWord_308508).sum := by decide
  have hdescent : baseEnd_308508 < baseStart_308508 := by decide
  rcases family_descends (prefixWord ++ tailWord_308508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308590 : List Nat := [4, 1, 2, 4, 1, 2, 2, 5]
def baseStart_308590 : Nat := 118140960795 + 308590 * 2 ^ 59
def prefixEnd_308590 : Nat := 4983230072969 + 3 ^ 40 * 308590 * 2
def baseEnd_308590 : Nat := 23474814099415240578641

theorem tailTrace_308590 : CollatzResearch.WordTrace tailWord_308590 prefixEnd_308590 23474814099415240578641 := by
  unfold tailWord_308590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406900244004825977651403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7503467968025738547474149 1406900244004825977651403)
  ·
    refine ⟨2110350366007238966477105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1406900244004825977651403 2110350366007238966477105)
    ·
      refine ⟨1582762774505429224857829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2110350366007238966477105 1582762774505429224857829)
      ·
        refine ⟨296768020219767979660843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1582762774505429224857829 296768020219767979660843)
        ·
          refine ⟨445152030329651969491265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296768020219767979660843 445152030329651969491265)
          ·
            refine ⟨333864022747238977118449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445152030329651969491265 333864022747238977118449)
            ·
              refine ⟨250398017060429232838837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333864022747238977118449 250398017060429232838837)
              ·
                refine ⟨23474814099415240578641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 250398017060429232838837 23474814099415240578641)
                ·
                  rfl

theorem cell21_308590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_308590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308590 prefixEnd_308590 := by exact prefixLift 308590
  have htrace : WordTrace (prefixWord ++ tailWord_308590) baseStart_308590 baseEnd_308590 := by
    simpa [prefixWord, tailWord_308590, baseEnd_308590] using wordTrace_append hprefix tailTrace_308590
  have hstable : (prefixWord ++ tailWord_308590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308590).length < 2 ^ (prefixWord ++ tailWord_308590).sum := by decide
  have hdescent : baseEnd_308590 < baseStart_308590 := by decide
  rcases family_descends (prefixWord ++ tailWord_308590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308615 : List Nat := [1, 1, 4, 2, 2, 4, 7]
def baseStart_308615 : Nat := 118140960795 + 308615 * 2 ^ 59
def prefixEnd_308615 : Nat := 4983230072969 + 3 ^ 40 * 308615 * 2
def baseEnd_308615 : Nat := 7825571959872359313245

theorem tailTrace_308615 : CollatzResearch.WordTrace tailWord_308615 prefixEnd_308615 7825571959872359313245 := by
  unfold tailWord_308615
  simp only [CollatzResearch.WordTrace]
  refine ⟨11256113776948037090871299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7504075851298691393914199 11256113776948037090871299)
  ·
    refine ⟨16884170665422055636306949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11256113776948037090871299 16884170665422055636306949)
    ·
      refine ⟨3165781999766635431807553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16884170665422055636306949 3165781999766635431807553)
      ·
        refine ⟨2374336499824976573855665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3165781999766635431807553 2374336499824976573855665)
        ·
          refine ⟨1780752374868732430391749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2374336499824976573855665 1780752374868732430391749)
          ·
            refine ⟨333891070287887330698453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1780752374868732430391749 333891070287887330698453)
            ·
              refine ⟨7825571959872359313245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 333891070287887330698453 7825571959872359313245)
              ·
                rfl

theorem cell21_308615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 7].length) (baseStart_308615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308615 prefixEnd_308615 := by exact prefixLift 308615
  have htrace : WordTrace (prefixWord ++ tailWord_308615) baseStart_308615 baseEnd_308615 := by
    simpa [prefixWord, tailWord_308615, baseEnd_308615] using wordTrace_append hprefix tailTrace_308615
  have hstable : (prefixWord ++ tailWord_308615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308615).length < 2 ^ (prefixWord ++ tailWord_308615).sum := by decide
  have hdescent : baseEnd_308615 < baseStart_308615 := by decide
  rcases family_descends (prefixWord ++ tailWord_308615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308632 : List Nat := [2, 1, 2, 5, 2, 1, 2, 6]
def baseStart_308632 : Nat := 118140960795 + 308632 * 2 ^ 59
def prefixEnd_308632 : Nat := 4983230072969 + 3 ^ 40 * 308632 * 2
def baseEnd_308632 : Nat := 23478009090154327345279

theorem tailTrace_308632 : CollatzResearch.WordTrace tailWord_308632 prefixEnd_308632 23478009090154327345279 := by
  unfold tailWord_308632
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628366908943224497120075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7504489211924299329493433 5628366908943224497120075)
  ·
    refine ⟨8442550363414836745680113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5628366908943224497120075 8442550363414836745680113)
    ·
      refine ⟨6331912772561127559260085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8442550363414836745680113 6331912772561127559260085)
      ·
        refine ⟨593616822427605708680633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6331912772561127559260085 593616822427605708680633)
        ·
          refine ⟨445212616820704281510475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 593616822427605708680633 445212616820704281510475)
          ·
            refine ⟨667818925231056422265713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445212616820704281510475 667818925231056422265713)
            ·
              refine ⟨500864193923292316699285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667818925231056422265713 500864193923292316699285)
              ·
                refine ⟨23478009090154327345279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 500864193923292316699285 23478009090154327345279)
                ·
                  rfl

theorem cell21_308632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_308632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308632 prefixEnd_308632 := by exact prefixLift 308632
  have htrace : WordTrace (prefixWord ++ tailWord_308632) baseStart_308632 baseEnd_308632 := by
    simpa [prefixWord, tailWord_308632, baseEnd_308632] using wordTrace_append hprefix tailTrace_308632
  have hstable : (prefixWord ++ tailWord_308632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308632).length < 2 ^ (prefixWord ++ tailWord_308632).sum := by decide
  have hdescent : baseEnd_308632 < baseStart_308632 := by decide
  rcases family_descends (prefixWord ++ tailWord_308632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308694 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_308694 : Nat := 118140960795 + 308694 * 2 ^ 59
def prefixEnd_308694 : Nat := 4983230072969 + 3 ^ 40 * 308694 * 2
def baseEnd_308694 : Nat := 70448176515164652002377

theorem tailTrace_308694 : CollatzResearch.WordTrace tailWord_308694 prefixEnd_308694 70448176515164652002377 := by
  unfold tailWord_308694
  simp only [CollatzResearch.WordTrace]
  refine ⟨703687196478864598937321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7505996762441222388664757 703687196478864598937321)
  ·
    refine ⟨527765397359148449202991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 703687196478864598937321 527765397359148449202991)
    ·
      refine ⟨791648096038722673804487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527765397359148449202991 791648096038722673804487)
      ·
        refine ⟨1187472144058084010706731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791648096038722673804487 1187472144058084010706731)
        ·
          refine ⟨1781208216087126016060097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187472144058084010706731 1781208216087126016060097)
          ·
            refine ⟨1335906162065344512045073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1781208216087126016060097 1335906162065344512045073)
            ·
              refine ⟨1001929621549008384033805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1335906162065344512045073 1001929621549008384033805)
              ·
                refine ⟨375723608080878144012677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001929621549008384033805 375723608080878144012677)
                ·
                  refine ⟨70448176515164652002377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375723608080878144012677 70448176515164652002377)
                  ·
                    rfl

theorem cell21_308694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_308694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308694 prefixEnd_308694 := by exact prefixLift 308694
  have htrace : WordTrace (prefixWord ++ tailWord_308694) baseStart_308694 baseEnd_308694 := by
    simpa [prefixWord, tailWord_308694, baseEnd_308694] using wordTrace_append hprefix tailTrace_308694
  have hstable : (prefixWord ++ tailWord_308694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308694).length < 2 ^ (prefixWord ++ tailWord_308694).sum := by decide
  have hdescent : baseEnd_308694 < baseStart_308694 := by decide
  rcases family_descends (prefixWord ++ tailWord_308694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308705 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 7]
def baseStart_308705 : Nat := 118140960795 + 308705 * 2 ^ 59
def prefixEnd_308705 : Nat := 4983230072969 + 3 ^ 40 * 308705 * 2
def baseEnd_308705 : Nat := 70450686865031077319021

theorem tailTrace_308705 : CollatzResearch.WordTrace tailWord_308705 prefixEnd_308705 70450686865031077319021 := by
  unfold tailWord_308705
  simp only [CollatzResearch.WordTrace]
  refine ⟨11259396346621982461647569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7506264231081321641098379 11259396346621982461647569)
  ·
    refine ⟨8444547259966486846235677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11259396346621982461647569 8444547259966486846235677)
    ·
      refine ⟨3166705222487432567338379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8444547259966486846235677 3166705222487432567338379)
      ·
        refine ⟨4750057833731148851007569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166705222487432567338379 4750057833731148851007569)
        ·
          refine ⟨3562543375298361638255677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4750057833731148851007569 3562543375298361638255677)
          ·
            refine ⟨1335953765736885614345879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3562543375298361638255677 1335953765736885614345879)
            ·
              refine ⟨2003930648605328421518819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335953765736885614345879 2003930648605328421518819)
              ·
                refine ⟨3005895972907992632278229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2003930648605328421518819 3005895972907992632278229)
                ·
                  refine ⟨70450686865031077319021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3005895972907992632278229 70450686865031077319021)
                  ·
                    rfl

theorem cell21_308705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_308705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308705 prefixEnd_308705 := by exact prefixLift 308705
  have htrace : WordTrace (prefixWord ++ tailWord_308705) baseStart_308705 baseEnd_308705 := by
    simpa [prefixWord, tailWord_308705, baseEnd_308705] using wordTrace_append hprefix tailTrace_308705
  have hstable : (prefixWord ++ tailWord_308705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308705).length < 2 ^ (prefixWord ++ tailWord_308705).sum := by decide
  have hdescent : baseEnd_308705 < baseStart_308705 := by decide
  rcases family_descends (prefixWord ++ tailWord_308705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308753 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 4]
def baseStart_308753 : Nat := 118140960795 + 308753 * 2 ^ 59
def prefixEnd_308753 : Nat := 4983230072969 + 3 ^ 40 * 308753 * 2
def baseEnd_308753 : Nat := 70461641118993660518923

theorem tailTrace_308753 : CollatzResearch.WordTrace tailWord_308753 prefixEnd_308753 70461641118993660518923 := by
  unfold tailWord_308753
  simp only [CollatzResearch.WordTrace]
  refine ⟨11261147050448086659394913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7507431366965391106263275 11261147050448086659394913)
  ·
    refine ⟨8445860287836064994546185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11261147050448086659394913 8445860287836064994546185)
    ·
      refine ⟨6334395215877048745909639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8445860287836064994546185 6334395215877048745909639)
      ·
        refine ⟨9501592823815573118864459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6334395215877048745909639 9501592823815573118864459)
        ·
          refine ⟨14252389235723359678296689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9501592823815573118864459 14252389235723359678296689)
          ·
            refine ⟨10689291926792519758722517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14252389235723359678296689 10689291926792519758722517)
            ·
              refine ⟨250530279534199681845059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10689291926792519758722517 250530279534199681845059)
              ·
                refine ⟨375795419301299522767589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250530279534199681845059 375795419301299522767589)
                ·
                  refine ⟨70461641118993660518923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375795419301299522767589 70461641118993660518923)
                  ·
                    rfl

theorem cell21_308753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_308753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308753 prefixEnd_308753 := by exact prefixLift 308753
  have htrace : WordTrace (prefixWord ++ tailWord_308753) baseStart_308753 baseEnd_308753 := by
    simpa [prefixWord, tailWord_308753, baseEnd_308753] using wordTrace_append hprefix tailTrace_308753
  have hstable : (prefixWord ++ tailWord_308753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308753).length < 2 ^ (prefixWord ++ tailWord_308753).sum := by decide
  have hdescent : baseEnd_308753 < baseStart_308753 := by decide
  rcases family_descends (prefixWord ++ tailWord_308753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308767 : List Nat := [1, 1, 2, 4, 1, 1, 6, 5]
def baseStart_308767 : Nat := 118140960795 + 308767 * 2 ^ 59
def prefixEnd_308767 : Nat := 4983230072969 + 3 ^ 40 * 308767 * 2
def baseEnd_308767 : Nat := 23488278703244249095187

theorem tailTrace_308767 : CollatzResearch.WordTrace tailWord_308767 prefixEnd_308767 23488278703244249095187 := by
  unfold tailWord_308767
  simp only [CollatzResearch.WordTrace]
  refine ⟨11261657672397367050404555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7507771781598244700269703 11261657672397367050404555)
  ·
    refine ⟨16892486508596050575606833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11261657672397367050404555 16892486508596050575606833)
    ·
      refine ⟨12669364881447037931705125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16892486508596050575606833 12669364881447037931705125)
      ·
        refine ⟨2375505915271319612194711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12669364881447037931705125 2375505915271319612194711)
        ·
          refine ⟨3563258872906979418292067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2375505915271319612194711 3563258872906979418292067)
          ·
            refine ⟨5344888309360469127438101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3563258872906979418292067 5344888309360469127438101)
            ·
              refine ⟨250541639501271990348661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5344888309360469127438101 250541639501271990348661)
              ·
                refine ⟨23488278703244249095187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 250541639501271990348661 23488278703244249095187)
                ·
                  rfl

theorem cell21_308767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 5].length) (baseStart_308767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308767 prefixEnd_308767 := by exact prefixLift 308767
  have htrace : WordTrace (prefixWord ++ tailWord_308767) baseStart_308767 baseEnd_308767 := by
    simpa [prefixWord, tailWord_308767, baseEnd_308767] using wordTrace_append hprefix tailTrace_308767
  have hstable : (prefixWord ++ tailWord_308767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308767).length < 2 ^ (prefixWord ++ tailWord_308767).sum := by decide
  have hdescent : baseEnd_308767 < baseStart_308767 := by decide
  rcases family_descends (prefixWord ++ tailWord_308767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308846 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_308846 : Nat := 118140960795 + 308846 * 2 ^ 59
def prefixEnd_308846 : Nat := 4983230072969 + 3 ^ 40 * 308846 * 2
def baseEnd_308846 : Nat := 70482864986046165468733

theorem tailTrace_308846 : CollatzResearch.WordTrace tailWord_308846 prefixEnd_308846 70482864986046165468733 := by
  unfold tailWord_308846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408067379888895442816299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7509692692740775695020261 1408067379888895442816299)
  ·
    refine ⟨2112101069833343164224449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408067379888895442816299 2112101069833343164224449)
    ·
      refine ⟨1584075802375007373168337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2112101069833343164224449 1584075802375007373168337)
      ·
        refine ⟨1188056851781255529876253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1584075802375007373168337 1188056851781255529876253)
        ·
          refine ⟨445521319417970823703595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1188056851781255529876253 445521319417970823703595)
          ·
            refine ⟨668281979126956235555393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445521319417970823703595 668281979126956235555393)
            ·
              refine ⟨501211484345217176666545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668281979126956235555393 501211484345217176666545)
              ·
                refine ⟨375908613258912882499909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501211484345217176666545 375908613258912882499909)
                ·
                  refine ⟨70482864986046165468733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375908613258912882499909 70482864986046165468733)
                  ·
                    rfl

theorem cell21_308846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_308846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308846 prefixEnd_308846 := by exact prefixLift 308846
  have htrace : WordTrace (prefixWord ++ tailWord_308846) baseStart_308846 baseEnd_308846 := by
    simpa [prefixWord, tailWord_308846, baseEnd_308846] using wordTrace_append hprefix tailTrace_308846
  have hstable : (prefixWord ++ tailWord_308846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308846).length < 2 ^ (prefixWord ++ tailWord_308846).sum := by decide
  have hdescent : baseEnd_308846 < baseStart_308846 := by decide
  rcases family_descends (prefixWord ++ tailWord_308846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308857 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 5]
def baseStart_308857 : Nat := 118140960795 + 308857 * 2 ^ 59
def prefixEnd_308857 : Nat := 4983230072969 + 3 ^ 40 * 308857 * 2
def baseEnd_308857 : Nat := 70485375335912590785377

theorem tailTrace_308857 : CollatzResearch.WordTrace tailWord_308857 prefixEnd_308857 70485375335912590785377 := by
  unfold tailWord_308857
  simp only [CollatzResearch.WordTrace]
  refine ⟨11264940242071312421180825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7509960161380874947453883 11264940242071312421180825)
  ·
    refine ⟨8448705181553484315885619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11264940242071312421180825 8448705181553484315885619)
    ·
      refine ⟨12673057772330226473828429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8448705181553484315885619 12673057772330226473828429)
      ·
        refine ⟨4752396664623834927685661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12673057772330226473828429 4752396664623834927685661)
        ·
          refine ⟨1782148749233938097882123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4752396664623834927685661 1782148749233938097882123)
          ·
            refine ⟨2673223123850907146823185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782148749233938097882123 2673223123850907146823185)
            ·
              refine ⟨2004917342888180360117389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2673223123850907146823185 2004917342888180360117389)
              ·
                refine ⟨751844003583067635044021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2004917342888180360117389 751844003583067635044021)
                ·
                  refine ⟨70485375335912590785377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 751844003583067635044021 70485375335912590785377)
                  ·
                    rfl

theorem cell21_308857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_308857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308857 prefixEnd_308857 := by exact prefixLift 308857
  have htrace : WordTrace (prefixWord ++ tailWord_308857) baseStart_308857 baseEnd_308857 := by
    simpa [prefixWord, tailWord_308857, baseEnd_308857] using wordTrace_append hprefix tailTrace_308857
  have hstable : (prefixWord ++ tailWord_308857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308857).length < 2 ^ (prefixWord ++ tailWord_308857).sum := by decide
  have hdescent : baseEnd_308857 < baseStart_308857 := by decide
  rcases family_descends (prefixWord ++ tailWord_308857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308874 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_308874 : Nat := 118140960795 + 308874 * 2 ^ 59
def prefixEnd_308874 : Nat := 4983230072969 + 3 ^ 40 * 308874 * 2
def baseEnd_308874 : Nat := 70489254967524339002009

theorem tailTrace_308874 : CollatzResearch.WordTrace tailWord_308874 prefixEnd_308874 70489254967524339002009 := by
  unfold tailWord_308874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2816390070752431081137419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7510373522006482883033117 2816390070752431081137419)
  ·
    refine ⟨4224585106128646621706129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2816390070752431081137419 4224585106128646621706129)
    ·
      refine ⟨3168438829596484966279597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4224585106128646621706129 3168438829596484966279597)
      ·
        refine ⟨1188164561098681862354849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3168438829596484966279597 1188164561098681862354849)
        ·
          refine ⟨891123420824011396766137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1188164561098681862354849 891123420824011396766137)
          ·
            refine ⟨668342565618008547574603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891123420824011396766137 668342565618008547574603)
            ·
              refine ⟨1002513848427012821361905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668342565618008547574603 1002513848427012821361905)
              ·
                refine ⟨751885386320259616021429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002513848427012821361905 751885386320259616021429)
                ·
                  refine ⟨70489254967524339002009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 751885386320259616021429 70489254967524339002009)
                  ·
                    rfl

theorem cell21_308874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_308874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308874 prefixEnd_308874 := by exact prefixLift 308874
  have htrace : WordTrace (prefixWord ++ tailWord_308874) baseStart_308874 baseEnd_308874 := by
    simpa [prefixWord, tailWord_308874, baseEnd_308874] using wordTrace_append hprefix tailTrace_308874
  have hstable : (prefixWord ++ tailWord_308874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308874).length < 2 ^ (prefixWord ++ tailWord_308874).sum := by decide
  have hdescent : baseEnd_308874 < baseStart_308874 := by decide
  rcases family_descends (prefixWord ++ tailWord_308874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308964 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_308964 : Nat := 118140960795 + 308964 * 2 ^ 59
def prefixEnd_308964 : Nat := 4983230072969 + 3 ^ 40 * 308964 * 2
def baseEnd_308964 : Nat := 70509794193704182501825

theorem tailTrace_308964 : CollatzResearch.WordTrace tailWord_308964 prefixEnd_308964 70509794193704182501825 := by
  unfold tailWord_308964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634421426341834847662973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7512561901789113130217297 5634421426341834847662973)
  ·
    refine ⟨2112908034878188067873615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5634421426341834847662973 2112908034878188067873615)
    ·
      refine ⟨3169362052317282101810423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112908034878188067873615 3169362052317282101810423)
      ·
        refine ⟨4754043078475923152715635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169362052317282101810423 4754043078475923152715635)
        ·
          refine ⟨7131064617713884729073453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754043078475923152715635 7131064617713884729073453)
          ·
            refine ⟨2674149231642706773402545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7131064617713884729073453 2674149231642706773402545)
            ·
              refine ⟨2005611923732030080051909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2674149231642706773402545 2005611923732030080051909)
              ·
                refine ⟨376052235699755640009733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2005611923732030080051909 376052235699755640009733)
                ·
                  refine ⟨70509794193704182501825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376052235699755640009733 70509794193704182501825)
                  ·
                    rfl

theorem cell21_308964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_308964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_308964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_308964 prefixEnd_308964 := by exact prefixLift 308964
  have htrace : WordTrace (prefixWord ++ tailWord_308964) baseStart_308964 baseEnd_308964 := by
    simpa [prefixWord, tailWord_308964, baseEnd_308964] using wordTrace_append hprefix tailTrace_308964
  have hstable : (prefixWord ++ tailWord_308964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308964).length < 2 ^ (prefixWord ++ tailWord_308964).sum := by decide
  have hdescent : baseEnd_308964 < baseStart_308964 := by decide
  rcases family_descends (prefixWord ++ tailWord_308964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309012 : List Nat := [2, 4, 4, 1, 10]
def baseStart_309012 : Nat := 118140960795 + 309012 * 2 ^ 59
def prefixEnd_309012 : Nat := 4983230072969 + 3 ^ 40 * 309012 * 2
def baseEnd_309012 : Nat := 870626524045268712367

theorem tailTrace_309012 : CollatzResearch.WordTrace tailWord_309012 prefixEnd_309012 870626524045268712367 := by
  unfold tailWord_309012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635296778254886946536645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7513729037673182595382193 5635296778254886946536645)
  ·
    refine ⟨1056618145922791302475621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5635296778254886946536645 1056618145922791302475621)
    ·
      refine ⟨198115902360523369214179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1056618145922791302475621 198115902360523369214179)
      ·
        refine ⟨297173853540785053821269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198115902360523369214179 297173853540785053821269)
        ·
          refine ⟨870626524045268712367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 297173853540785053821269 870626524045268712367)
          ·
            rfl

theorem cell21_309012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 10].length) (baseStart_309012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309012 prefixEnd_309012 := by exact prefixLift 309012
  have htrace : WordTrace (prefixWord ++ tailWord_309012) baseStart_309012 baseEnd_309012 := by
    simpa [prefixWord, tailWord_309012, baseEnd_309012] using wordTrace_append hprefix tailTrace_309012
  have hstable : (prefixWord ++ tailWord_309012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309012).length < 2 ^ (prefixWord ++ tailWord_309012).sum := by decide
  have hdescent : baseEnd_309012 < baseStart_309012 := by decide
  rcases family_descends (prefixWord ++ tailWord_309012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309102 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_309102 : Nat := 118140960795 + 309102 * 2 ^ 59
def prefixEnd_309102 : Nat := 4983230072969 + 3 ^ 40 * 309102 * 2
def baseEnd_309102 : Nat := 70541287673846609201543

theorem tailTrace_309102 : CollatzResearch.WordTrace tailWord_309102 prefixEnd_309102 70541287673846609201543 := by
  unfold tailWord_309102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1409234515772964907981195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7515917417455812842566373 1409234515772964907981195)
  ·
    refine ⟨2113851773659447361971793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1409234515772964907981195 2113851773659447361971793)
    ·
      refine ⟨1585388830244585521478845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2113851773659447361971793 1585388830244585521478845)
      ·
        refine ⟨594520811341719570554567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1585388830244585521478845 594520811341719570554567)
        ·
          refine ⟨891781217012579355831851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594520811341719570554567 891781217012579355831851)
          ·
            refine ⟨1337671825518869033747777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891781217012579355831851 1337671825518869033747777)
            ·
              refine ⟨1003253869139151775310833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337671825518869033747777 1003253869139151775310833)
              ·
                refine ⟨752440401854363831483125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003253869139151775310833 752440401854363831483125)
                ·
                  refine ⟨70541287673846609201543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 752440401854363831483125 70541287673846609201543)
                  ·
                    rfl

theorem cell21_309102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_309102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309102 prefixEnd_309102 := by exact prefixLift 309102
  have htrace : WordTrace (prefixWord ++ tailWord_309102) baseStart_309102 baseEnd_309102 := by
    simpa [prefixWord, tailWord_309102, baseEnd_309102] using wordTrace_append hprefix tailTrace_309102
  have hstable : (prefixWord ++ tailWord_309102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309102).length < 2 ^ (prefixWord ++ tailWord_309102).sum := by decide
  have hdescent : baseEnd_309102 < baseStart_309102 := by decide
  rcases family_descends (prefixWord ++ tailWord_309102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309192 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 4]
def baseStart_309192 : Nat := 118140960795 + 309192 * 2 ^ 59
def prefixEnd_309192 : Nat := 4983230072969 + 3 ^ 40 * 309192 * 2
def baseEnd_309192 : Nat := 70561826900026452701359

theorem tailTrace_309192 : CollatzResearch.WordTrace tailWord_309192 prefixEnd_309192 70561826900026452701359 := by
  unfold tailWord_309192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638579347928832317312915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7518105797238443089750553 5638579347928832317312915)
  ·
    refine ⟨8457869021893248475969373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5638579347928832317312915 8457869021893248475969373)
    ·
      refine ⟨3171700883209968178488515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8457869021893248475969373 3171700883209968178488515)
      ·
        refine ⟨4757551324814952267732773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3171700883209968178488515 4757551324814952267732773)
        ·
          refine ⟨892040873402803550199895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4757551324814952267732773 892040873402803550199895)
          ·
            refine ⟨1338061310104205325299843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892040873402803550199895 1338061310104205325299843)
            ·
              refine ⟨2007091965156307987949765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1338061310104205325299843 2007091965156307987949765)
              ·
                refine ⟨376329743466807747740581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2007091965156307987949765 376329743466807747740581)
                ·
                  refine ⟨70561826900026452701359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376329743466807747740581 70561826900026452701359)
                  ·
                    rfl

theorem cell21_309192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_309192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309192 prefixEnd_309192 := by exact prefixLift 309192
  have htrace : WordTrace (prefixWord ++ tailWord_309192) baseStart_309192 baseEnd_309192 := by
    simpa [prefixWord, tailWord_309192, baseEnd_309192] using wordTrace_append hprefix tailTrace_309192
  have hstable : (prefixWord ++ tailWord_309192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309192).length < 2 ^ (prefixWord ++ tailWord_309192).sum := by decide
  have hdescent : baseEnd_309192 < baseStart_309192 := by decide
  rcases family_descends (prefixWord ++ tailWord_309192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309212 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 5]
def baseStart_309212 : Nat := 118140960795 + 309212 * 2 ^ 59
def prefixEnd_309212 : Nat := 4983230072969 + 3 ^ 40 * 309212 * 2
def baseEnd_309212 : Nat := 70566391172510862367985

theorem tailTrace_309212 : CollatzResearch.WordTrace tailWord_309212 prefixEnd_309212 70566391172510862367985 := by
  unfold tailWord_309212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638944077892604025176945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7518592103856805366902593 5638944077892604025176945)
  ·
    refine ⟨4229208058419453018882709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5638944077892604025176945 4229208058419453018882709)
    ·
      refine ⟨198244127738411860260127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4229208058419453018882709 198244127738411860260127)
      ·
        refine ⟨297366191607617790390191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198244127738411860260127 297366191607617790390191)
        ·
          refine ⟨446049287411426685585287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297366191607617790390191 446049287411426685585287)
          ·
            refine ⟨669073931117140028377931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446049287411426685585287 669073931117140028377931)
            ·
              refine ⟨1003610896675710042566897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669073931117140028377931 1003610896675710042566897)
              ·
                refine ⟨752708172506782531925173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003610896675710042566897 752708172506782531925173)
                ·
                  refine ⟨70566391172510862367985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 752708172506782531925173 70566391172510862367985)
                  ·
                    rfl

theorem cell21_309212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_309212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309212 prefixEnd_309212 := by exact prefixLift 309212
  have htrace : WordTrace (prefixWord ++ tailWord_309212) baseStart_309212 baseEnd_309212 := by
    simpa [prefixWord, tailWord_309212, baseEnd_309212] using wordTrace_append hprefix tailTrace_309212
  have hstable : (prefixWord ++ tailWord_309212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309212).length < 2 ^ (prefixWord ++ tailWord_309212).sum := by decide
  have hdescent : baseEnd_309212 < baseStart_309212 := by decide
  rcases family_descends (prefixWord ++ tailWord_309212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309282 : List Nat := [3, 3, 1, 1, 1, 2, 3, 7]
def baseStart_309282 : Nat := 118140960795 + 309282 * 2 ^ 59
def prefixEnd_309282 : Nat := 4983230072969 + 3 ^ 40 * 309282 * 2
def baseEnd_309282 : Nat := 23527455375402098733725

theorem tailTrace_309282 : CollatzResearch.WordTrace tailWord_309282 prefixEnd_309282 23527455375402098733725 := by
  unfold tailWord_309282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820110316382902501350525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7520294177021073336934733 2820110316382902501350525)
  ·
    refine ⟨1057541368643588438006447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2820110316382902501350525 1057541368643588438006447)
    ·
      refine ⟨1586312052965382657009671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057541368643588438006447 1586312052965382657009671)
      ·
        refine ⟨2379468079448073985514507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1586312052965382657009671 2379468079448073985514507)
        ·
          refine ⟨3569202119172110978271761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379468079448073985514507 3569202119172110978271761)
          ·
            refine ⟨2676901589379083233703821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3569202119172110978271761 2676901589379083233703821)
            ·
              refine ⟨1003838096017156212638933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2676901589379083233703821 1003838096017156212638933)
              ·
                refine ⟨23527455375402098733725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1003838096017156212638933 23527455375402098733725)
                ·
                  rfl

theorem cell21_309282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_309282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309282 prefixEnd_309282 := by exact prefixLift 309282
  have htrace : WordTrace (prefixWord ++ tailWord_309282) baseStart_309282 baseEnd_309282 := by
    simpa [prefixWord, tailWord_309282, baseEnd_309282] using wordTrace_append hprefix tailTrace_309282
  have hstable : (prefixWord ++ tailWord_309282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309282).length < 2 ^ (prefixWord ++ tailWord_309282).sum := by decide
  have hdescent : baseEnd_309282 < baseStart_309282 := by decide
  rcases family_descends (prefixWord ++ tailWord_309282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309327 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 4]
def baseStart_309327 : Nat := 118140960795 + 309327 * 2 ^ 59
def prefixEnd_309327 : Nat := 4983230072969 + 3 ^ 40 * 309327 * 2
def baseEnd_309327 : Nat := 70592635739296217951083

theorem tailTrace_309327 : CollatzResearch.WordTrace tailWord_309327 prefixEnd_309327 70592635739296217951083 := by
  unfold tailWord_309327
  simp only [CollatzResearch.WordTrace]
  refine ⟨11282082550368582690790235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7521388366912388460526823 11282082550368582690790235)
  ·
    refine ⟨16923123825552874036185353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11282082550368582690790235 16923123825552874036185353)
    ·
      refine ⟨12692342869164655527139015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16923123825552874036185353 12692342869164655527139015)
      ·
        refine ⟨19038514303746983290708523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12692342869164655527139015 19038514303746983290708523)
        ·
          refine ⟨28557771455620474936062785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19038514303746983290708523 28557771455620474936062785)
          ·
            refine ⟨21418328591715356202047089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28557771455620474936062785 21418328591715356202047089)
            ·
              refine ⟨16063746443786517151535317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21418328591715356202047089 16063746443786517151535317)
              ·
                refine ⟨376494057276246495739109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16063746443786517151535317 376494057276246495739109)
                ·
                  refine ⟨70592635739296217951083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376494057276246495739109 70592635739296217951083)
                  ·
                    rfl

theorem cell21_309327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 4].length) (baseStart_309327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309327 prefixEnd_309327 := by exact prefixLift 309327
  have htrace : WordTrace (prefixWord ++ tailWord_309327) baseStart_309327 baseEnd_309327 := by
    simpa [prefixWord, tailWord_309327, baseEnd_309327] using wordTrace_append hprefix tailTrace_309327
  have hstable : (prefixWord ++ tailWord_309327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309327).length < 2 ^ (prefixWord ++ tailWord_309327).sum := by decide
  have hdescent : baseEnd_309327 < baseStart_309327 := by decide
  rcases family_descends (prefixWord ++ tailWord_309327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309468 : List Nat := [2, 2, 5, 2, 1, 2, 7]
def baseStart_309468 : Nat := 118140960795 + 309468 * 2 ^ 59
def prefixEnd_309468 : Nat := 4983230072969 + 3 ^ 40 * 309468 * 2
def baseEnd_309468 : Nat := 7847201540034589566755

theorem tailTrace_309468 : CollatzResearch.WordTrace tailWord_309468 prefixEnd_309468 7847201540034589566755 := by
  unfold tailWord_309468
  simp only [CollatzResearch.WordTrace]
  refine ⟨5643612621428881885836529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7524816828571842514448705 5643612621428881885836529)
  ·
    refine ⟨4232709466071661414377397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5643612621428881885836529 4232709466071661414377397)
    ·
      refine ⟨396816512444218257597881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4232709466071661414377397 396816512444218257597881)
      ·
        refine ⟨297612384333163693198411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396816512444218257597881 297612384333163693198411)
        ·
          refine ⟨446418576499745539797617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297612384333163693198411 446418576499745539797617)
          ·
            refine ⟨334813932374809154848213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446418576499745539797617 334813932374809154848213)
            ·
              refine ⟨7847201540034589566755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 334813932374809154848213 7847201540034589566755)
              ·
                rfl

theorem cell21_309468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 7].length) (baseStart_309468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309468 prefixEnd_309468 := by exact prefixLift 309468
  have htrace : WordTrace (prefixWord ++ tailWord_309468) baseStart_309468 baseEnd_309468 := by
    simpa [prefixWord, tailWord_309468, baseEnd_309468] using wordTrace_append hprefix tailTrace_309468
  have hstable : (prefixWord ++ tailWord_309468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309468).length < 2 ^ (prefixWord ++ tailWord_309468).sum := by decide
  have hdescent : baseEnd_309468 < baseStart_309468 := by decide
  rcases family_descends (prefixWord ++ tailWord_309468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309474 : List Nat := [3, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_309474 : Nat := 118140960795 + 309474 * 2 ^ 59
def prefixEnd_309474 : Nat := 4983230072969 + 3 ^ 40 * 309474 * 2
def baseEnd_309474 : Nat := 70626183142056629000783

theorem tailTrace_309474 : CollatzResearch.WordTrace tailWord_309474 prefixEnd_309474 70626183142056629000783 := by
  unfold tailWord_309474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821861020209006699097869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7524962720557351197594317 2821861020209006699097869)
  ·
    refine ⟨1058197882578377512161701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2821861020209006699097869 1058197882578377512161701)
    ·
      refine ⟨198412102983445783530319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1058197882578377512161701 198412102983445783530319)
      ·
        refine ⟨297618154475168675295479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198412102983445783530319 297618154475168675295479)
        ·
          refine ⟨446427231712753012943219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297618154475168675295479 446427231712753012943219)
          ·
            refine ⟨669640847569129519414829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446427231712753012943219 669640847569129519414829)
            ·
              refine ⟨251115317838423569780561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 669640847569129519414829 251115317838423569780561)
              ·
                refine ⟨188336488378817677335421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251115317838423569780561 188336488378817677335421)
                ·
                  refine ⟨70626183142056629000783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188336488378817677335421 70626183142056629000783)
                  ·
                    rfl

theorem cell21_309474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_309474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309474 prefixEnd_309474 := by exact prefixLift 309474
  have htrace : WordTrace (prefixWord ++ tailWord_309474) baseStart_309474 baseEnd_309474 := by
    simpa [prefixWord, tailWord_309474, baseEnd_309474] using wordTrace_append hprefix tailTrace_309474
  have hstable : (prefixWord ++ tailWord_309474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309474).length < 2 ^ (prefixWord ++ tailWord_309474).sum := by decide
  have hdescent : baseEnd_309474 < baseStart_309474 := by decide
  rcases family_descends (prefixWord ++ tailWord_309474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309533 : List Nat := [1, 4, 2, 3, 3, 1, 2, 2, 3]
def baseStart_309533 : Nat := 118140960795 + 309533 * 2 ^ 59
def prefixEnd_309533 : Nat := 4983230072969 + 3 ^ 40 * 309533 * 2
def baseEnd_309533 : Nat := 70639647745885637517329

theorem tailTrace_309533 : CollatzResearch.WordTrace tailWord_309533 prefixEnd_309533 70639647745885637517329 := by
  unfold tailWord_309533
  simp only [CollatzResearch.WordTrace]
  refine ⟨11289595987622279872789253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7526397325081519915192835 11289595987622279872789253)
  ·
    refine ⟨2116799247679177476147985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11289595987622279872789253 2116799247679177476147985)
    ·
      refine ⟨1587599435759383107110989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2116799247679177476147985 1587599435759383107110989)
      ·
        refine ⟨595349788409768665166621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1587599435759383107110989 595349788409768665166621)
        ·
          refine ⟨223256170653663249437483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 595349788409768665166621 223256170653663249437483)
          ·
            refine ⟨334884255980494874156225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223256170653663249437483 334884255980494874156225)
            ·
              refine ⟨251163191985371155617169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334884255980494874156225 251163191985371155617169)
              ·
                refine ⟨188372393989028366712877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251163191985371155617169 188372393989028366712877)
                ·
                  refine ⟨70639647745885637517329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188372393989028366712877 70639647745885637517329)
                  ·
                    rfl

theorem cell21_309533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_309533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309533 prefixEnd_309533 := by exact prefixLift 309533
  have htrace : WordTrace (prefixWord ++ tailWord_309533) baseStart_309533 baseEnd_309533 := by
    simpa [prefixWord, tailWord_309533, baseEnd_309533] using wordTrace_append hprefix tailTrace_309533
  have hstable : (prefixWord ++ tailWord_309533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309533).length < 2 ^ (prefixWord ++ tailWord_309533).sum := by decide
  have hdescent : baseEnd_309533 < baseStart_309533 := by decide
  rcases family_descends (prefixWord ++ tailWord_309533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309544 : List Nat := [2, 1, 5, 1, 4, 1, 1, 6]
def baseStart_309544 : Nat := 118140960795 + 309544 * 2 ^ 59
def prefixEnd_309544 : Nat := 4983230072969 + 3 ^ 40 * 309544 * 2
def baseEnd_309544 : Nat := 23547386031917354277991

theorem tailTrace_309544 : CollatzResearch.WordTrace tailWord_309544 prefixEnd_309544 23547386031917354277991 := by
  unfold tailWord_309544
  simp only [CollatzResearch.WordTrace]
  refine ⟨5644998595291214375719843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7526664793721619167626457 5644998595291214375719843)
  ·
    refine ⟨8467497892936821563579765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5644998595291214375719843 8467497892936821563579765)
    ·
      refine ⟨793827927462827021585603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8467497892936821563579765 793827927462827021585603)
      ·
        refine ⟨1190741891194240532378405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793827927462827021585603 1190741891194240532378405)
        ·
          refine ⟨223264104598920099820951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1190741891194240532378405 223264104598920099820951)
          ·
            refine ⟨334896156898380149731427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223264104598920099820951 334896156898380149731427)
            ·
              refine ⟨502344235347570224597141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334896156898380149731427 502344235347570224597141)
              ·
                refine ⟨23547386031917354277991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 502344235347570224597141 23547386031917354277991)
                ·
                  rfl

theorem cell21_309544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 6].length) (baseStart_309544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309544 prefixEnd_309544 := by exact prefixLift 309544
  have htrace : WordTrace (prefixWord ++ tailWord_309544) baseStart_309544 baseEnd_309544 := by
    simpa [prefixWord, tailWord_309544, baseEnd_309544] using wordTrace_append hprefix tailTrace_309544
  have hstable : (prefixWord ++ tailWord_309544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309544).length < 2 ^ (prefixWord ++ tailWord_309544).sum := by decide
  have hdescent : baseEnd_309544 < baseStart_309544 := by decide
  rcases family_descends (prefixWord ++ tailWord_309544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309555 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 4]
def baseStart_309555 : Nat := 118140960795 + 309555 * 2 ^ 59
def prefixEnd_309555 : Nat := 4983230072969 + 3 ^ 40 * 309555 * 2
def baseEnd_309555 : Nat := 70644668445618488150617

theorem tailTrace_309555 : CollatzResearch.WordTrace tailWord_309555 prefixEnd_309555 70644668445618488150617 := by
  unfold tailWord_309555
  simp only [CollatzResearch.WordTrace]
  refine ⟨11290398393542577630090119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7526932262361718420060079 11290398393542577630090119)
  ·
    refine ⟨16935597590313866445135179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11290398393542577630090119 16935597590313866445135179)
    ·
      refine ⟨25403396385470799667702769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16935597590313866445135179 25403396385470799667702769)
      ·
        refine ⟨19052547289103099750777077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25403396385470799667702769 19052547289103099750777077)
        ·
          refine ⟨1786176308353415601635351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19052547289103099750777077 1786176308353415601635351)
          ·
            refine ⟨2679264462530123402453027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786176308353415601635351 2679264462530123402453027)
            ·
              refine ⟨4018896693795185103679541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679264462530123402453027 4018896693795185103679541)
              ·
                refine ⟨376771565043298603469957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4018896693795185103679541 376771565043298603469957)
                ·
                  refine ⟨70644668445618488150617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376771565043298603469957 70644668445618488150617)
                  ·
                    rfl

theorem cell21_309555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 4].length) (baseStart_309555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309555 prefixEnd_309555 := by exact prefixLift 309555
  have htrace : WordTrace (prefixWord ++ tailWord_309555) baseStart_309555 baseEnd_309555 := by
    simpa [prefixWord, tailWord_309555, baseEnd_309555] using wordTrace_append hprefix tailTrace_309555
  have hstable : (prefixWord ++ tailWord_309555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309555).length < 2 ^ (prefixWord ++ tailWord_309555).sum := by decide
  have hdescent : baseEnd_309555 < baseStart_309555 := by decide
  rcases family_descends (prefixWord ++ tailWord_309555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309589 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 4]
def baseStart_309589 : Nat := 118140960795 + 309589 * 2 ^ 59
def prefixEnd_309589 : Nat := 4983230072969 + 3 ^ 40 * 309589 * 2
def baseEnd_309589 : Nat := 70652427708841984583881

theorem tailTrace_309589 : CollatzResearch.WordTrace tailWord_309589 prefixEnd_309589 70652427708841984583881 := by
  unfold tailWord_309589
  simp only [CollatzResearch.WordTrace]
  refine ⟨11291638475419401436827821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7527758983612934291218547 11291638475419401436827821)
  ·
    refine ⟨4234364428282275538810433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11291638475419401436827821 4234364428282275538810433)
    ·
      refine ⟨3175773321211706654107825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4234364428282275538810433 3175773321211706654107825)
      ·
        refine ⟨2381829990908779990580869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3175773321211706654107825 2381829990908779990580869)
        ·
          refine ⟨446593123295396248233913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2381829990908779990580869 446593123295396248233913)
          ·
            refine ⟨334944842471547186175435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446593123295396248233913 334944842471547186175435)
            ·
              refine ⟨502417263707320779263153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334944842471547186175435 502417263707320779263153)
              ·
                refine ⟨376812947780490584447365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502417263707320779263153 376812947780490584447365)
                ·
                  refine ⟨70652427708841984583881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376812947780490584447365 70652427708841984583881)
                  ·
                    rfl

theorem cell21_309589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_309589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309589 prefixEnd_309589 := by exact prefixLift 309589
  have htrace : WordTrace (prefixWord ++ tailWord_309589) baseStart_309589 baseEnd_309589 := by
    simpa [prefixWord, tailWord_309589, baseEnd_309589] using wordTrace_append hprefix tailTrace_309589
  have hstable : (prefixWord ++ tailWord_309589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309589).length < 2 ^ (prefixWord ++ tailWord_309589).sum := by decide
  have hdescent : baseEnd_309589 < baseStart_309589 := by decide
  rcases family_descends (prefixWord ++ tailWord_309589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309665 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 4]
def baseStart_309665 : Nat := 118140960795 + 309665 * 2 ^ 59
def prefixEnd_309665 : Nat := 4983230072969 + 3 ^ 40 * 309665 * 2
def baseEnd_309665 : Nat := 70669771944282741317059

theorem tailTrace_309665 : CollatzResearch.WordTrace tailWord_309665 prefixEnd_309665 70669771944282741317059 := by
  unfold tailWord_309665
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294410423144066416594449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7529606948762710944396299 11294410423144066416594449)
  ·
    refine ⟨8470807817358049812445837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11294410423144066416594449 8470807817358049812445837)
    ·
      refine ⟨3176552931509268679667189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8470807817358049812445837 3176552931509268679667189)
      ·
        refine ⟨297801837328993938718799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3176552931509268679667189 297801837328993938718799)
        ·
          refine ⟨446702755993490908078199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297801837328993938718799 446702755993490908078199)
          ·
            refine ⟨670054133990236362117299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446702755993490908078199 670054133990236362117299)
            ·
              refine ⟨1005081200985354543175949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670054133990236362117299 1005081200985354543175949)
              ·
                refine ⟨376905450369507953690981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1005081200985354543175949 376905450369507953690981)
                ·
                  refine ⟨70669771944282741317059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 376905450369507953690981 70669771944282741317059)
                  ·
                    rfl

theorem cell21_309665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_309665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309665 prefixEnd_309665 := by exact prefixLift 309665
  have htrace : WordTrace (prefixWord ++ tailWord_309665) baseStart_309665 baseEnd_309665 := by
    simpa [prefixWord, tailWord_309665, baseEnd_309665] using wordTrace_append hprefix tailTrace_309665
  have hstable : (prefixWord ++ tailWord_309665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309665).length < 2 ^ (prefixWord ++ tailWord_309665).sum := by decide
  have hdescent : baseEnd_309665 < baseStart_309665 := by decide
  rcases family_descends (prefixWord ++ tailWord_309665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309690 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_309690 : Nat := 118140960795 + 309690 * 2 ^ 59
def prefixEnd_309690 : Nat := 4983230072969 + 3 ^ 40 * 309690 * 2
def baseEnd_309690 : Nat := 70675477284888253400341

theorem tailTrace_309690 : CollatzResearch.WordTrace tailWord_309690 prefixEnd_309690 70675477284888253400341 := by
  unfold tailWord_309690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2823830562013373921563631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7530214832035663790836349 2823830562013373921563631)
  ·
    refine ⟨4235745843020060882345447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2823830562013373921563631 4235745843020060882345447)
    ·
      refine ⟨6353618764530091323518171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235745843020060882345447 6353618764530091323518171)
      ·
        refine ⟨9530428146795136985277257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6353618764530091323518171 9530428146795136985277257)
        ·
          refine ⟨7147821110096352738957943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9530428146795136985277257 7147821110096352738957943)
          ·
            refine ⟨10721731665144529108436915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7147821110096352738957943 10721731665144529108436915)
            ·
              refine ⟨16082597497716793662655373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10721731665144529108436915 16082597497716793662655373)
              ·
                refine ⟨6030974061643797623495765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16082597497716793662655373 6030974061643797623495765)
                ·
                  refine ⟨70675477284888253400341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6030974061643797623495765 70675477284888253400341)
                  ·
                    rfl

theorem cell21_309690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_309690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309690 prefixEnd_309690 := by exact prefixLift 309690
  have htrace : WordTrace (prefixWord ++ tailWord_309690) baseStart_309690 baseEnd_309690 := by
    simpa [prefixWord, tailWord_309690, baseEnd_309690] using wordTrace_append hprefix tailTrace_309690
  have hstable : (prefixWord ++ tailWord_309690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309690).length < 2 ^ (prefixWord ++ tailWord_309690).sum := by decide
  have hdescent : baseEnd_309690 < baseStart_309690 := by decide
  rcases family_descends (prefixWord ++ tailWord_309690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309814 : List Nat := [5, 1, 2, 1, 2, 1, 9]
def baseStart_309814 : Nat := 118140960795 + 309814 * 2 ^ 59
def prefixEnd_309814 : Nat := 4983230072969 + 3 ^ 40 * 309814 * 2
def baseEnd_309814 : Nat := 7855975086032399259269

theorem tailTrace_309814 : CollatzResearch.WordTrace tailWord_309814 prefixEnd_309814 7855975086032399259269 := by
  unfold tailWord_309814
  simp only [CollatzResearch.WordTrace]
  refine ⟨706240306225266553985531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7533229933069509909178997 706240306225266553985531)
  ·
    refine ⟨1059360459337899830978297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 706240306225266553985531 1059360459337899830978297)
    ·
      refine ⟨794520344503424873233723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1059360459337899830978297 794520344503424873233723)
      ·
        refine ⟨1191780516755137309850585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794520344503424873233723 1191780516755137309850585)
        ·
          refine ⟨893835387566352982387939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1191780516755137309850585 893835387566352982387939)
          ·
            refine ⟨1340753081349529473581909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893835387566352982387939 1340753081349529473581909)
            ·
              refine ⟨7855975086032399259269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1340753081349529473581909 7855975086032399259269)
              ·
                rfl

theorem cell21_309814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 9].length) (baseStart_309814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309814 prefixEnd_309814 := by exact prefixLift 309814
  have htrace : WordTrace (prefixWord ++ tailWord_309814) baseStart_309814 baseEnd_309814 := by
    simpa [prefixWord, tailWord_309814, baseEnd_309814] using wordTrace_append hprefix tailTrace_309814
  have hstable : (prefixWord ++ tailWord_309814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309814).length < 2 ^ (prefixWord ++ tailWord_309814).sum := by decide
  have hdescent : baseEnd_309814 < baseStart_309814 := by decide
  rcases family_descends (prefixWord ++ tailWord_309814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309935 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 4]
def baseStart_309935 : Nat := 118140960795 + 309935 * 2 ^ 59
def prefixEnd_309935 : Nat := 4983230072969 + 3 ^ 40 * 309935 * 2
def baseEnd_309935 : Nat := 70731389622822271816507

theorem tailTrace_309935 : CollatzResearch.WordTrace tailWord_309935 prefixEnd_309935 70731389622822271816507 := by
  unfold tailWord_309935
  simp only [CollatzResearch.WordTrace]
  refine ⟨11304258132165902528923259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7536172088110601685948839 11304258132165902528923259)
  ·
    refine ⟨16956387198248853793384889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11304258132165902528923259 16956387198248853793384889)
    ·
      refine ⟨12717290398686640345038667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16956387198248853793384889 12717290398686640345038667)
      ·
        refine ⟨19075935598029960517558001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12717290398686640345038667 19075935598029960517558001)
        ·
          refine ⟨14306951698522470388168501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19075935598029960517558001 14306951698522470388168501)
          ·
            refine ⟨1341276721736481598890797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14306951698522470388168501 1341276721736481598890797)
            ·
              refine ⟨502978770651180599584049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1341276721736481598890797 502978770651180599584049)
              ·
                refine ⟨377234077988385449688037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502978770651180599584049 377234077988385449688037)
                ·
                  refine ⟨70731389622822271816507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377234077988385449688037 70731389622822271816507)
                  ·
                    rfl

theorem cell21_309935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 4].length) (baseStart_309935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309935 prefixEnd_309935 := by exact prefixLift 309935
  have htrace : WordTrace (prefixWord ++ tailWord_309935) baseStart_309935 baseEnd_309935 := by
    simpa [prefixWord, tailWord_309935, baseEnd_309935] using wordTrace_append hprefix tailTrace_309935
  have hstable : (prefixWord ++ tailWord_309935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309935).length < 2 ^ (prefixWord ++ tailWord_309935).sum := by decide
  have hdescent : baseEnd_309935 < baseStart_309935 := by decide
  rcases family_descends (prefixWord ++ tailWord_309935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309952 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_309952 : Nat := 118140960795 + 309952 * 2 ^ 59
def prefixEnd_309952 : Nat := 4983230072969 + 3 ^ 40 * 309952 * 2
def baseEnd_309952 : Nat := 70735269254434020033139

theorem tailTrace_309952 : CollatzResearch.WordTrace tailWord_309952 prefixEnd_309952 70735269254434020033139 := by
  unfold tailWord_309952
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652439086552157216146055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7536585448736209621528073 5652439086552157216146055)
  ·
    refine ⟨8478658629828235824219083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5652439086552157216146055 8478658629828235824219083)
    ·
      refine ⟨12717987944742353736328625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8478658629828235824219083 12717987944742353736328625)
      ·
        refine ⟨9538490958556765302246469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12717987944742353736328625 9538490958556765302246469)
        ·
          refine ⟨1788467054729393494171213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9538490958556765302246469 1788467054729393494171213)
          ·
            refine ⟨670675145523522560314205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1788467054729393494171213 670675145523522560314205)
            ·
              refine ⟨251503179571320960117827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 670675145523522560314205 251503179571320960117827)
              ·
                refine ⟨377254769356981440176741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251503179571320960117827 377254769356981440176741)
                ·
                  refine ⟨70735269254434020033139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377254769356981440176741 70735269254434020033139)
                  ·
                    rfl

theorem cell21_309952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_309952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309952 prefixEnd_309952 := by exact prefixLift 309952
  have htrace : WordTrace (prefixWord ++ tailWord_309952) baseStart_309952 baseEnd_309952 := by
    simpa [prefixWord, tailWord_309952, baseEnd_309952] using wordTrace_append hprefix tailTrace_309952
  have hstable : (prefixWord ++ tailWord_309952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309952).length < 2 ^ (prefixWord ++ tailWord_309952).sum := by decide
  have hdescent : baseEnd_309952 < baseStart_309952 := by decide
  rcases family_descends (prefixWord ++ tailWord_309952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309958 : List Nat := [6, 1, 2, 1, 3, 1, 2, 5]
def baseStart_309958 : Nat := 118140960795 + 309958 * 2 ^ 59
def prefixEnd_309958 : Nat := 4983230072969 + 3 ^ 40 * 309958 * 2
def baseEnd_309958 : Nat := 23578879512059780977709

theorem tailTrace_309958 : CollatzResearch.WordTrace tailWord_309958 prefixEnd_309958 23578879512059780977709 := by
  unfold tailWord_309958
  simp only [CollatzResearch.WordTrace]
  refine ⟨353284281596330545531579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7536731340721718304673685 353284281596330545531579)
  ·
    refine ⟨529926422394495818297369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353284281596330545531579 529926422394495818297369)
    ·
      refine ⟨397444816795871863723027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 529926422394495818297369 397444816795871863723027)
      ·
        refine ⟨596167225193807795584541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397444816795871863723027 596167225193807795584541)
        ·
          refine ⟨223562709447677923344203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 596167225193807795584541 223562709447677923344203)
          ·
            refine ⟨335344064171516885016305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223562709447677923344203 335344064171516885016305)
            ·
              refine ⟨251508048128637663762229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335344064171516885016305 251508048128637663762229)
              ·
                refine ⟨23578879512059780977709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 251508048128637663762229 23578879512059780977709)
                ·
                  rfl

theorem cell21_309958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_309958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309958 prefixEnd_309958 := by exact prefixLift 309958
  have htrace : WordTrace (prefixWord ++ tailWord_309958) baseStart_309958 baseEnd_309958 := by
    simpa [prefixWord, tailWord_309958, baseEnd_309958] using wordTrace_append hprefix tailTrace_309958
  have hstable : (prefixWord ++ tailWord_309958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309958).length < 2 ^ (prefixWord ++ tailWord_309958).sum := by decide
  have hdescent : baseEnd_309958 < baseStart_309958 := by decide
  rcases family_descends (prefixWord ++ tailWord_309958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309966 : List Nat := [4, 1, 1, 1, 3, 2, 4, 5]
def baseStart_309966 : Nat := 118140960795 + 309966 * 2 ^ 59
def prefixEnd_309966 : Nat := 4983230072969 + 3 ^ 40 * 309966 * 2
def baseEnd_309966 : Nat := 23579488081724368933259

theorem tailTrace_309966 : CollatzResearch.WordTrace tailWord_309966 prefixEnd_309966 23579488081724368933259 := by
  unfold tailWord_309966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413173599381699352912719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7536925863369063215534501 1413173599381699352912719)
  ·
    refine ⟨2119760399072549029369079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1413173599381699352912719 2119760399072549029369079)
    ·
      refine ⟨3179640598608823544053619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2119760399072549029369079 3179640598608823544053619)
      ·
        refine ⟨4769460897913235316080429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3179640598608823544053619 4769460897913235316080429)
        ·
          refine ⟨1788547836717463243530161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4769460897913235316080429 1788547836717463243530161)
          ·
            refine ⟨1341410877538097432647621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1788547836717463243530161 1341410877538097432647621)
            ·
              refine ⟨251514539538393268621429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1341410877538097432647621 251514539538393268621429)
              ·
                refine ⟨23579488081724368933259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 251514539538393268621429 23579488081724368933259)
                ·
                  rfl

theorem cell21_309966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_309966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309966 prefixEnd_309966 := by exact prefixLift 309966
  have htrace : WordTrace (prefixWord ++ tailWord_309966) baseStart_309966 baseEnd_309966 := by
    simpa [prefixWord, tailWord_309966, baseEnd_309966] using wordTrace_append hprefix tailTrace_309966
  have hstable : (prefixWord ++ tailWord_309966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309966).length < 2 ^ (prefixWord ++ tailWord_309966).sum := by decide
  have hdescent : baseEnd_309966 < baseStart_309966 := by decide
  rcases family_descends (prefixWord ++ tailWord_309966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309972 : List Nat := [2, 4, 1, 3, 3, 1, 1, 3, 3]
def baseStart_309972 : Nat := 118140960795 + 309972 * 2 ^ 59
def prefixEnd_309972 : Nat := 4983230072969 + 3 ^ 40 * 309972 * 2
def baseEnd_309972 : Nat := 70739833526918429699765

theorem tailTrace_309972 : CollatzResearch.WordTrace tailWord_309972 prefixEnd_309972 70739833526918429699765 := by
  unfold tailWord_309972
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652803816515928924010085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7537071755354571898680113 5652803816515928924010085)
  ·
    refine ⟨1059900715596736673251891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5652803816515928924010085 1059900715596736673251891)
    ·
      refine ⟨1589851073395105009877837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059900715596736673251891 1589851073395105009877837)
      ·
        refine ⟨596194152523164378704189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1589851073395105009877837 596194152523164378704189)
        ·
          refine ⟨223572807196186642014071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 596194152523164378704189 223572807196186642014071)
          ·
            refine ⟨335359210794279963021107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223572807196186642014071 335359210794279963021107)
            ·
              refine ⟨503038816191419944531661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335359210794279963021107 503038816191419944531661)
              ·
                refine ⟨188639556071782479199373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503038816191419944531661 188639556071782479199373)
                ·
                  refine ⟨70739833526918429699765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188639556071782479199373 70739833526918429699765)
                  ·
                    rfl

theorem cell21_309972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_309972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_309972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_309972 prefixEnd_309972 := by exact prefixLift 309972
  have htrace : WordTrace (prefixWord ++ tailWord_309972) baseStart_309972 baseEnd_309972 := by
    simpa [prefixWord, tailWord_309972, baseEnd_309972] using wordTrace_append hprefix tailTrace_309972
  have hstable : (prefixWord ++ tailWord_309972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309972).length < 2 ^ (prefixWord ++ tailWord_309972).sum := by decide
  have hdescent : baseEnd_309972 < baseStart_309972 := by decide
  rcases family_descends (prefixWord ++ tailWord_309972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310045 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 4]
def baseStart_310045 : Nat := 118140960795 + 310045 * 2 ^ 59
def prefixEnd_310045 : Nat := 4983230072969 + 3 ^ 40 * 310045 * 2
def baseEnd_310045 : Nat := 70756493121486524982949

theorem tailTrace_310045 : CollatzResearch.WordTrace tailWord_310045 prefixEnd_310045 70756493121486524982949 := by
  unfold tailWord_310045
  simp only [CollatzResearch.WordTrace]
  refine ⟨11308270161767391315427589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7538846774511594210285059 11308270161767391315427589)
  ·
    refine ⟨2120300655331385871642673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11308270161767391315427589 2120300655331385871642673)
    ·
      refine ⟨1590225491498539403732005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2120300655331385871642673 1590225491498539403732005)
      ·
        refine ⟨298167279655976138199751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1590225491498539403732005 298167279655976138199751)
        ·
          refine ⟨447250919483964207299627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298167279655976138199751 447250919483964207299627)
          ·
            refine ⟨670876379225946310949441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447250919483964207299627 670876379225946310949441)
            ·
              refine ⟨503157284419459733212081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670876379225946310949441 503157284419459733212081)
              ·
                refine ⟨377367963314594799909061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503157284419459733212081 377367963314594799909061)
                ·
                  refine ⟨70756493121486524982949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377367963314594799909061 70756493121486524982949)
                  ·
                    rfl

theorem cell21_310045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_310045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310045 prefixEnd_310045 := by exact prefixLift 310045
  have htrace : WordTrace (prefixWord ++ tailWord_310045) baseStart_310045 baseEnd_310045 := by
    simpa [prefixWord, tailWord_310045, baseEnd_310045] using wordTrace_append hprefix tailTrace_310045
  have hstable : (prefixWord ++ tailWord_310045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310045).length < 2 ^ (prefixWord ++ tailWord_310045).sum := by decide
  have hdescent : baseEnd_310045 < baseStart_310045 := by decide
  rcases family_descends (prefixWord ++ tailWord_310045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310056 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 5]
def baseStart_310056 : Nat := 118140960795 + 310056 * 2 ^ 59
def prefixEnd_310056 : Nat := 4983230072969 + 3 ^ 40 * 310056 * 2
def baseEnd_310056 : Nat := 70759003471352950299593

theorem tailTrace_310056 : CollatzResearch.WordTrace tailWord_310056 prefixEnd_310056 70759003471352950299593 := by
  unfold tailWord_310056
  simp only [CollatzResearch.WordTrace]
  refine ⟨5654335682363770097039011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7539114243151693462718681 5654335682363770097039011)
  ·
    refine ⟨8481503523545655145558517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5654335682363770097039011 8481503523545655145558517)
    ·
      refine ⟨795140955332405169896111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8481503523545655145558517 795140955332405169896111)
      ·
        refine ⟨1192711432998607754844167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795140955332405169896111 1192711432998607754844167)
        ·
          refine ⟨1789067149497911632266251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192711432998607754844167 1789067149497911632266251)
          ·
            refine ⟨2683600724246867448399377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789067149497911632266251 2683600724246867448399377)
            ·
              refine ⟨2012700543185150586299533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2683600724246867448399377 2012700543185150586299533)
              ·
                refine ⟨754762703694431469862325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2012700543185150586299533 754762703694431469862325)
                ·
                  refine ⟨70759003471352950299593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 754762703694431469862325 70759003471352950299593)
                  ·
                    rfl

theorem cell21_310056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_310056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310056 prefixEnd_310056 := by exact prefixLift 310056
  have htrace : WordTrace (prefixWord ++ tailWord_310056) baseStart_310056 baseEnd_310056 := by
    simpa [prefixWord, tailWord_310056, baseEnd_310056] using wordTrace_append hprefix tailTrace_310056
  have hstable : (prefixWord ++ tailWord_310056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310056).length < 2 ^ (prefixWord ++ tailWord_310056).sum := by decide
  have hdescent : baseEnd_310056 < baseStart_310056 := by decide
  rcases family_descends (prefixWord ++ tailWord_310056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310149 : List Nat := [1, 3, 1, 1, 3, 3, 3, 3, 3]
def baseStart_310149 : Nat := 118140960795 + 310149 * 2 ^ 59
def prefixEnd_310149 : Nat := 4983230072969 + 3 ^ 40 * 310149 * 2
def baseEnd_310149 : Nat := 70780227338405455249403

theorem tailTrace_310149 : CollatzResearch.WordTrace tailWord_310149 prefixEnd_310149 70780227338405455249403 := by
  unfold tailWord_310149
  simp only [CollatzResearch.WordTrace]
  refine ⟨11312063353390617077213501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7541375568927078051475667 11312063353390617077213501)
  ·
    refine ⟨4242023757521481403955063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11312063353390617077213501 4242023757521481403955063)
    ·
      refine ⟨6363035636282222105932595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4242023757521481403955063 6363035636282222105932595)
      ·
        refine ⟨9544553454423333158898893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6363035636282222105932595 9544553454423333158898893)
        ·
          refine ⟨3579207545408749934587085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9544553454423333158898893 3579207545408749934587085)
          ·
            refine ⟨1342202829528281225470157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3579207545408749934587085 1342202829528281225470157)
            ·
              refine ⟨503326061073105459551309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1342202829528281225470157 503326061073105459551309)
              ·
                refine ⟨188747272902414547331741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503326061073105459551309 188747272902414547331741)
                ·
                  refine ⟨70780227338405455249403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188747272902414547331741 70780227338405455249403)
                  ·
                    rfl

theorem cell21_310149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_310149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310149 prefixEnd_310149 := by exact prefixLift 310149
  have htrace : WordTrace (prefixWord ++ tailWord_310149) baseStart_310149 baseEnd_310149 := by
    simpa [prefixWord, tailWord_310149, baseEnd_310149] using wordTrace_append hprefix tailTrace_310149
  have hstable : (prefixWord ++ tailWord_310149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310149).length < 2 ^ (prefixWord ++ tailWord_310149).sum := by decide
  have hdescent : baseEnd_310149 < baseStart_310149 := by decide
  rcases family_descends (prefixWord ++ tailWord_310149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310177 : List Nat := [1, 2, 3, 4, 1, 1, 1, 8]
def baseStart_310177 : Nat := 118140960795 + 310177 * 2 ^ 59
def prefixEnd_310177 : Nat := 4983230072969 + 3 ^ 40 * 310177 * 2
def baseEnd_310177 : Nat := 23595539106627876260893

theorem tailTrace_310177 : CollatzResearch.WordTrace tailWord_310177 prefixEnd_310177 23595539106627876260893 := by
  unfold tailWord_310177
  simp only [CollatzResearch.WordTrace]
  refine ⟨11313084597289177859232785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7542056398192785239488523 11313084597289177859232785)
  ·
    refine ⟨8484813447966883394424589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11313084597289177859232785 8484813447966883394424589)
    ·
      refine ⟨3181805042987581272909221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8484813447966883394424589 3181805042987581272909221)
      ·
        refine ⟨596588445560171488670479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3181805042987581272909221 596588445560171488670479)
        ·
          refine ⟨894882668340257233005719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596588445560171488670479 894882668340257233005719)
          ·
            refine ⟨1342324002510385849508579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894882668340257233005719 1342324002510385849508579)
            ·
              refine ⟨2013486003765578774262869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342324002510385849508579 2013486003765578774262869)
              ·
                refine ⟨23595539106627876260893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2013486003765578774262869 23595539106627876260893)
                ·
                  rfl

theorem cell21_310177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 8].length) (baseStart_310177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310177 prefixEnd_310177 := by exact prefixLift 310177
  have htrace : WordTrace (prefixWord ++ tailWord_310177) baseStart_310177 baseEnd_310177 := by
    simpa [prefixWord, tailWord_310177, baseEnd_310177] using wordTrace_append hprefix tailTrace_310177
  have hstable : (prefixWord ++ tailWord_310177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310177).length < 2 ^ (prefixWord ++ tailWord_310177).sum := by decide
  have hdescent : baseEnd_310177 < baseStart_310177 := by decide
  rcases family_descends (prefixWord ++ tailWord_310177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310270 : List Nat := [4, 2, 2, 2, 2, 1, 8]
def baseStart_310270 : Nat := 118140960795 + 310270 * 2 ^ 59
def prefixEnd_310270 : Nat := 4983230072969 + 3 ^ 40 * 310270 * 2
def baseEnd_310270 : Nat := 7867537909659570414721

theorem tailTrace_310270 : CollatzResearch.WordTrace tailWord_310270 prefixEnd_310270 7867537909659570414721 := by
  unfold tailWord_310270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414559573244031842796033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7544317723968169828245509 1414559573244031842796033)
  ·
    refine ⟨1060919679933023882097025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1414559573244031842796033 1060919679933023882097025)
    ·
      refine ⟨795689759949767911572769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1060919679933023882097025 795689759949767911572769)
      ·
        refine ⟨596767319962325933679577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 795689759949767911572769 596767319962325933679577)
        ·
          refine ⟨447575489971744450259683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596767319962325933679577 447575489971744450259683)
          ·
            refine ⟨671363234957616675389525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447575489971744450259683 671363234957616675389525)
            ·
              refine ⟨7867537909659570414721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 671363234957616675389525 7867537909659570414721)
              ·
                rfl

theorem cell21_310270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 8].length) (baseStart_310270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310270 prefixEnd_310270 := by exact prefixLift 310270
  have htrace : WordTrace (prefixWord ++ tailWord_310270) baseStart_310270 baseEnd_310270 := by
    simpa [prefixWord, tailWord_310270, baseEnd_310270] using wordTrace_append hprefix tailTrace_310270
  have hstable : (prefixWord ++ tailWord_310270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310270).length < 2 ^ (prefixWord ++ tailWord_310270).sum := by decide
  have hdescent : baseEnd_310270 < baseStart_310270 := by decide
  rcases family_descends (prefixWord ++ tailWord_310270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310284 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_310284 : Nat := 118140960795 + 310284 * 2 ^ 59
def prefixEnd_310284 : Nat := 4983230072969 + 3 ^ 40 * 310284 * 2
def baseEnd_310284 : Nat := 70811036177675220499127

theorem tailTrace_310284 : CollatzResearch.WordTrace tailWord_310284 prefixEnd_310284 70811036177675220499127 := by
  unfold tailWord_310284
  simp only [CollatzResearch.WordTrace]
  refine ⟨5658493603950767566688953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7544658138601023422251937 5658493603950767566688953)
  ·
    refine ⟨4243870202963075675016715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5658493603950767566688953 4243870202963075675016715)
    ·
      refine ⟨6365805304444613512525073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4243870202963075675016715 6365805304444613512525073)
      ·
        refine ⟨4774353978333460134393805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6365805304444613512525073 4774353978333460134393805)
        ·
          refine ⟨1790382741875047550397677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4774353978333460134393805 1790382741875047550397677)
          ·
            refine ⟨671393528203142831399129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1790382741875047550397677 671393528203142831399129)
            ·
              refine ⟨503545146152357123549347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671393528203142831399129 503545146152357123549347)
              ·
                refine ⟨755317719228535685324021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503545146152357123549347 755317719228535685324021)
                ·
                  refine ⟨70811036177675220499127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 755317719228535685324021 70811036177675220499127)
                  ·
                    rfl

theorem cell21_310284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_310284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310284 prefixEnd_310284 := by exact prefixLift 310284
  have htrace : WordTrace (prefixWord ++ tailWord_310284) baseStart_310284 baseEnd_310284 := by
    simpa [prefixWord, tailWord_310284, baseEnd_310284] using wordTrace_append hprefix tailTrace_310284
  have hstable : (prefixWord ++ tailWord_310284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310284).length < 2 ^ (prefixWord ++ tailWord_310284).sum := by decide
  have hdescent : baseEnd_310284 < baseStart_310284 := by decide
  rcases family_descends (prefixWord ++ tailWord_310284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310304 : List Nat := [2, 1, 1, 7, 2, 1, 2, 5]
def baseStart_310304 : Nat := 118140960795 + 310304 * 2 ^ 59
def prefixEnd_310304 : Nat := 4983230072969 + 3 ^ 40 * 310304 * 2
def baseEnd_310304 : Nat := 23605200150053210055251

theorem tailTrace_310304 : CollatzResearch.WordTrace tailWord_310304 prefixEnd_310304 23605200150053210055251 := by
  unfold tailWord_310304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5658858333914539274552983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7545144445219385699403977 5658858333914539274552983)
  ·
    refine ⟨8488287500871808911829475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5658858333914539274552983 8488287500871808911829475)
    ·
      refine ⟨12732431251307713367744213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8488287500871808911829475 12732431251307713367744213)
      ·
        refine ⟨298416357452524532056505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12732431251307713367744213 298416357452524532056505)
        ·
          refine ⟨223812268089393399042379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298416357452524532056505 223812268089393399042379)
          ·
            refine ⟨335718402134090098563569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223812268089393399042379 335718402134090098563569)
            ·
              refine ⟨251788801600567573922677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335718402134090098563569 251788801600567573922677)
              ·
                refine ⟨23605200150053210055251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 251788801600567573922677 23605200150053210055251)
                ·
                  rfl

theorem cell21_310304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_310304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310304 prefixEnd_310304 := by exact prefixLift 310304
  have htrace : WordTrace (prefixWord ++ tailWord_310304) baseStart_310304 baseEnd_310304 := by
    simpa [prefixWord, tailWord_310304, baseEnd_310304] using wordTrace_append hprefix tailTrace_310304
  have hstable : (prefixWord ++ tailWord_310304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310304).length < 2 ^ (prefixWord ++ tailWord_310304).sum := by decide
  have hdescent : baseEnd_310304 < baseStart_310304 := by decide
  rcases family_descends (prefixWord ++ tailWord_310304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310329 : List Nat := [1, 2, 1, 5, 2, 3, 7]
def baseStart_310329 : Nat := 118140960795 + 310329 * 2 ^ 59
def prefixEnd_310329 : Nat := 4983230072969 + 3 ^ 40 * 310329 * 2
def baseEnd_310329 : Nat := 7869033976751682472115

theorem tailTrace_310329 : CollatzResearch.WordTrace tailWord_310329 prefixEnd_310329 7869033976751682472115 := by
  unfold tailWord_310329
  simp only [CollatzResearch.WordTrace]
  refine ⟨11318628492738507818766041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7545752328492338545844027 11318628492738507818766041)
  ·
    refine ⟨8488971369553880864074531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11318628492738507818766041 8488971369553880864074531)
    ·
      refine ⟨12733457054330821296111797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8488971369553880864074531 12733457054330821296111797)
      ·
        refine ⟨1193761598843514496510481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12733457054330821296111797 1193761598843514496510481)
        ·
          refine ⟨895321199132635872382861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1193761598843514496510481 895321199132635872382861)
          ·
            refine ⟨335745449674738452143573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 895321199132635872382861 335745449674738452143573)
            ·
              refine ⟨7869033976751682472115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 335745449674738452143573 7869033976751682472115)
              ·
                rfl

theorem cell21_310329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 7].length) (baseStart_310329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310329 prefixEnd_310329 := by exact prefixLift 310329
  have htrace : WordTrace (prefixWord ++ tailWord_310329) baseStart_310329 baseEnd_310329 := by
    simpa [prefixWord, tailWord_310329, baseEnd_310329] using wordTrace_append hprefix tailTrace_310329
  have hstable : (prefixWord ++ tailWord_310329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310329).length < 2 ^ (prefixWord ++ tailWord_310329).sum := by decide
  have hdescent : baseEnd_310329 < baseStart_310329 := by decide
  rcases family_descends (prefixWord ++ tailWord_310329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310349 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 4]
def baseStart_310349 : Nat := 118140960795 + 310349 * 2 ^ 59
def prefixEnd_310349 : Nat := 4983230072969 + 3 ^ 40 * 310349 * 2
def baseEnd_310349 : Nat := 70825870063249551915661

theorem tailTrace_310349 : CollatzResearch.WordTrace tailWord_310349 prefixEnd_310349 70825870063249551915661 := by
  unfold tailWord_310349
  simp only [CollatzResearch.WordTrace]
  refine ⟨11319357952666051234494101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7546238635110700822996067 11319357952666051234494101)
  ·
    refine ⟨530594904031221151616911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11319357952666051234494101 530594904031221151616911)
    ·
      refine ⟨795892356046831727425367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530594904031221151616911 795892356046831727425367)
      ·
        refine ⟨1193838534070247591138051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795892356046831727425367 1193838534070247591138051)
        ·
          refine ⟨1790757801105371386707077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193838534070247591138051 1790757801105371386707077)
          ·
            refine ⟨335767087707257135007577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1790757801105371386707077 335767087707257135007577)
            ·
              refine ⟨251825315780442851255683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335767087707257135007577 251825315780442851255683)
              ·
                refine ⟨377737973670664276883525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251825315780442851255683 377737973670664276883525)
                ·
                  refine ⟨70825870063249551915661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377737973670664276883525 70825870063249551915661)
                  ·
                    rfl

theorem cell21_310349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_310349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310349 prefixEnd_310349 := by exact prefixLift 310349
  have htrace : WordTrace (prefixWord ++ tailWord_310349) baseStart_310349 baseEnd_310349 := by
    simpa [prefixWord, tailWord_310349, baseEnd_310349] using wordTrace_append hprefix tailTrace_310349
  have hstable : (prefixWord ++ tailWord_310349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310349).length < 2 ^ (prefixWord ++ tailWord_310349).sum := by decide
  have hdescent : baseEnd_310349 < baseStart_310349 := by decide
  rcases family_descends (prefixWord ++ tailWord_310349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310450 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_310450 : Nat := 118140960795 + 310450 * 2 ^ 59
def prefixEnd_310450 : Nat := 4983230072969 + 3 ^ 40 * 310450 * 2
def baseEnd_310450 : Nat := 70848919639295820732121

theorem tailTrace_310450 : CollatzResearch.WordTrace tailWord_310450 prefixEnd_310450 70848919639295820732121 := by
  unfold tailWord_310450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2830760431325036370980201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7548694483533430322613869 2830760431325036370980201)
  ·
    refine ⟨2123070323493777278235151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2830760431325036370980201 2123070323493777278235151)
    ·
      refine ⟨3184605485240665917352727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2123070323493777278235151 3184605485240665917352727)
      ·
        refine ⟨4776908227860998876029091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184605485240665917352727 4776908227860998876029091)
        ·
          refine ⟨7165362341791498314043637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776908227860998876029091 7165362341791498314043637)
          ·
            refine ⟨671752719542952966941591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7165362341791498314043637 671752719542952966941591)
            ·
              refine ⟨1007629079314429450412387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671752719542952966941591 1007629079314429450412387)
              ·
                refine ⟨1511443618971644175618581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007629079314429450412387 1511443618971644175618581)
                ·
                  refine ⟨70848919639295820732121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1511443618971644175618581 70848919639295820732121)
                  ·
                    rfl

theorem cell21_310450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_310450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310450 prefixEnd_310450 := by exact prefixLift 310450
  have htrace : WordTrace (prefixWord ++ tailWord_310450) baseStart_310450 baseEnd_310450 := by
    simpa [prefixWord, tailWord_310450, baseEnd_310450] using wordTrace_append hprefix tailTrace_310450
  have hstable : (prefixWord ++ tailWord_310450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310450).length < 2 ^ (prefixWord ++ tailWord_310450).sum := by decide
  have hdescent : baseEnd_310450 < baseStart_310450 := by decide
  rcases family_descends (prefixWord ++ tailWord_310450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310540 : List Nat := [2, 2, 1, 2, 2, 3, 2, 7]
def baseStart_310540 : Nat := 118140960795 + 310540 * 2 ^ 59
def prefixEnd_310540 : Nat := 4983230072969 + 3 ^ 40 * 310540 * 2
def baseEnd_310540 : Nat := 23623152955158554743979

theorem tailTrace_310540 : CollatzResearch.WordTrace tailWord_310540 prefixEnd_310540 23623152955158554743979 := by
  unfold tailWord_310540
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663162147487045427348537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7550882863316060569798049 5663162147487045427348537)
  ·
    refine ⟨4247371610615284070511403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5663162147487045427348537 4247371610615284070511403)
    ·
      refine ⟨6371057415922926105767105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4247371610615284070511403 6371057415922926105767105)
      ·
        refine ⟨4778293061942194579325329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6371057415922926105767105 4778293061942194579325329)
        ·
          refine ⟨3583719796456645934493997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4778293061942194579325329 3583719796456645934493997)
          ·
            refine ⟨1343894923671242225435249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3583719796456645934493997 1343894923671242225435249)
            ·
              refine ⟨1007921192753431669076437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1343894923671242225435249 1007921192753431669076437)
              ·
                refine ⟨23623152955158554743979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1007921192753431669076437 23623152955158554743979)
                ·
                  rfl

theorem cell21_310540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_310540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310540 prefixEnd_310540 := by exact prefixLift 310540
  have htrace : WordTrace (prefixWord ++ tailWord_310540) baseStart_310540 baseEnd_310540 := by
    simpa [prefixWord, tailWord_310540, baseEnd_310540] using wordTrace_append hprefix tailTrace_310540
  have hstable : (prefixWord ++ tailWord_310540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310540).length < 2 ^ (prefixWord ++ tailWord_310540).sum := by decide
  have hdescent : baseEnd_310540 < baseStart_310540 := by decide
  rcases family_descends (prefixWord ++ tailWord_310540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310661 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 6]
def baseStart_310661 : Nat := 118140960795 + 310661 * 2 ^ 59
def prefixEnd_310661 : Nat := 4983230072969 + 3 ^ 40 * 310661 * 2
def baseEnd_310661 : Nat := 70897072714006342715023

theorem tailTrace_310661 : CollatzResearch.WordTrace tailWord_310661 prefixEnd_310661 70897072714006342715023 := by
  unfold tailWord_310661
  simp only [CollatzResearch.WordTrace]
  refine ⟨11330737527535728519851837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7553825018357152346567891 11330737527535728519851837)
  ·
    refine ⟨4249026572825898194944439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11330737527535728519851837 4249026572825898194944439)
    ·
      refine ⟨6373539859238847292416659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4249026572825898194944439 6373539859238847292416659)
      ·
        refine ⟨9560309788858270938624989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6373539859238847292416659 9560309788858270938624989)
        ·
          refine ⟨3585116170821851601984371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9560309788858270938624989 3585116170821851601984371)
          ·
            refine ⟨5377674256232777402976557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585116170821851601984371 5377674256232777402976557)
            ·
              refine ⟨2016627846087291526116209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5377674256232777402976557 2016627846087291526116209)
              ·
                refine ⟨1512470884565468644587157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016627846087291526116209 1512470884565468644587157)
                ·
                  refine ⟨70897072714006342715023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1512470884565468644587157 70897072714006342715023)
                  ·
                    rfl

theorem cell21_310661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_310661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310661 prefixEnd_310661 := by exact prefixLift 310661
  have htrace : WordTrace (prefixWord ++ tailWord_310661) baseStart_310661 baseEnd_310661 := by
    simpa [prefixWord, tailWord_310661, baseEnd_310661] using wordTrace_append hprefix tailTrace_310661
  have hstable : (prefixWord ++ tailWord_310661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310661).length < 2 ^ (prefixWord ++ tailWord_310661).sum := by decide
  have hdescent : baseEnd_310661 < baseStart_310661 := by decide
  rcases family_descends (prefixWord ++ tailWord_310661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310681 : List Nat := [1, 2, 1, 2, 1, 6, 3, 2, 3]
def baseStart_310681 : Nat := 118140960795 + 310681 * 2 ^ 59
def prefixEnd_310681 : Nat := 4983230072969 + 3 ^ 40 * 310681 * 2
def baseEnd_310681 : Nat := 70901636986490752381649

theorem tailTrace_310681 : CollatzResearch.WordTrace tailWord_310681 prefixEnd_310681 70901636986490752381649 := by
  unfold tailWord_310681
  simp only [CollatzResearch.WordTrace]
  refine ⟨11331466987463271935579897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7554311324975514623719931 11331466987463271935579897)
  ·
    refine ⟨8498600240597453951684923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11331466987463271935579897 8498600240597453951684923)
    ·
      refine ⟨12747900360896180927527385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8498600240597453951684923 12747900360896180927527385)
      ·
        refine ⟨9560925270672135695645539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12747900360896180927527385 9560925270672135695645539)
        ·
          refine ⟨14341387906008203543468309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9560925270672135695645539 14341387906008203543468309)
          ·
            refine ⟨672252558094134541100077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14341387906008203543468309 672252558094134541100077)
            ·
              refine ⟨252094709285300452912529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 672252558094134541100077 252094709285300452912529)
              ·
                refine ⟨189071031963975339684397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252094709285300452912529 189071031963975339684397)
                ·
                  refine ⟨70901636986490752381649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189071031963975339684397 70901636986490752381649)
                  ·
                    rfl

theorem cell21_310681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_310681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310681 prefixEnd_310681 := by exact prefixLift 310681
  have htrace : WordTrace (prefixWord ++ tailWord_310681) baseStart_310681 baseEnd_310681 := by
    simpa [prefixWord, tailWord_310681, baseEnd_310681] using wordTrace_append hprefix tailTrace_310681
  have hstable : (prefixWord ++ tailWord_310681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310681).length < 2 ^ (prefixWord ++ tailWord_310681).sum := by decide
  have hdescent : baseEnd_310681 < baseStart_310681 := by decide
  rcases family_descends (prefixWord ++ tailWord_310681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310788 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_310788 : Nat := 118140960795 + 310788 * 2 ^ 59
def prefixEnd_310788 : Nat := 4983230072969 + 3 ^ 40 * 310788 * 2
def baseEnd_310788 : Nat := 70926055844282344098097

theorem tailTrace_310788 : CollatzResearch.WordTrace tailWord_310788 prefixEnd_310788 70926055844282344098097 := by
  unfold tailWord_310788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5667684799037814604862509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7556913065383752806483345 5667684799037814604862509)
  ·
    refine ⟨2125381799639180476823441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5667684799037814604862509 2125381799639180476823441)
    ·
      refine ⟨1594036349729385357617581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2125381799639180476823441 1594036349729385357617581)
      ·
        refine ⟨597763631148519509106593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1594036349729385357617581 597763631148519509106593)
        ·
          refine ⟨448322723361389631829945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597763631148519509106593 448322723361389631829945)
          ·
            refine ⟨336242042521042223872459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448322723361389631829945 336242042521042223872459)
            ·
              refine ⟨504363063781563335808689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336242042521042223872459 504363063781563335808689)
              ·
                refine ⟨378272297836172501856517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504363063781563335808689 378272297836172501856517)
                ·
                  refine ⟨70926055844282344098097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 378272297836172501856517 70926055844282344098097)
                  ·
                    rfl

theorem cell21_310788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_310788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310788 prefixEnd_310788 := by exact prefixLift 310788
  have htrace : WordTrace (prefixWord ++ tailWord_310788) baseStart_310788 baseEnd_310788 := by
    simpa [prefixWord, tailWord_310788, baseEnd_310788] using wordTrace_append hprefix tailTrace_310788
  have hstable : (prefixWord ++ tailWord_310788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310788).length < 2 ^ (prefixWord ++ tailWord_310788).sum := by decide
  have hdescent : baseEnd_310788 < baseStart_310788 := by decide
  rcases family_descends (prefixWord ++ tailWord_310788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310830 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_310830 : Nat := 118140960795 + 310830 * 2 ^ 59
def prefixEnd_310830 : Nat := 4983230072969 + 3 ^ 40 * 310830 * 2
def baseEnd_310830 : Nat := 70935640816499604398011

theorem tailTrace_310830 : CollatzResearch.WordTrace tailWord_310830 prefixEnd_310830 70935640816499604398011 := by
  unfold tailWord_310830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417112682990433797844243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7557934309282313588502629 1417112682990433797844243)
  ·
    refine ⟨2125669024485650696766365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1417112682990433797844243 2125669024485650696766365)
    ·
      refine ⟨797125884182119011287387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2125669024485650696766365 797125884182119011287387)
      ·
        refine ⟨1195688826273178516931081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797125884182119011287387 1195688826273178516931081)
        ·
          refine ⟨896766619704883887698311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1195688826273178516931081 896766619704883887698311)
          ·
            refine ⟨1345149929557325831547467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896766619704883887698311 1345149929557325831547467)
            ·
              refine ⟨2017724894335988747321201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345149929557325831547467 2017724894335988747321201)
              ·
                refine ⟨1513293670751991560490901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2017724894335988747321201 1513293670751991560490901)
                ·
                  refine ⟨70935640816499604398011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1513293670751991560490901 70935640816499604398011)
                  ·
                    rfl

theorem cell21_310830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_310830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310830 prefixEnd_310830 := by exact prefixLift 310830
  have htrace : WordTrace (prefixWord ++ tailWord_310830) baseStart_310830 baseEnd_310830 := by
    simpa [prefixWord, tailWord_310830, baseEnd_310830] using wordTrace_append hprefix tailTrace_310830
  have hstable : (prefixWord ++ tailWord_310830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310830).length < 2 ^ (prefixWord ++ tailWord_310830).sum := by decide
  have hdescent : baseEnd_310830 < baseStart_310830 := by decide
  rcases family_descends (prefixWord ++ tailWord_310830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310909 : List Nat := [1, 4, 1, 1, 4, 1, 4, 2, 3]
def baseStart_310909 : Nat := 118140960795 + 310909 * 2 ^ 59
def prefixEnd_310909 : Nat := 4983230072969 + 3 ^ 40 * 310909 * 2
def baseEnd_310909 : Nat := 70953669692813022581183

theorem tailTrace_310909 : CollatzResearch.WordTrace tailWord_310909 prefixEnd_310909 70953669692813022581183 := by
  unfold tailWord_310909
  simp only [CollatzResearch.WordTrace]
  refine ⟨11339782830637266874879781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7559855220424844583253187 11339782830637266874879781)
  ·
    refine ⟨2126209280744487539039959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11339782830637266874879781 2126209280744487539039959)
    ·
      refine ⟨3189313921116731308559939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126209280744487539039959 3189313921116731308559939)
      ·
        refine ⟨4783970881675096962839909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189313921116731308559939 4783970881675096962839909)
        ·
          refine ⟨896994540314080680532483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4783970881675096962839909 896994540314080680532483)
          ·
            refine ⟨1345491810471121020798725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896994540314080680532483 1345491810471121020798725)
            ·
              refine ⟨252279714463335191399761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1345491810471121020798725 252279714463335191399761)
              ·
                refine ⟨189209785847501393549821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252279714463335191399761 189209785847501393549821)
                ·
                  refine ⟨70953669692813022581183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189209785847501393549821 70953669692813022581183)
                  ·
                    rfl

theorem cell21_310909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_310909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_310909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_310909 prefixEnd_310909 := by exact prefixLift 310909
  have htrace : WordTrace (prefixWord ++ tailWord_310909) baseStart_310909 baseEnd_310909 := by
    simpa [prefixWord, tailWord_310909, baseEnd_310909] using wordTrace_append hprefix tailTrace_310909
  have hstable : (prefixWord ++ tailWord_310909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310909).length < 2 ^ (prefixWord ++ tailWord_310909).sum := by decide
  have hdescent : baseEnd_310909 < baseStart_310909 := by decide
  rcases family_descends (prefixWord ++ tailWord_310909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311027 : List Nat := [1, 1, 1, 2, 2, 3, 2, 6, 3]
def baseStart_311027 : Nat := 118140960795 + 311027 * 2 ^ 59
def prefixEnd_311027 : Nat := 4983230072969 + 3 ^ 40 * 311027 * 2
def baseEnd_311027 : Nat := 70980598900471039614275

theorem tailTrace_311027 : CollatzResearch.WordTrace tailWord_311027 prefixEnd_311027 70980598900471039614275 := by
  unfold tailWord_311027
  simp only [CollatzResearch.WordTrace]
  refine ⟨11344086644209773027675335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7562724429473182018450223 11344086644209773027675335)
  ·
    refine ⟨17016129966314659541513003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11344086644209773027675335 17016129966314659541513003)
    ·
      refine ⟨25524194949471989312269505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17016129966314659541513003 25524194949471989312269505)
      ·
        refine ⟨19143146212103991984202129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25524194949471989312269505 19143146212103991984202129)
        ·
          refine ⟨14357359659077993988151597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19143146212103991984202129 14357359659077993988151597)
          ·
            refine ⟨5384009872154247745556849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14357359659077993988151597 5384009872154247745556849)
            ·
              refine ⟨4038007404115685809167637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5384009872154247745556849 4038007404115685809167637)
              ·
                refine ⟨189281597067922772304733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4038007404115685809167637 189281597067922772304733)
                ·
                  refine ⟨70980598900471039614275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189281597067922772304733 70980598900471039614275)
                  ·
                    rfl

theorem cell21_311027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 3].length) (baseStart_311027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311027 prefixEnd_311027 := by exact prefixLift 311027
  have htrace : WordTrace (prefixWord ++ tailWord_311027) baseStart_311027 baseEnd_311027 := by
    simpa [prefixWord, tailWord_311027, baseEnd_311027] using wordTrace_append hprefix tailTrace_311027
  have hstable : (prefixWord ++ tailWord_311027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311027).length < 2 ^ (prefixWord ++ tailWord_311027).sum := by decide
  have hdescent : baseEnd_311027 < baseStart_311027 := by decide
  rcases family_descends (prefixWord ++ tailWord_311027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311103 : List Nat := [1, 1, 2, 2, 6, 1, 1, 2, 5]
def baseStart_311103 : Nat := 118140960795 + 311103 * 2 ^ 59
def prefixEnd_311103 : Nat := 4983230072969 + 3 ^ 40 * 311103 * 2
def baseEnd_311103 : Nat := 70997943135911796347453

theorem tailTrace_311103 : CollatzResearch.WordTrace tailWord_311103 prefixEnd_311103 70997943135911796347453 := by
  unfold tailWord_311103
  simp only [CollatzResearch.WordTrace]
  refine ⟨11346858591934438007441963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7564572394622958671627975 11346858591934438007441963)
  ·
    refine ⟨17020287887901657011162945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11346858591934438007441963 17020287887901657011162945)
    ·
      refine ⟨12765215915926242758372209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17020287887901657011162945 12765215915926242758372209)
      ·
        refine ⟨9573911936944682068779157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12765215915926242758372209 9573911936944682068779157)
        ·
          refine ⟨448777122044281971974023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9573911936944682068779157 448777122044281971974023)
          ·
            refine ⟨673165683066422957961035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448777122044281971974023 673165683066422957961035)
            ·
              refine ⟨1009748524599634436941553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673165683066422957961035 1009748524599634436941553)
              ·
                refine ⟨757311393449725827706165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009748524599634436941553 757311393449725827706165)
                ·
                  refine ⟨70997943135911796347453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 757311393449725827706165 70997943135911796347453)
                  ·
                    rfl

theorem cell21_311103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 5].length) (baseStart_311103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311103 prefixEnd_311103 := by exact prefixLift 311103
  have htrace : WordTrace (prefixWord ++ tailWord_311103) baseStart_311103 baseEnd_311103 := by
    simpa [prefixWord, tailWord_311103, baseEnd_311103] using wordTrace_append hprefix tailTrace_311103
  have hstable : (prefixWord ++ tailWord_311103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311103).length < 2 ^ (prefixWord ++ tailWord_311103).sum := by decide
  have hdescent : baseEnd_311103 < baseStart_311103 := by decide
  rcases family_descends (prefixWord ++ tailWord_311103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311162 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_311162 : Nat := 118140960795 + 311162 * 2 ^ 59
def prefixEnd_311162 : Nat := 4983230072969 + 3 ^ 40 * 311162 * 2
def baseEnd_311162 : Nat := 71011407739740804863999

theorem tailTrace_311162 : CollatzResearch.WordTrace tailWord_311162 prefixEnd_311162 71011407739740804863999 := by
  unfold tailWord_311162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837252624680172770959935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7566006999147127389226493 2837252624680172770959935)
  ·
    refine ⟨4255878937020259156439903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2837252624680172770959935 4255878937020259156439903)
    ·
      refine ⟨6383818405530388734659855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4255878937020259156439903 6383818405530388734659855)
      ·
        refine ⟨9575727608295583101989783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6383818405530388734659855 9575727608295583101989783)
        ·
          refine ⟨14363591412443374652984675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9575727608295583101989783 14363591412443374652984675)
          ·
            refine ⟨21545387118665061979477013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14363591412443374652984675 21545387118665061979477013)
            ·
              refine ⟨1009940021187424780287985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21545387118665061979477013 1009940021187424780287985)
              ·
                refine ⟨757455015890568585215989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009940021187424780287985 757455015890568585215989)
                ·
                  refine ⟨71011407739740804863999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 757455015890568585215989 71011407739740804863999)
                  ·
                    rfl

theorem cell21_311162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_311162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311162 prefixEnd_311162 := by exact prefixLift 311162
  have htrace : WordTrace (prefixWord ++ tailWord_311162) baseStart_311162 baseEnd_311162 := by
    simpa [prefixWord, tailWord_311162, baseEnd_311162] using wordTrace_append hprefix tailTrace_311162
  have hstable : (prefixWord ++ tailWord_311162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311162).length < 2 ^ (prefixWord ++ tailWord_311162).sum := by decide
  have hdescent : baseEnd_311162 < baseStart_311162 := by decide
  rcases family_descends (prefixWord ++ tailWord_311162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311182 : List Nat := [4, 1, 1, 5, 2, 1, 7]
def baseStart_311182 : Nat := 118140960795 + 311182 * 2 ^ 59
def prefixEnd_311182 : Nat := 4983230072969 + 3 ^ 40 * 311182 * 2
def baseEnd_311182 : Nat := 7890663556913912725625

theorem tailTrace_311182 : CollatzResearch.WordTrace tailWord_311182 prefixEnd_311182 7890663556913912725625 := by
  unfold tailWord_311182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1418717494831029312445975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7566493305765489666378533 1418717494831029312445975)
  ·
    refine ⟨2128076242246543968668963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1418717494831029312445975 2128076242246543968668963)
    ·
      refine ⟨3192114363369815953003445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128076242246543968668963 3192114363369815953003445)
      ·
        refine ⟨299260721565920245594073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3192114363369815953003445 299260721565920245594073)
        ·
          refine ⟨224445541174440184195555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299260721565920245594073 224445541174440184195555)
          ·
            refine ⟨336668311761660276293333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224445541174440184195555 336668311761660276293333)
            ·
              refine ⟨7890663556913912725625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 336668311761660276293333 7890663556913912725625)
              ·
                rfl

theorem cell21_311182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 7].length) (baseStart_311182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311182 prefixEnd_311182 := by exact prefixLift 311182
  have htrace : WordTrace (prefixWord ++ tailWord_311182) baseStart_311182 baseEnd_311182 := by
    simpa [prefixWord, tailWord_311182, baseEnd_311182] using wordTrace_append hprefix tailTrace_311182
  have hstable : (prefixWord ++ tailWord_311182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311182).length < 2 ^ (prefixWord ++ tailWord_311182).sum := by decide
  have hdescent : baseEnd_311182 < baseStart_311182 := by decide
  rcases family_descends (prefixWord ++ tailWord_311182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311196 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_311196 : Nat := 118140960795 + 311196 * 2 ^ 59
def prefixEnd_311196 : Nat := 4983230072969 + 3 ^ 40 * 311196 * 2
def baseEnd_311196 : Nat := 71019167002964301297263

theorem tailTrace_311196 : CollatzResearch.WordTrace tailWord_311196 prefixEnd_311196 71019167002964301297263 := by
  unfold tailWord_311196
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675125290298757445288721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7566833720398343260384961 5675125290298757445288721)
  ·
    refine ⟨4256343967724068083966541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5675125290298757445288721 4256343967724068083966541)
    ·
      refine ⟨1596128987896525531487453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4256343967724068083966541 1596128987896525531487453)
      ·
        refine ⟨598548370461197074307795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1596128987896525531487453 598548370461197074307795)
        ·
          refine ⟨897822555691795611461693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598548370461197074307795 897822555691795611461693)
          ·
            refine ⟨336683458384423354298135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 897822555691795611461693 336683458384423354298135)
            ·
              refine ⟨505025187576635031447203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336683458384423354298135 505025187576635031447203)
              ·
                refine ⟨757537781364952547170805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505025187576635031447203 757537781364952547170805)
                ·
                  refine ⟨71019167002964301297263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 757537781364952547170805 71019167002964301297263)
                  ·
                    rfl

theorem cell21_311196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_311196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311196 prefixEnd_311196 := by exact prefixLift 311196
  have htrace : WordTrace (prefixWord ++ tailWord_311196) baseStart_311196 baseEnd_311196 := by
    simpa [prefixWord, tailWord_311196, baseEnd_311196] using wordTrace_append hprefix tailTrace_311196
  have hstable : (prefixWord ++ tailWord_311196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311196).length < 2 ^ (prefixWord ++ tailWord_311196).sum := by decide
  have hdescent : baseEnd_311196 < baseStart_311196 := by decide
  rcases family_descends (prefixWord ++ tailWord_311196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311255 : List Nat := [1, 1, 3, 2, 1, 1, 5, 4, 3]
def baseStart_311255 : Nat := 118140960795 + 311255 * 2 ^ 59
def prefixEnd_311255 : Nat := 4983230072969 + 3 ^ 40 * 311255 * 2
def baseEnd_311255 : Nat := 71032631606793309813809

theorem tailTrace_311255 : CollatzResearch.WordTrace tailWord_311255 prefixEnd_311255 71032631606793309813809 := by
  unfold tailWord_311255
  simp only [CollatzResearch.WordTrace]
  refine ⟨11352402487383767966975219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7568268324922511977983479 11352402487383767966975219)
  ·
    refine ⟨17028603731075651950462829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11352402487383767966975219 17028603731075651950462829)
    ·
      refine ⟨6385726399153369481423561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17028603731075651950462829 6385726399153369481423561)
      ·
        refine ⟨4789294799365027111067671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6385726399153369481423561 4789294799365027111067671)
        ·
          refine ⟨7183942199047540666601507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4789294799365027111067671 7183942199047540666601507)
          ·
            refine ⟨10775913298571310999902261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7183942199047540666601507 10775913298571310999902261)
            ·
              refine ⟨1010241871741060406240837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10775913298571310999902261 1010241871741060406240837)
              ·
                refine ⟨189420350951448826170157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1010241871741060406240837 189420350951448826170157)
                ·
                  refine ⟨71032631606793309813809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189420350951448826170157 71032631606793309813809)
                  ·
                    rfl

theorem cell21_311255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 3].length) (baseStart_311255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311255 prefixEnd_311255 := by exact prefixLift 311255
  have htrace : WordTrace (prefixWord ++ tailWord_311255) baseStart_311255 baseEnd_311255 := by
    simpa [prefixWord, tailWord_311255, baseEnd_311255] using wordTrace_append hprefix tailTrace_311255
  have hstable : (prefixWord ++ tailWord_311255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311255).length < 2 ^ (prefixWord ++ tailWord_311255).sum := by decide
  have hdescent : baseEnd_311255 < baseStart_311255 := by decide
  rcases family_descends (prefixWord ++ tailWord_311255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311421 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 4]
def baseStart_311421 : Nat := 118140960795 + 311421 * 2 ^ 59
def prefixEnd_311421 : Nat := 4983230072969 + 3 ^ 40 * 311421 * 2
def baseEnd_311421 : Nat := 71070515068413910046803

theorem tailTrace_311421 : CollatzResearch.WordTrace tailWord_311421 prefixEnd_311421 71070515068413910046803 := by
  unfold tailWord_311421
  simp only [CollatzResearch.WordTrace]
  refine ⟨11358457004782378317518117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7572304669854918878345411 11358457004782378317518117)
  ·
    refine ⟨2129710688396695934534647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11358457004782378317518117 2129710688396695934534647)
    ·
      refine ⟨3194566032595043901801971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2129710688396695934534647 3194566032595043901801971)
      ·
        refine ⟨4791849048892565852702957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3194566032595043901801971 4791849048892565852702957)
        ·
          refine ⟨1796943393334712194763609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4791849048892565852702957 1796943393334712194763609)
          ·
            refine ⟨1347707545001034146072707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1796943393334712194763609 1347707545001034146072707)
            ·
              refine ⟨2021561317501551219109061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347707545001034146072707 2021561317501551219109061)
              ·
                refine ⟨379042747031540853582949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2021561317501551219109061 379042747031540853582949)
                ·
                  refine ⟨71070515068413910046803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 379042747031540853582949 71070515068413910046803)
                  ·
                    rfl

theorem cell21_311421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_311421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311421 prefixEnd_311421 := by exact prefixLift 311421
  have htrace : WordTrace (prefixWord ++ tailWord_311421) baseStart_311421 baseEnd_311421 := by
    simpa [prefixWord, tailWord_311421, baseEnd_311421] using wordTrace_append hprefix tailTrace_311421
  have hstable : (prefixWord ++ tailWord_311421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311421).length < 2 ^ (prefixWord ++ tailWord_311421).sum := by decide
  have hdescent : baseEnd_311421 < baseStart_311421 := by decide
  rcases family_descends (prefixWord ++ tailWord_311421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311452 : List Nat := [2, 2, 3, 2, 1, 1, 5, 5]
def baseStart_311452 : Nat := 118140960795 + 311452 * 2 ^ 59
def prefixEnd_311452 : Nat := 4983230072969 + 3 ^ 40 * 311452 * 2
def baseEnd_311452 : Nat := 23692529896921581676691

theorem tailTrace_311452 : CollatzResearch.WordTrace tailWord_311452 prefixEnd_311452 23692529896921581676691 := by
  unfold tailWord_311452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5679793833835035305948305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7573058445113380407931073 5679793833835035305948305)
  ·
    refine ⟨4259845375376276479461229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5679793833835035305948305 4259845375376276479461229)
    ·
      refine ⟨1597442015766103679797961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4259845375376276479461229 1597442015766103679797961)
      ·
        refine ⟨1198081511824577759848471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1597442015766103679797961 1198081511824577759848471)
        ·
          refine ⟨1797122267736866639772707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198081511824577759848471 1797122267736866639772707)
          ·
            refine ⟨2695683401605299959659061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797122267736866639772707 2695683401605299959659061)
            ·
              refine ⟨252720318900496871218037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2695683401605299959659061 252720318900496871218037)
              ·
                refine ⟨23692529896921581676691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252720318900496871218037 23692529896921581676691)
                ·
                  rfl

theorem cell21_311452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 5].length) (baseStart_311452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311452 prefixEnd_311452 := by exact prefixLift 311452
  have htrace : WordTrace (prefixWord ++ tailWord_311452) baseStart_311452 baseEnd_311452 := by
    simpa [prefixWord, tailWord_311452, baseEnd_311452] using wordTrace_append hprefix tailTrace_311452
  have hstable : (prefixWord ++ tailWord_311452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311452).length < 2 ^ (prefixWord ++ tailWord_311452).sum := by decide
  have hdescent : baseEnd_311452 < baseStart_311452 := by decide
  rcases family_descends (prefixWord ++ tailWord_311452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311480 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_311480 : Nat := 118140960795 + 311480 * 2 ^ 59
def prefixEnd_311480 : Nat := 4983230072969 + 3 ^ 40 * 311480 * 2
def baseEnd_311480 : Nat := 71083979672242918563349

theorem tailTrace_311480 : CollatzResearch.WordTrace tailWord_311480 prefixEnd_311480 71083979672242918563349 := by
  unfold tailWord_311480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5680304455784315696957947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7573739274379087595943929 5680304455784315696957947)
  ·
    refine ⟨8520456683676473545436921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5680304455784315696957947 8520456683676473545436921)
    ·
      refine ⟨6390342512757355159077691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8520456683676473545436921 6390342512757355159077691)
      ·
        refine ⟨9585513769136032738616537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6390342512757355159077691 9585513769136032738616537)
        ·
          refine ⟨7189135326852024553962403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9585513769136032738616537 7189135326852024553962403)
          ·
            refine ⟨10783702990278036830943605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7189135326852024553962403 10783702990278036830943605)
            ·
              refine ⟨1010972155338565952900963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10783702990278036830943605 1010972155338565952900963)
              ·
                refine ⟨1516458233007848929351445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010972155338565952900963 1516458233007848929351445)
                ·
                  refine ⟨71083979672242918563349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1516458233007848929351445 71083979672242918563349)
                  ·
                    rfl

theorem cell21_311480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_311480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311480 prefixEnd_311480 := by exact prefixLift 311480
  have htrace : WordTrace (prefixWord ++ tailWord_311480) baseStart_311480 baseEnd_311480 := by
    simpa [prefixWord, tailWord_311480, baseEnd_311480] using wordTrace_append hprefix tailTrace_311480
  have hstable : (prefixWord ++ tailWord_311480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311480).length < 2 ^ (prefixWord ++ tailWord_311480).sum := by decide
  have hdescent : baseEnd_311480 < baseStart_311480 := by decide
  rcases family_descends (prefixWord ++ tailWord_311480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311517 : List Nat := [1, 4, 3, 2, 1, 3, 1, 3, 3]
def baseStart_311517 : Nat := 118140960795 + 311517 * 2 ^ 59
def prefixEnd_311517 : Nat := 4983230072969 + 3 ^ 40 * 311517 * 2
def baseEnd_311517 : Nat := 71092423576339076446607

theorem tailTrace_311517 : CollatzResearch.WordTrace tailWord_311517 prefixEnd_311517 71092423576339076446607 := by
  unfold tailWord_311517
  simp only [CollatzResearch.WordTrace]
  refine ⟨11361958412434586713012805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7574638941623057808675203 11361958412434586713012805)
  ·
    refine ⟨2130367202331485008689901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11361958412434586713012805 2130367202331485008689901)
    ·
      refine ⟨798887700874306878258713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2130367202331485008689901 798887700874306878258713)
      ·
        refine ⟨599165775655730158694035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 798887700874306878258713 599165775655730158694035)
        ·
          refine ⟨898748663483595238041053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599165775655730158694035 898748663483595238041053)
          ·
            refine ⟨337030748806348214265395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 898748663483595238041053 337030748806348214265395)
            ·
              refine ⟨505546123209522321398093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337030748806348214265395 505546123209522321398093)
              ·
                refine ⟨189579796203570870524285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 505546123209522321398093 189579796203570870524285)
                ·
                  refine ⟨71092423576339076446607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189579796203570870524285 71092423576339076446607)
                  ·
                    rfl

theorem cell21_311517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_311517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311517 prefixEnd_311517 := by exact prefixLift 311517
  have htrace : WordTrace (prefixWord ++ tailWord_311517) baseStart_311517 baseEnd_311517 := by
    simpa [prefixWord, tailWord_311517, baseEnd_311517] using wordTrace_append hprefix tailTrace_311517
  have hstable : (prefixWord ++ tailWord_311517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311517).length < 2 ^ (prefixWord ++ tailWord_311517).sum := by decide
  have hdescent : baseEnd_311517 < baseStart_311517 := by decide
  rcases family_descends (prefixWord ++ tailWord_311517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311604 : List Nat := [2, 5, 1, 1, 1, 2, 3, 6]
def baseStart_311604 : Nat := 118140960795 + 311604 * 2 ^ 59
def prefixEnd_311604 : Nat := 4983230072969 + 3 ^ 40 * 311604 * 2
def baseEnd_311604 : Nat := 23704092720548752832143

theorem tailTrace_311604 : CollatzResearch.WordTrace tailWord_311604 prefixEnd_311604 23704092720548752832143 := by
  unfold tailWord_311604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682565781559700285714933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7576754375412933714286577 5682565781559700285714933)
  ·
    refine ⟨532740542021221901785775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5682565781559700285714933 532740542021221901785775)
    ·
      refine ⟨799110813031832852678663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 532740542021221901785775 799110813031832852678663)
      ·
        refine ⟨1198666219547749279017995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799110813031832852678663 1198666219547749279017995)
        ·
          refine ⟨1797999329321623918526993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198666219547749279017995 1797999329321623918526993)
          ·
            refine ⟨1348499496991217938895245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797999329321623918526993 1348499496991217938895245)
            ·
              refine ⟨505687311371706727085717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1348499496991217938895245 505687311371706727085717)
              ·
                refine ⟨23704092720548752832143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 505687311371706727085717 23704092720548752832143)
                ·
                  rfl

theorem cell21_311604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 6].length) (baseStart_311604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311604 prefixEnd_311604 := by exact prefixLift 311604
  have htrace : WordTrace (prefixWord ++ tailWord_311604) baseStart_311604 baseEnd_311604 := by
    simpa [prefixWord, tailWord_311604, baseEnd_311604] using wordTrace_append hprefix tailTrace_311604
  have hstable : (prefixWord ++ tailWord_311604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311604).length < 2 ^ (prefixWord ++ tailWord_311604).sum := by decide
  have hdescent : baseEnd_311604 < baseStart_311604 := by decide
  rcases family_descends (prefixWord ++ tailWord_311604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311666 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_311666 : Nat := 118140960795 + 311666 * 2 ^ 59
def prefixEnd_311666 : Nat := 4983230072969 + 3 ^ 40 * 311666 * 2
def baseEnd_311666 : Nat := 71126427406347928462969

theorem tailTrace_311666 : CollatzResearch.WordTrace tailWord_311666 prefixEnd_311666 71126427406347928462969 := by
  unfold tailWord_311666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841848222223696290046713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7578261925929856773457901 2841848222223696290046713)
  ·
    refine ⟨2131386166667772217535035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2841848222223696290046713 2131386166667772217535035)
    ·
      refine ⟨3197079250001658326302553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2131386166667772217535035 3197079250001658326302553)
      ·
        refine ⟨2397809437501243744726915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3197079250001658326302553 2397809437501243744726915)
        ·
          refine ⟨3596714156251865617090373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397809437501243744726915 3596714156251865617090373)
          ·
            refine ⟨674383904297224803204445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3596714156251865617090373 674383904297224803204445)
            ·
              refine ⟨252893964111459301201667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 674383904297224803204445 252893964111459301201667)
              ·
                refine ⟨379340946167188951802501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252893964111459301201667 379340946167188951802501)
                ·
                  refine ⟨71126427406347928462969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 379340946167188951802501 71126427406347928462969)
                  ·
                    rfl

theorem cell21_311666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_311666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311666 prefixEnd_311666 := by exact prefixLift 311666
  have htrace : WordTrace (prefixWord ++ tailWord_311666) baseStart_311666 baseEnd_311666 := by
    simpa [prefixWord, tailWord_311666, baseEnd_311666] using wordTrace_append hprefix tailTrace_311666
  have hstable : (prefixWord ++ tailWord_311666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311666).length < 2 ^ (prefixWord ++ tailWord_311666).sum := by decide
  have hdescent : baseEnd_311666 < baseStart_311666 := by decide
  rcases family_descends (prefixWord ++ tailWord_311666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311762 : List Nat := [3, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_311762 : Nat := 118140960795 + 311762 * 2 ^ 59
def prefixEnd_311762 : Nat := 4983230072969 + 3 ^ 40 * 311762 * 2
def baseEnd_311762 : Nat := 71148335914273094862773

theorem tailTrace_311762 : CollatzResearch.WordTrace tailWord_311762 prefixEnd_311762 71148335914273094862773 := by
  unfold tailWord_311762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842723574136748388920385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7580596197697995703787693 2842723574136748388920385)
  ·
    refine ⟨2132042680602561291690289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2842723574136748388920385 2132042680602561291690289)
    ·
      refine ⟨1599032010451920968767717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2132042680602561291690289 1599032010451920968767717)
      ·
        refine ⟨299818501959735181643947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1599032010451920968767717 299818501959735181643947)
        ·
          refine ⟨449727752939602772465921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299818501959735181643947 449727752939602772465921)
          ·
            refine ⟨337295814704702079349441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449727752939602772465921 337295814704702079349441)
            ·
              refine ⟨252971861028526559512081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337295814704702079349441 252971861028526559512081)
              ·
                refine ⟨189728895771394919634061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252971861028526559512081 189728895771394919634061)
                ·
                  refine ⟨71148335914273094862773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189728895771394919634061 71148335914273094862773)
                  ·
                    rfl

theorem cell21_311762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_311762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311762 prefixEnd_311762 := by exact prefixLift 311762
  have htrace : WordTrace (prefixWord ++ tailWord_311762) baseStart_311762 baseEnd_311762 := by
    simpa [prefixWord, tailWord_311762, baseEnd_311762] using wordTrace_append hprefix tailTrace_311762
  have hstable : (prefixWord ++ tailWord_311762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311762).length < 2 ^ (prefixWord ++ tailWord_311762).sum := by decide
  have hdescent : baseEnd_311762 < baseStart_311762 := by decide
  rcases family_descends (prefixWord ++ tailWord_311762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311815 : List Nat := [1, 1, 4, 3, 3, 1, 8]
def baseStart_311815 : Nat := 118140960795 + 311815 * 2 ^ 59
def prefixEnd_311815 : Nat := 4983230072969 + 3 ^ 40 * 311815 * 2
def baseEnd_311815 : Nat := 7906714581817420053259

theorem tailTrace_311815 : CollatzResearch.WordTrace tailWord_311815 prefixEnd_311815 7906714581817420053259 := by
  unfold tailWord_311815
  simp only [CollatzResearch.WordTrace]
  refine ⟨11372827365354983607360899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7581884910236655738240599 11372827365354983607360899)
  ·
    refine ⟨17059241048032475411041349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11372827365354983607360899 17059241048032475411041349)
    ·
      refine ⟨3198607696506089139570253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17059241048032475411041349 3198607696506089139570253)
      ·
        refine ⟨1199477886189783427338845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3198607696506089139570253 1199477886189783427338845)
        ·
          refine ⟨449804207321168785252067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1199477886189783427338845 449804207321168785252067)
          ·
            refine ⟨674706310981753177878101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449804207321168785252067 674706310981753177878101)
            ·
              refine ⟨7906714581817420053259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 674706310981753177878101 7906714581817420053259)
              ·
                rfl

theorem cell21_311815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 8].length) (baseStart_311815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311815 prefixEnd_311815 := by exact prefixLift 311815
  have htrace : WordTrace (prefixWord ++ tailWord_311815) baseStart_311815 baseEnd_311815 := by
    simpa [prefixWord, tailWord_311815, baseEnd_311815] using wordTrace_append hprefix tailTrace_311815
  have hstable : (prefixWord ++ tailWord_311815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311815).length < 2 ^ (prefixWord ++ tailWord_311815).sum := by decide
  have hdescent : baseEnd_311815 < baseStart_311815 := by decide
  rcases family_descends (prefixWord ++ tailWord_311815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311821 : List Nat := [1, 7, 1, 1, 1, 1, 2, 4, 3]
def baseStart_311821 : Nat := 118140960795 + 311821 * 2 ^ 59
def prefixEnd_311821 : Nat := 4983230072969 + 3 ^ 40 * 311821 * 2
def baseEnd_311821 : Nat := 71161800518102103379319

theorem tailTrace_311821 : CollatzResearch.WordTrace tailWord_311821 prefixEnd_311821 71161800518102103379319 := by
  unfold tailWord_311821
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373046203333246632079317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7582030802222164421386211 11373046203333246632079317)
  ·
    refine ⟨266555770390622967939359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11373046203333246632079317 266555770390622967939359)
    ·
      refine ⟨399833655585934451909039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266555770390622967939359 399833655585934451909039)
      ·
        refine ⟨599750483378901677863559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399833655585934451909039 599750483378901677863559)
        ·
          refine ⟨899625725068352516795339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599750483378901677863559 899625725068352516795339)
          ·
            refine ⟨1349438587602528775193009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899625725068352516795339 1349438587602528775193009)
            ·
              refine ⟨1012078940701896581394757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349438587602528775193009 1012078940701896581394757)
              ·
                refine ⟨189764801381605609011517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1012078940701896581394757 189764801381605609011517)
                ·
                  refine ⟨71161800518102103379319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189764801381605609011517 71161800518102103379319)
                  ·
                    rfl

theorem cell21_311821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_311821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311821 prefixEnd_311821 := by exact prefixLift 311821
  have htrace : WordTrace (prefixWord ++ tailWord_311821) baseStart_311821 baseEnd_311821 := by
    simpa [prefixWord, tailWord_311821, baseEnd_311821] using wordTrace_append hprefix tailTrace_311821
  have hstable : (prefixWord ++ tailWord_311821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311821).length < 2 ^ (prefixWord ++ tailWord_311821).sum := by decide
  have hdescent : baseEnd_311821 < baseStart_311821 := by decide
  rcases family_descends (prefixWord ++ tailWord_311821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311919 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 8]
def baseStart_311919 : Nat := 118140960795 + 311919 * 2 ^ 59
def prefixEnd_311919 : Nat := 4983230072969 + 3 ^ 40 * 311919 * 2
def baseEnd_311919 : Nat := 71184165453275710745785

theorem tailTrace_311919 : CollatzResearch.WordTrace tailWord_311919 prefixEnd_311919 71184165453275710745785 := by
  unfold tailWord_311919
  simp only [CollatzResearch.WordTrace]
  refine ⟨11376620556978209369146811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7584413704652139579431207 11376620556978209369146811)
  ·
    refine ⟨17064930835467314053720217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11376620556978209369146811 17064930835467314053720217)
    ·
      refine ⟨12798698126600485540290163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17064930835467314053720217 12798698126600485540290163)
      ·
        refine ⟨19198047189900728310435245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12798698126600485540290163 19198047189900728310435245)
        ·
          refine ⟨7199267696212773116413217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19198047189900728310435245 7199267696212773116413217)
          ·
            refine ⟨5399450772159579837309913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7199267696212773116413217 5399450772159579837309913)
            ·
              refine ⟨4049588079119684877982435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5399450772159579837309913 4049588079119684877982435)
              ·
                refine ⟨6074382118679527316973653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049588079119684877982435 6074382118679527316973653)
                ·
                  refine ⟨71184165453275710745785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6074382118679527316973653 71184165453275710745785)
                  ·
                    rfl

theorem cell21_311919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 8].length) (baseStart_311919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311919 prefixEnd_311919 := by exact prefixLift 311919
  have htrace : WordTrace (prefixWord ++ tailWord_311919) baseStart_311919 baseEnd_311919 := by
    simpa [prefixWord, tailWord_311919, baseEnd_311919] using wordTrace_append hprefix tailTrace_311919
  have hstable : (prefixWord ++ tailWord_311919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311919).length < 2 ^ (prefixWord ++ tailWord_311919).sum := by decide
  have hdescent : baseEnd_311919 < baseStart_311919 := by decide
  rcases family_descends (prefixWord ++ tailWord_311919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311936 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_311936 : Nat := 118140960795 + 311936 * 2 ^ 59
def prefixEnd_311936 : Nat := 4983230072969 + 3 ^ 40 * 311936 * 2
def baseEnd_311936 : Nat := 71188045084887458962417

theorem tailTrace_311936 : CollatzResearch.WordTrace tailWord_311936 prefixEnd_311936 71188045084887458962417 := by
  unfold tailWord_311936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5688620298958310636257831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7584827065277747515010441 5688620298958310636257831)
  ·
    refine ⟨8532930448437465954386747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5688620298958310636257831 8532930448437465954386747)
    ·
      refine ⟨12799395672656198931580121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8532930448437465954386747 12799395672656198931580121)
      ·
        refine ⟨9599546754492149198685091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12799395672656198931580121 9599546754492149198685091)
        ·
          refine ⟨14399320131738223798027637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9599546754492149198685091 14399320131738223798027637)
          ·
            refine ⟨1349936262350458481065091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14399320131738223798027637 1349936262350458481065091)
            ·
              refine ⟨2024904393525687721597637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349936262350458481065091 2024904393525687721597637)
              ·
                refine ⟨379669573786066447799557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2024904393525687721597637 379669573786066447799557)
                ·
                  refine ⟨71188045084887458962417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 379669573786066447799557 71188045084887458962417)
                  ·
                    rfl

theorem cell21_311936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_311936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311936 prefixEnd_311936 := by exact prefixLift 311936
  have htrace : WordTrace (prefixWord ++ tailWord_311936) baseStart_311936 baseEnd_311936 := by
    simpa [prefixWord, tailWord_311936, baseEnd_311936] using wordTrace_append hprefix tailTrace_311936
  have hstable : (prefixWord ++ tailWord_311936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311936).length < 2 ^ (prefixWord ++ tailWord_311936).sum := by decide
  have hdescent : baseEnd_311936 < baseStart_311936 := by decide
  rcases family_descends (prefixWord ++ tailWord_311936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311939 : List Nat := [1, 1, 1, 3, 3, 1, 6, 2, 3]
def baseStart_311939 : Nat := 118140960795 + 311939 * 2 ^ 59
def prefixEnd_311939 : Nat := 4983230072969 + 3 ^ 40 * 311939 * 2
def baseEnd_311939 : Nat := 71188729725760120412411

theorem tailTrace_311939 : CollatzResearch.WordTrace tailWord_311939 prefixEnd_311939 71188729725760120412411 := by
  unfold tailWord_311939
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377350016905752784874871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7584900011270501856583247 11377350016905752784874871)
  ·
    refine ⟨17066025025358629177312307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11377350016905752784874871 17066025025358629177312307)
    ·
      refine ⟨25599037538037943765968461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17066025025358629177312307 25599037538037943765968461)
      ·
        refine ⟨9599639076764228912238173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25599037538037943765968461 9599639076764228912238173)
        ·
          refine ⟨3599864653786585842089315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9599639076764228912238173 3599864653786585842089315)
          ·
            refine ⟨5399796980679878763133973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599864653786585842089315 5399796980679878763133973)
            ·
              refine ⟨253115483469369317021905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5399796980679878763133973 253115483469369317021905)
              ·
                refine ⟨189836612602026987766429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253115483469369317021905 189836612602026987766429)
                ·
                  refine ⟨71188729725760120412411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189836612602026987766429 71188729725760120412411)
                  ·
                    rfl

theorem cell21_311939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 3].length) (baseStart_311939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311939 prefixEnd_311939 := by exact prefixLift 311939
  have htrace : WordTrace (prefixWord ++ tailWord_311939) baseStart_311939 baseEnd_311939 := by
    simpa [prefixWord, tailWord_311939, baseEnd_311939] using wordTrace_append hprefix tailTrace_311939
  have hstable : (prefixWord ++ tailWord_311939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311939).length < 2 ^ (prefixWord ++ tailWord_311939).sum := by decide
  have hdescent : baseEnd_311939 < baseStart_311939 := by decide
  rcases family_descends (prefixWord ++ tailWord_311939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311998 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_311998 : Nat := 118140960795 + 311998 * 2 ^ 59
def prefixEnd_311998 : Nat := 4983230072969 + 3 ^ 40 * 311998 * 2
def baseEnd_311998 : Nat := 71202194329589128928957

theorem tailTrace_311998 : CollatzResearch.WordTrace tailWord_311998 prefixEnd_311998 71202194329589128928957 := by
  unfold tailWord_311998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1422437740461500732659081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7586334615794670574181765 1422437740461500732659081)
  ·
    refine ⟨1066828305346125549494311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1422437740461500732659081 1066828305346125549494311)
    ·
      refine ⟨1600242458019188324241467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066828305346125549494311 1600242458019188324241467)
      ·
        refine ⟨2400363687028782486362201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1600242458019188324241467 2400363687028782486362201)
        ·
          refine ⟨1800272765271586864771651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2400363687028782486362201 1800272765271586864771651)
          ·
            refine ⟨2700409147907380297157477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800272765271586864771651 2700409147907380297157477)
            ·
              refine ⟨506326715232633805717027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2700409147907380297157477 506326715232633805717027)
              ·
                refine ⟨759490072848950708575541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506326715232633805717027 759490072848950708575541)
                ·
                  refine ⟨71202194329589128928957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 759490072848950708575541 71202194329589128928957)
                  ·
                    rfl

theorem cell21_311998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_311998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_311998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_311998 prefixEnd_311998 := by exact prefixLift 311998
  have htrace : WordTrace (prefixWord ++ tailWord_311998) baseStart_311998 baseEnd_311998 := by
    simpa [prefixWord, tailWord_311998, baseEnd_311998] using wordTrace_append hprefix tailTrace_311998
  have hstable : (prefixWord ++ tailWord_311998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311998).length < 2 ^ (prefixWord ++ tailWord_311998).sum := by decide
  have hdescent : baseEnd_311998 < baseStart_311998 := by decide
  rcases family_descends (prefixWord ++ tailWord_311998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312026 : List Nat := [3, 1, 1, 2, 2, 2, 3, 7]
def baseStart_312026 : Nat := 118140960795 + 312026 * 2 ^ 59
def prefixEnd_312026 : Nat := 4983230072969 + 3 ^ 40 * 312026 * 2
def baseEnd_312026 : Nat := 23736194770355767487411

theorem tailTrace_312026 : CollatzResearch.WordTrace tailWord_312026 prefixEnd_312026 23736194770355767487411 := by
  unfold tailWord_312026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2845130791897641660822983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7587015445060377762194621 2845130791897641660822983)
  ·
    refine ⟨4267696187846462491234475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2845130791897641660822983 4267696187846462491234475)
    ·
      refine ⟨6401544281769693736851713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4267696187846462491234475 6401544281769693736851713)
      ·
        refine ⟨4801158211327270302638785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6401544281769693736851713 4801158211327270302638785)
        ·
          refine ⟨3600868658495452726979089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4801158211327270302638785 3600868658495452726979089)
          ·
            refine ⟨2700651493871589545234317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3600868658495452726979089 2700651493871589545234317)
            ·
              refine ⟨1012744310201846079462869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2700651493871589545234317 1012744310201846079462869)
              ·
                refine ⟨23736194770355767487411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1012744310201846079462869 23736194770355767487411)
                ·
                  rfl

theorem cell21_312026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_312026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312026 prefixEnd_312026 := by exact prefixLift 312026
  have htrace : WordTrace (prefixWord ++ tailWord_312026) baseStart_312026 baseEnd_312026 := by
    simpa [prefixWord, tailWord_312026, baseEnd_312026] using wordTrace_append hprefix tailTrace_312026
  have hstable : (prefixWord ++ tailWord_312026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312026).length < 2 ^ (prefixWord ++ tailWord_312026).sum := by decide
  have hdescent : baseEnd_312026 < baseStart_312026 := by decide
  rcases family_descends (prefixWord ++ tailWord_312026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312164 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_312164 : Nat := 118140960795 + 312164 * 2 ^ 59
def prefixEnd_312164 : Nat := 4983230072969 + 3 ^ 40 * 312164 * 2
def baseEnd_312164 : Nat := 71240077791209729161951

theorem tailTrace_312164 : CollatzResearch.WordTrace tailWord_312164 prefixEnd_312164 71240077791209729161951 := by
  unfold tailWord_312164
  simp only [CollatzResearch.WordTrace]
  refine ⟨5692778220545308105907773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7590370960727077474543697 5692778220545308105907773)
  ·
    refine ⟨2134791832704490539715415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5692778220545308105907773 2134791832704490539715415)
    ·
      refine ⟨3202187749056735809573123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2134791832704490539715415 3202187749056735809573123)
      ·
        refine ⟨4803281623585103714359685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3202187749056735809573123 4803281623585103714359685)
        ·
          refine ⟨900615304422206946442441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4803281623585103714359685 900615304422206946442441)
          ·
            refine ⟨675461478316655209831831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 900615304422206946442441 675461478316655209831831)
            ·
              refine ⟨1013192217474982814747747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675461478316655209831831 1013192217474982814747747)
              ·
                refine ⟨1519788326212474222121621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013192217474982814747747 1519788326212474222121621)
                ·
                  refine ⟨71240077791209729161951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1519788326212474222121621 71240077791209729161951)
                  ·
                    rfl

theorem cell21_312164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_312164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312164 prefixEnd_312164 := by exact prefixLift 312164
  have htrace : WordTrace (prefixWord ++ tailWord_312164) baseStart_312164 baseEnd_312164 := by
    simpa [prefixWord, tailWord_312164, baseEnd_312164] using wordTrace_append hprefix tailTrace_312164
  have hstable : (prefixWord ++ tailWord_312164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312164).length < 2 ^ (prefixWord ++ tailWord_312164).sum := by decide
  have hdescent : baseEnd_312164 < baseStart_312164 := by decide
  rcases family_descends (prefixWord ++ tailWord_312164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312192 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_312192 : Nat := 118140960795 + 312192 * 2 ^ 59
def prefixEnd_312192 : Nat := 4983230072969 + 3 ^ 40 * 312192 * 2
def baseEnd_312192 : Nat := 71246467772687902695227

theorem tailTrace_312192 : CollatzResearch.WordTrace tailWord_312192 prefixEnd_312192 71246467772687902695227 := by
  unfold tailWord_312192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5693288842494588496917415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7591051789992784662556553 5693288842494588496917415)
  ·
    refine ⟨8539933263741882745376123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5693288842494588496917415 8539933263741882745376123)
    ·
      refine ⟨12809899895612824118064185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8539933263741882745376123 12809899895612824118064185)
      ·
        refine ⟨9607424921709618088548139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12809899895612824118064185 9607424921709618088548139)
        ·
          refine ⟨14411137382564427132822209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9607424921709618088548139 14411137382564427132822209)
          ·
            refine ⟨10808353036923320349616657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14411137382564427132822209 10808353036923320349616657)
            ·
              refine ⟨8106264777692490262212493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10808353036923320349616657 8106264777692490262212493)
              ·
                refine ⟨3039849291634683848329685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8106264777692490262212493 3039849291634683848329685)
                ·
                  refine ⟨71246467772687902695227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3039849291634683848329685 71246467772687902695227)
                  ·
                    rfl

theorem cell21_312192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_312192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312192 prefixEnd_312192 := by exact prefixLift 312192
  have htrace : WordTrace (prefixWord ++ tailWord_312192) baseStart_312192 baseEnd_312192 := by
    simpa [prefixWord, tailWord_312192, baseEnd_312192] using wordTrace_append hprefix tailTrace_312192
  have hstable : (prefixWord ++ tailWord_312192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312192).length < 2 ^ (prefixWord ++ tailWord_312192).sum := by decide
  have hdescent : baseEnd_312192 < baseStart_312192 := by decide
  rcases family_descends (prefixWord ++ tailWord_312192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312226 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_312226 : Nat := 118140960795 + 312226 * 2 ^ 59
def prefixEnd_312226 : Nat := 4983230072969 + 3 ^ 40 * 312226 * 2
def baseEnd_312226 : Nat := 71254227035911399128491

theorem tailTrace_312226 : CollatzResearch.WordTrace tailWord_312226 prefixEnd_312226 71254227035911399128491 := by
  unfold tailWord_312226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2846954441716500200143133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7591878511244000533715021 2846954441716500200143133)
  ·
    refine ⟨1067607915643687575053675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2846954441716500200143133 1067607915643687575053675)
    ·
      refine ⟨1601411873465531362580513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1067607915643687575053675 1601411873465531362580513)
      ·
        refine ⟨1201058905099148521935385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1601411873465531362580513 1201058905099148521935385)
        ·
          refine ⟨900794178824361391451539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1201058905099148521935385 900794178824361391451539)
          ·
            refine ⟨1351191268236542087177309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900794178824361391451539 1351191268236542087177309)
            ·
              refine ⟨506696725588703282691491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1351191268236542087177309 506696725588703282691491)
              ·
                refine ⟨760045088383054924037237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506696725588703282691491 760045088383054924037237)
                ·
                  refine ⟨71254227035911399128491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 760045088383054924037237 71254227035911399128491)
                  ·
                    rfl

theorem cell21_312226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_312226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312226 prefixEnd_312226 := by exact prefixLift 312226
  have htrace : WordTrace (prefixWord ++ tailWord_312226) baseStart_312226 baseEnd_312226 := by
    simpa [prefixWord, tailWord_312226, baseEnd_312226] using wordTrace_append hprefix tailTrace_312226
  have hstable : (prefixWord ++ tailWord_312226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312226).length < 2 ^ (prefixWord ++ tailWord_312226).sum := by decide
  have hdescent : baseEnd_312226 < baseStart_312226 := by decide
  rcases family_descends (prefixWord ++ tailWord_312226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312254 : List Nat := [4, 2, 1, 1, 1, 2, 1, 9]
def baseStart_312254 : Nat := 118140960795 + 312254 * 2 ^ 59
def prefixEnd_312254 : Nat := 4983230072969 + 3 ^ 40 * 312254 * 2
def baseEnd_312254 : Nat := 23753539005796524220589

theorem tailTrace_312254 : CollatzResearch.WordTrace tailWord_312254 prefixEnd_312254 23753539005796524220589 := by
  unfold tailWord_312254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423604876345570197823977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7592559340509707721727877 1423604876345570197823977)
  ·
    refine ⟨1067703657259177648367983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1423604876345570197823977 1067703657259177648367983)
    ·
      refine ⟨1601555485888766472551975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1067703657259177648367983 1601555485888766472551975)
      ·
        refine ⟨2402333228833149708827963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601555485888766472551975 2402333228833149708827963)
        ·
          refine ⟨3603499843249724563241945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402333228833149708827963 3603499843249724563241945)
          ·
            refine ⟨2702624882437293422431459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3603499843249724563241945 2702624882437293422431459)
            ·
              refine ⟨4053937323655940133647189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702624882437293422431459 4053937323655940133647189)
              ·
                refine ⟨23753539005796524220589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4053937323655940133647189 23753539005796524220589)
                ·
                  rfl

theorem cell21_312254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_312254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312254 prefixEnd_312254 := by exact prefixLift 312254
  have htrace : WordTrace (prefixWord ++ tailWord_312254) baseStart_312254 baseEnd_312254 := by
    simpa [prefixWord, tailWord_312254, baseEnd_312254] using wordTrace_append hprefix tailTrace_312254
  have hstable : (prefixWord ++ tailWord_312254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312254).length < 2 ^ (prefixWord ++ tailWord_312254).sum := by decide
  have hdescent : baseEnd_312254 < baseStart_312254 := by decide
  rcases family_descends (prefixWord ++ tailWord_312254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312277 : List Nat := [1, 3, 2, 3, 4, 1, 2, 2, 3]
def baseStart_312277 : Nat := 118140960795 + 312277 * 2 ^ 59
def prefixEnd_312277 : Nat := 4983230072969 + 3 ^ 40 * 312277 * 2
def baseEnd_312277 : Nat := 71265865930746643778387

theorem tailTrace_312277 : CollatzResearch.WordTrace tailWord_312277 prefixEnd_312277 71265865930746643778387 := by
  unfold tailWord_312277
  simp only [CollatzResearch.WordTrace]
  refine ⟨11389677889681236510679085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7593118593120824340452723 11389677889681236510679085)
  ·
    refine ⟨4271129208630463691504657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11389677889681236510679085 4271129208630463691504657)
    ·
      refine ⟨3203346906472847768628493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4271129208630463691504657 3203346906472847768628493)
      ·
        refine ⟨1201255089927317913235685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3203346906472847768628493 1201255089927317913235685)
        ·
          refine ⟨225235329361372108731691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1201255089927317913235685 225235329361372108731691)
          ·
            refine ⟨337852994042058163097537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225235329361372108731691 337852994042058163097537)
            ·
              refine ⟨253389745531543622323153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337852994042058163097537 253389745531543622323153)
              ·
                refine ⟨190042309148657716742365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253389745531543622323153 190042309148657716742365)
                ·
                  refine ⟨71265865930746643778387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190042309148657716742365 71265865930746643778387)
                  ·
                    rfl

theorem cell21_312277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_312277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312277 prefixEnd_312277 := by exact prefixLift 312277
  have htrace : WordTrace (prefixWord ++ tailWord_312277) baseStart_312277 baseEnd_312277 := by
    simpa [prefixWord, tailWord_312277, baseEnd_312277] using wordTrace_append hprefix tailTrace_312277
  have hstable : (prefixWord ++ tailWord_312277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312277).length < 2 ^ (prefixWord ++ tailWord_312277).sum := by decide
  have hdescent : baseEnd_312277 < baseStart_312277 := by decide
  rcases family_descends (prefixWord ++ tailWord_312277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312302 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_312302 : Nat := 118140960795 + 312302 * 2 ^ 59
def prefixEnd_312302 : Nat := 4983230072969 + 3 ^ 40 * 312302 * 2
def baseEnd_312302 : Nat := 71271571271352155861669

theorem tailTrace_312302 : CollatzResearch.WordTrace tailWord_312302 prefixEnd_312302 71271571271352155861669 := by
  unfold tailWord_312302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423823714323833222542395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7593726476393777186892773 1423823714323833222542395)
  ·
    refine ⟨2135735571485749833813593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1423823714323833222542395 2135735571485749833813593)
    ·
      refine ⟨1601801678614312375360195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2135735571485749833813593 1601801678614312375360195)
      ·
        refine ⟨2402702517921468563040293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601801678614312375360195 2402702517921468563040293)
        ·
          refine ⟨450506722110275355570055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2402702517921468563040293 450506722110275355570055)
          ·
            refine ⟨675760083165413033355083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450506722110275355570055 675760083165413033355083)
            ·
              refine ⟨1013640124748119550032625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675760083165413033355083 1013640124748119550032625)
              ·
                refine ⟨760230093561089662524469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013640124748119550032625 760230093561089662524469)
                ·
                  refine ⟨71271571271352155861669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 760230093561089662524469 71271571271352155861669)
                  ·
                    rfl

theorem cell21_312302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_312302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312302 prefixEnd_312302 := by exact prefixLift 312302
  have htrace : WordTrace (prefixWord ++ tailWord_312302) baseStart_312302 baseEnd_312302 := by
    simpa [prefixWord, tailWord_312302, baseEnd_312302] using wordTrace_append hprefix tailTrace_312302
  have hstable : (prefixWord ++ tailWord_312302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312302).length < 2 ^ (prefixWord ++ tailWord_312302).sum := by decide
  have hdescent : baseEnd_312302 < baseStart_312302 := by decide
  rcases family_descends (prefixWord ++ tailWord_312302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312330 : List Nat := [3, 1, 2, 2, 3, 2, 8]
def baseStart_312330 : Nat := 118140960795 + 312330 * 2 ^ 59
def prefixEnd_312330 : Nat := 4983230072969 + 3 ^ 40 * 312330 * 2
def baseEnd_312330 : Nat := 7919773472536703266105

theorem tailTrace_312330 : CollatzResearch.WordTrace tailWord_312330 prefixEnd_312330 7919773472536703266105 := by
  unfold tailWord_312330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847902739622306640589611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7594407305659484374905629 2847902739622306640589611)
  ·
    refine ⟨4271854109433459960884417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2847902739622306640589611 4271854109433459960884417)
    ·
      refine ⟨3203890582075094970663313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4271854109433459960884417 3203890582075094970663313)
      ·
        refine ⟨2402917936556321227997485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3203890582075094970663313 2402917936556321227997485)
        ·
          refine ⟨901094226208620460499057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2402917936556321227997485 901094226208620460499057)
          ·
            refine ⟨675820669656465345374293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 901094226208620460499057 675820669656465345374293)
            ·
              refine ⟨7919773472536703266105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 675820669656465345374293 7919773472536703266105)
              ·
                rfl

theorem cell21_312330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 8].length) (baseStart_312330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312330 prefixEnd_312330 := by exact prefixLift 312330
  have htrace : WordTrace (prefixWord ++ tailWord_312330) baseStart_312330 baseEnd_312330 := by
    simpa [prefixWord, tailWord_312330, baseEnd_312330] using wordTrace_append hprefix tailTrace_312330
  have hstable : (prefixWord ++ tailWord_312330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312330).length < 2 ^ (prefixWord ++ tailWord_312330).sum := by decide
  have hdescent : baseEnd_312330 < baseStart_312330 := by decide
  rcases family_descends (prefixWord ++ tailWord_312330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312378 : List Nat := [3, 1, 1, 1, 3, 1, 5, 3, 3]
def baseStart_312378 : Nat := 118140960795 + 312378 * 2 ^ 59
def prefixEnd_312378 : Nat := 4983230072969 + 3 ^ 40 * 312378 * 2
def baseEnd_312378 : Nat := 71288915506792912594847

theorem tailTrace_312378 : CollatzResearch.WordTrace tailWord_312378 prefixEnd_312378 71288915506792912594847 := by
  unfold tailWord_312378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848340415578832690026447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7595574441543553840070525 2848340415578832690026447)
  ·
    refine ⟨4272510623368249035039671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2848340415578832690026447 4272510623368249035039671)
    ·
      refine ⟨6408765935052373552559507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272510623368249035039671 6408765935052373552559507)
      ·
        refine ⟨9613148902578560328839261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408765935052373552559507 9613148902578560328839261)
        ·
          refine ⟨3604930838466960123314723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9613148902578560328839261 3604930838466960123314723)
          ·
            refine ⟨5407396257700440184972085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3604930838466960123314723 5407396257700440184972085)
            ·
              refine ⟨506943399159416267341133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5407396257700440184972085 506943399159416267341133)
              ·
                refine ⟨190103774684781100252925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 506943399159416267341133 190103774684781100252925)
                ·
                  refine ⟨71288915506792912594847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190103774684781100252925 71288915506792912594847)
                  ·
                    rfl

theorem cell21_312378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_312378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312378 prefixEnd_312378 := by exact prefixLift 312378
  have htrace : WordTrace (prefixWord ++ tailWord_312378) baseStart_312378 baseEnd_312378 := by
    simpa [prefixWord, tailWord_312378, baseEnd_312378] using wordTrace_append hprefix tailTrace_312378
  have hstable : (prefixWord ++ tailWord_312378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312378).length < 2 ^ (prefixWord ++ tailWord_312378).sum := by decide
  have hdescent : baseEnd_312378 < baseStart_312378 := by decide
  rcases family_descends (prefixWord ++ tailWord_312378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312389 : List Nat := [1, 3, 1, 1, 1, 3, 11]
def baseStart_312389 : Nat := 118140960795 + 312389 * 2 ^ 59
def prefixEnd_312389 : Nat := 4983230072969 + 3 ^ 40 * 312389 * 2
def baseEnd_312389 : Nat := 7921269539628815323499

theorem tailTrace_312389 : CollatzResearch.WordTrace tailWord_312389 prefixEnd_312389 7921269539628815323499 := by
  unfold tailWord_312389
  simp only [CollatzResearch.WordTrace]
  refine ⟨11393762865275479638756221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7595841910183653092504147 11393762865275479638756221)
  ·
    refine ⟨4272661074478304864533583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11393762865275479638756221 4272661074478304864533583)
    ·
      refine ⟨6408991611717457296800375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272661074478304864533583 6408991611717457296800375)
      ·
        refine ⟨9613487417576185945200563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408991611717457296800375 9613487417576185945200563)
        ·
          refine ⟨14420231126364278917800845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9613487417576185945200563 14420231126364278917800845)
          ·
            refine ⟨5407586672386604594175317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14420231126364278917800845 5407586672386604594175317)
            ·
              refine ⟨7921269539628815323499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5407586672386604594175317 7921269539628815323499)
              ·
                rfl

theorem cell21_312389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 11].length) (baseStart_312389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312389 prefixEnd_312389 := by exact prefixLift 312389
  have htrace : WordTrace (prefixWord ++ tailWord_312389) baseStart_312389 baseEnd_312389 := by
    simpa [prefixWord, tailWord_312389, baseEnd_312389] using wordTrace_append hprefix tailTrace_312389
  have hstable : (prefixWord ++ tailWord_312389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312389).length < 2 ^ (prefixWord ++ tailWord_312389).sum := by decide
  have hdescent : baseEnd_312389 < baseStart_312389 := by decide
  rcases family_descends (prefixWord ++ tailWord_312389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312420 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 7]
def baseStart_312420 : Nat := 118140960795 + 312420 * 2 ^ 59
def prefixEnd_312420 : Nat := 4983230072969 + 3 ^ 40 * 312420 * 2
def baseEnd_312420 : Nat := 71298500479010172894761

theorem tailTrace_312420 : CollatzResearch.WordTrace tailWord_312420 prefixEnd_312420 71298500479010172894761 := by
  unfold tailWord_312420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5697446764081585966567357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7596595685442114622089809 5697446764081585966567357)
  ·
    refine ⟨2136542536530594737462759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5697446764081585966567357 2136542536530594737462759)
    ·
      refine ⟨3204813804795892106194139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136542536530594737462759 3204813804795892106194139)
      ·
        refine ⟨4807220707193838159291209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204813804795892106194139 4807220707193838159291209)
        ·
          refine ⟨3605415530395378619468407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4807220707193838159291209 3605415530395378619468407)
          ·
            refine ⟨5408123295593067929202611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3605415530395378619468407 5408123295593067929202611)
            ·
              refine ⟨8112184943389601893803917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5408123295593067929202611 8112184943389601893803917)
              ·
                refine ⟨3042069353771100710176469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8112184943389601893803917 3042069353771100710176469)
                ·
                  refine ⟨71298500479010172894761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3042069353771100710176469 71298500479010172894761)
                  ·
                    rfl

theorem cell21_312420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_312420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312420 prefixEnd_312420 := by exact prefixLift 312420
  have htrace : WordTrace (prefixWord ++ tailWord_312420) baseStart_312420 baseEnd_312420 := by
    simpa [prefixWord, tailWord_312420, baseEnd_312420] using wordTrace_append hprefix tailTrace_312420
  have hstable : (prefixWord ++ tailWord_312420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312420).length < 2 ^ (prefixWord ++ tailWord_312420).sum := by decide
  have hdescent : baseEnd_312420 < baseStart_312420 := by decide
  rcases family_descends (prefixWord ++ tailWord_312420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312502 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_312502 : Nat := 118140960795 + 312502 * 2 ^ 59
def prefixEnd_312502 : Nat := 4983230072969 + 3 ^ 40 * 312502 * 2
def baseEnd_312502 : Nat := 71317213996196252527927

theorem tailTrace_312502 : CollatzResearch.WordTrace tailWord_312502 prefixEnd_312502 71317213996196252527927 := by
  unfold tailWord_312502
  simp only [CollatzResearch.WordTrace]
  refine ⟨712367769616631246101235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7598589542577399958413173 712367769616631246101235)
  ·
    refine ⟨1068551654424946869151853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 712367769616631246101235 1068551654424946869151853)
    ·
      refine ⟨400706870409355075931945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1068551654424946869151853 400706870409355075931945)
      ·
        refine ⟨300530152807016306948959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400706870409355075931945 300530152807016306948959)
        ·
          refine ⟨450795229210524460423439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300530152807016306948959 450795229210524460423439)
          ·
            refine ⟨676192843815786690635159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450795229210524460423439 676192843815786690635159)
            ·
              refine ⟨1014289265723680035952739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676192843815786690635159 1014289265723680035952739)
              ·
                refine ⟨1521433898585520053929109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014289265723680035952739 1521433898585520053929109)
                ·
                  refine ⟨71317213996196252527927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1521433898585520053929109 71317213996196252527927)
                  ·
                    rfl

theorem cell21_312502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_312502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312502 prefixEnd_312502 := by exact prefixLift 312502
  have htrace : WordTrace (prefixWord ++ tailWord_312502) baseStart_312502 baseEnd_312502 := by
    simpa [prefixWord, tailWord_312502, baseEnd_312502] using wordTrace_append hprefix tailTrace_312502
  have hstable : (prefixWord ++ tailWord_312502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312502).length < 2 ^ (prefixWord ++ tailWord_312502).sum := by decide
  have hdescent : baseEnd_312502 < baseStart_312502 := by decide
  rcases family_descends (prefixWord ++ tailWord_312502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312665 : List Nat := [1, 2, 1, 2, 2, 2, 3, 5, 3]
def baseStart_312665 : Nat := 118140960795 + 312665 * 2 ^ 59
def prefixEnd_312665 : Nat := 4983230072969 + 3 ^ 40 * 312665 * 2
def baseEnd_312665 : Nat := 71354412816944191310927

theorem tailTrace_312665 : CollatzResearch.WordTrace tailWord_312665 prefixEnd_312665 71354412816944191310927 := by
  unfold tailWord_312665
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403829412275578775803449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7602552941517052517202299 11403829412275578775803449)
  ·
    refine ⟨8552872059206684081852587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11403829412275578775803449 8552872059206684081852587)
    ·
      refine ⟨12829308088810026122778881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8552872059206684081852587 12829308088810026122778881)
      ·
        refine ⟨9621981066607519592084161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12829308088810026122778881 9621981066607519592084161)
        ·
          refine ⟨7216485799955639694063121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9621981066607519592084161 7216485799955639694063121)
          ·
            refine ⟨5412364349966729770547341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7216485799955639694063121 5412364349966729770547341)
            ·
              refine ⟨2029636631237523663955253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5412364349966729770547341 2029636631237523663955253)
              ·
                refine ⟨190278434178517843495805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2029636631237523663955253 190278434178517843495805)
                ·
                  refine ⟨71354412816944191310927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190278434178517843495805 71354412816944191310927)
                  ·
                    rfl

theorem cell21_312665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_312665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312665 prefixEnd_312665 := by exact prefixLift 312665
  have htrace : WordTrace (prefixWord ++ tailWord_312665) baseStart_312665 baseEnd_312665 := by
    simpa [prefixWord, tailWord_312665, baseEnd_312665] using wordTrace_append hprefix tailTrace_312665
  have hstable : (prefixWord ++ tailWord_312665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312665).length < 2 ^ (prefixWord ++ tailWord_312665).sum := by decide
  have hdescent : baseEnd_312665 < baseStart_312665 := by decide
  rcases family_descends (prefixWord ++ tailWord_312665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312682 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 5]
def baseStart_312682 : Nat := 118140960795 + 312682 * 2 ^ 59
def prefixEnd_312682 : Nat := 4983230072969 + 3 ^ 40 * 312682 * 2
def baseEnd_312682 : Nat := 71358292448555939527559

theorem tailTrace_312682 : CollatzResearch.WordTrace tailWord_312682 prefixEnd_312682 71358292448555939527559 := by
  unfold tailWord_312682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2851112363303497669793075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7602966302142660452781533 2851112363303497669793075)
  ·
    refine ⟨4276668544955246504689613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2851112363303497669793075 4276668544955246504689613)
    ·
      refine ⟨1603750704358217439258605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4276668544955246504689613 1603750704358217439258605)
      ·
        refine ⟨601406514134331539721977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1603750704358217439258605 601406514134331539721977)
        ·
          refine ⟨451054885600748654791483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601406514134331539721977 451054885600748654791483)
          ·
            refine ⟨676582328401122982187225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451054885600748654791483 676582328401122982187225)
            ·
              refine ⟨507436746300842236640419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676582328401122982187225 507436746300842236640419)
              ·
                refine ⟨761155119451263354960629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507436746300842236640419 761155119451263354960629)
                ·
                  refine ⟨71358292448555939527559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 761155119451263354960629 71358292448555939527559)
                  ·
                    rfl

theorem cell21_312682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_312682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312682 prefixEnd_312682 := by exact prefixLift 312682
  have htrace : WordTrace (prefixWord ++ tailWord_312682) baseStart_312682 baseEnd_312682 := by
    simpa [prefixWord, tailWord_312682, baseEnd_312682] using wordTrace_append hprefix tailTrace_312682
  have hstable : (prefixWord ++ tailWord_312682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312682).length < 2 ^ (prefixWord ++ tailWord_312682).sum := by decide
  have hdescent : baseEnd_312682 < baseStart_312682 := by decide
  rcases family_descends (prefixWord ++ tailWord_312682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312702 : List Nat := [4, 2, 3, 2, 2, 1, 2, 5]
def baseStart_312702 : Nat := 118140960795 + 312702 * 2 ^ 59
def prefixEnd_312702 : Nat := 4983230072969 + 3 ^ 40 * 312702 * 2
def baseEnd_312702 : Nat := 23787618907013449731395

theorem tailTrace_312702 : CollatzResearch.WordTrace tailWord_312702 prefixEnd_312702 23787618907013449731395 := by
  unfold tailWord_312702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1425647364142691761862545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7603452608761022729933573 1425647364142691761862545)
  ·
    refine ⟨1069235523107018821396909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1425647364142691761862545 1069235523107018821396909)
    ·
      refine ⟨400963321165132058023841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1069235523107018821396909 400963321165132058023841)
      ·
        refine ⟨300722490873849043517881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400963321165132058023841 300722490873849043517881)
        ·
          refine ⟨225541868155386782638411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300722490873849043517881 225541868155386782638411)
          ·
            refine ⟨338312802233080173957617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225541868155386782638411 338312802233080173957617)
            ·
              refine ⟨253734601674810130468213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338312802233080173957617 253734601674810130468213)
              ·
                refine ⟨23787618907013449731395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253734601674810130468213 23787618907013449731395)
                ·
                  rfl

theorem cell21_312702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_312702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312702 prefixEnd_312702 := by exact prefixLift 312702
  have htrace : WordTrace (prefixWord ++ tailWord_312702) baseStart_312702 baseEnd_312702 := by
    simpa [prefixWord, tailWord_312702, baseEnd_312702] using wordTrace_append hprefix tailTrace_312702
  have hstable : (prefixWord ++ tailWord_312702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312702).length < 2 ^ (prefixWord ++ tailWord_312702).sum := by decide
  have hdescent : baseEnd_312702 < baseStart_312702 := by decide
  rcases family_descends (prefixWord ++ tailWord_312702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312890 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_312890 : Nat := 118140960795 + 312890 * 2 ^ 59
def prefixEnd_312890 : Nat := 4983230072969 + 3 ^ 40 * 312890 * 2
def baseEnd_312890 : Nat := 71405760882393800060467

theorem tailTrace_312890 : CollatzResearch.WordTrace tailWord_312890 prefixEnd_312890 71405760882393800060467 := by
  unfold tailWord_312890
  simp only [CollatzResearch.WordTrace]
  refine ⟨2853008959115110550686031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7608023890973628135162749 2853008959115110550686031)
  ·
    refine ⟨4279513438672665826029047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2853008959115110550686031 4279513438672665826029047)
    ·
      refine ⟨6419270158008998739043571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4279513438672665826029047 6419270158008998739043571)
      ·
        refine ⟨9628905237013498108565357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6419270158008998739043571 9628905237013498108565357)
        ·
          refine ⟨3610839463880061790712009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9628905237013498108565357 3610839463880061790712009)
          ·
            refine ⟨2708129597910046343034007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3610839463880061790712009 2708129597910046343034007)
            ·
              refine ⟨4062194396865069514551011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708129597910046343034007 4062194396865069514551011)
              ·
                refine ⟨6093291595297604271826517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4062194396865069514551011 6093291595297604271826517)
                ·
                  refine ⟨71405760882393800060467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6093291595297604271826517 71405760882393800060467)
                  ·
                    rfl

theorem cell21_312890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_312890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_312890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_312890 prefixEnd_312890 := by exact prefixLift 312890
  have htrace : WordTrace (prefixWord ++ tailWord_312890) baseStart_312890 baseEnd_312890 := by
    simpa [prefixWord, tailWord_312890, baseEnd_312890] using wordTrace_append hprefix tailTrace_312890
  have hstable : (prefixWord ++ tailWord_312890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312890).length < 2 ^ (prefixWord ++ tailWord_312890).sum := by decide
  have hdescent : baseEnd_312890 < baseStart_312890 := by decide
  rcases family_descends (prefixWord ++ tailWord_312890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
