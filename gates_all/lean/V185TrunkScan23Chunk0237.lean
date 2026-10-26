import V185TrunkScan23Chunk0236

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1402589 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1402589 : Nat := 118140960795 + 1402589 * 2 ^ 59
def prefixEnd_1402589 : Nat := 4983230072969 + 3 ^ 40 * 1402589 * 2
def baseEnd_1402589 : Nat := 720202317709118097787117

theorem tailTrace_1402589 : CollatzResearch.WordTrace tailWord_1402589 prefixEnd_1402589 720202317709118097787117 := by
  unfold tailWord_1402589
  simp only [CollatzResearch.WordTrace]
  refine ⟨51156623515667070975306821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34104415677111380650204547 51156623515667070975306821)
  ·
    refine ⟨9591866909187575807870029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51156623515667070975306821 9591866909187575807870029)
    ·
      refine ⟨3596950090945340927951261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9591866909187575807870029 3596950090945340927951261)
      ·
        refine ⟨1348856284104502847981723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3596950090945340927951261 1348856284104502847981723)
        ·
          refine ⟨2023284426156754271972585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348856284104502847981723 2023284426156754271972585)
          ·
            refine ⟨1517463319617565703979439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2023284426156754271972585 1517463319617565703979439)
            ·
              refine ⟨2276194979426348555969159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517463319617565703979439 2276194979426348555969159)
              ·
                refine ⟨3414292469139522833953739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2276194979426348555969159 3414292469139522833953739)
                ·
                  refine ⟨5121438703709284250930609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414292469139522833953739 5121438703709284250930609)
                  ·
                    refine ⟨3841079027781963188197957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5121438703709284250930609 3841079027781963188197957)
                    ·
                      refine ⟨720202317709118097787117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3841079027781963188197957 720202317709118097787117)
                      ·
                        rfl

theorem cell23_1402589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1402589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402589 prefixEnd_1402589 := by exact prefixLift 1402589
  have htrace : WordTrace (prefixWord ++ tailWord_1402589) baseStart_1402589 baseEnd_1402589 := by
    simpa [prefixWord, tailWord_1402589, baseEnd_1402589] using wordTrace_append hprefix tailTrace_1402589
  have hstable : (prefixWord ++ tailWord_1402589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402589).length < 2 ^ (prefixWord ++ tailWord_1402589).sum := by decide
  have hdescent : baseEnd_1402589 < baseStart_1402589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402599 : List Nat := [1, 1, 5, 4, 2, 1, 2, 7]
def baseStart_1402599 : Nat := 118140960795 + 1402599 * 2 ^ 59
def prefixEnd_1402599 : Nat := 4983230072969 + 3 ^ 40 * 1402599 * 2
def baseEnd_1402599 : Nat := 26674350093172705876373

theorem tailTrace_1402599 : CollatzResearch.WordTrace tailWord_1402599 prefixEnd_1402599 26674350093172705876373 := by
  unfold tailWord_1402599
  simp only [CollatzResearch.WordTrace]
  refine ⟨51156988245630842683170851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34104658830420561788780567 51156988245630842683170851)
  ·
    refine ⟨76735482368446264024756277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51156988245630842683170851 76735482368446264024756277)
    ·
      refine ⟨7193951472041837252320901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76735482368446264024756277 7193951472041837252320901)
      ·
        refine ⟨1348865901007844484810169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7193951472041837252320901 1348865901007844484810169)
        ·
          refine ⟨1011649425755883363607627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1348865901007844484810169 1011649425755883363607627)
          ·
            refine ⟨1517474138633825045411441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011649425755883363607627 1517474138633825045411441)
            ·
              refine ⟨1138105603975368784058581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517474138633825045411441 1138105603975368784058581)
              ·
                refine ⟨26674350093172705876373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1138105603975368784058581 26674350093172705876373)
                ·
                  rfl

theorem cell23_1402599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 7].length) (baseStart_1402599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402599 prefixEnd_1402599 := by exact prefixLift 1402599
  have htrace : WordTrace (prefixWord ++ tailWord_1402599) baseStart_1402599 baseEnd_1402599 := by
    simpa [prefixWord, tailWord_1402599, baseEnd_1402599] using wordTrace_append hprefix tailTrace_1402599
  have hstable : (prefixWord ++ tailWord_1402599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402599).length < 2 ^ (prefixWord ++ tailWord_1402599).sum := by decide
  have hdescent : baseEnd_1402599 < baseStart_1402599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402602 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_1402602 : Nat := 118140960795 + 1402602 * 2 ^ 59
def prefixEnd_1402602 : Nat := 4983230072969 + 3 ^ 40 * 1402602 * 2
def baseEnd_1402602 : Nat := 720208992957626546924557

theorem tailTrace_1402602 : CollatzResearch.WordTrace tailWord_1402602 prefixEnd_1402602 720208992957626546924557 := by
  unfold tailWord_1402602
  simp only [CollatzResearch.WordTrace]
  refine ⟨12789274416154993548882515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34104731776413316130353373 12789274416154993548882515)
  ·
    refine ⟨19183911624232490323323773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12789274416154993548882515 19183911624232490323323773)
    ·
      refine ⟨7193966859087183871246415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19183911624232490323323773 7193966859087183871246415)
      ·
        refine ⟨10790950288630775806869623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7193966859087183871246415 10790950288630775806869623)
        ·
          refine ⟨16186425432946163710304435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10790950288630775806869623 16186425432946163710304435)
          ·
            refine ⟨24279638149419245565456653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16186425432946163710304435 24279638149419245565456653)
            ·
              refine ⟨9104864306032217087046245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24279638149419245565456653 9104864306032217087046245)
              ·
                refine ⟨1707162057381040703821171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9104864306032217087046245 1707162057381040703821171)
                ·
                  refine ⟨2560743086071561055731757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707162057381040703821171 2560743086071561055731757)
                  ·
                    refine ⟨960278657276835395899409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560743086071561055731757 960278657276835395899409)
                    ·
                      refine ⟨720208992957626546924557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960278657276835395899409 720208992957626546924557)
                      ·
                        rfl

theorem cell23_1402602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_1402602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402602 prefixEnd_1402602 := by exact prefixLift 1402602
  have htrace : WordTrace (prefixWord ++ tailWord_1402602) baseStart_1402602 baseEnd_1402602 := by
    simpa [prefixWord, tailWord_1402602, baseEnd_1402602] using wordTrace_append hprefix tailTrace_1402602
  have hstable : (prefixWord ++ tailWord_1402602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402602).length < 2 ^ (prefixWord ++ tailWord_1402602).sum := by decide
  have hdescent : baseEnd_1402602 < baseStart_1402602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402615 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 1, 4, 2]
def baseStart_1402615 : Nat := 118140960795 + 1402615 * 2 ^ 59
def prefixEnd_1402615 : Nat := 4983230072969 + 3 ^ 40 * 1402615 * 2
def baseEnd_1402615 : Nat := 720215668206134996061997

theorem tailTrace_1402615 : CollatzResearch.WordTrace tailWord_1402615 prefixEnd_1402615 720215668206134996061997 := by
  unfold tailWord_1402615
  simp only [CollatzResearch.WordTrace]
  refine ⟨51157571813572877415753299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34105047875715251610502199 51157571813572877415753299)
  ·
    refine ⟨76736357720359316123629949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51157571813572877415753299 76736357720359316123629949)
    ·
      refine ⟨28776134145134743546361231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76736357720359316123629949 28776134145134743546361231)
      ·
        refine ⟨43164201217702115319541847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28776134145134743546361231 43164201217702115319541847)
        ·
          refine ⟨64746301826553172979312771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43164201217702115319541847 64746301826553172979312771)
          ·
            refine ⟨97119452739829759468969157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64746301826553172979312771 97119452739829759468969157)
            ·
              refine ⟨18209897388718079900431717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97119452739829759468969157 18209897388718079900431717)
              ·
                refine ⟨3414355760384639981330947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18209897388718079900431717 3414355760384639981330947)
                ·
                  refine ⟨5121533640576959971996421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414355760384639981330947 5121533640576959971996421)
                  ·
                    refine ⟨960287557608179994749329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5121533640576959971996421 960287557608179994749329)
                    ·
                      refine ⟨720215668206134996061997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960287557608179994749329 720215668206134996061997)
                      ·
                        rfl

theorem cell23_1402615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_1402615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402615 prefixEnd_1402615 := by exact prefixLift 1402615
  have htrace : WordTrace (prefixWord ++ tailWord_1402615) baseStart_1402615 baseEnd_1402615 := by
    simpa [prefixWord, tailWord_1402615, baseEnd_1402615] using wordTrace_append hprefix tailTrace_1402615
  have hstable : (prefixWord ++ tailWord_1402615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402615).length < 2 ^ (prefixWord ++ tailWord_1402615).sum := by decide
  have hdescent : baseEnd_1402615 < baseStart_1402615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402618 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_1402618 : Nat := 118140960795 + 1402618 * 2 ^ 59
def prefixEnd_1402618 : Nat := 4983230072969 + 3 ^ 40 * 1402618 * 2
def baseEnd_1402618 : Nat := 720217208648098484324483

theorem tailTrace_1402618 : CollatzResearch.WordTrace tailWord_1402618 prefixEnd_1402618 720217208648098484324483 := by
  unfold tailWord_1402618
  simp only [CollatzResearch.WordTrace]
  refine ⟨12789420308140502232028127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34105120821708005952075005 12789420308140502232028127)
  ·
    refine ⟨19184130462210753348042191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12789420308140502232028127 19184130462210753348042191)
    ·
      refine ⟨28776195693316130022063287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19184130462210753348042191 28776195693316130022063287)
      ·
        refine ⟨43164293539974195033094931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28776195693316130022063287 43164293539974195033094931)
        ·
          refine ⟨64746440309961292549642397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43164293539974195033094931 64746440309961292549642397)
          ·
            refine ⟨24279915116235484706115899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64746440309961292549642397 24279915116235484706115899)
            ·
              refine ⟨36419872674353227059173849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24279915116235484706115899 36419872674353227059173849)
              ·
                refine ⟨27314904505764920294380387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36419872674353227059173849 27314904505764920294380387)
                ·
                  refine ⟨40972356758647380441570581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27314904505764920294380387 40972356758647380441570581)
                  ·
                    refine ⟨1920579223061595958198621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40972356758647380441570581 1920579223061595958198621)
                    ·
                      refine ⟨720217208648098484324483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1920579223061595958198621 720217208648098484324483)
                      ·
                        rfl

theorem cell23_1402618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_1402618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402618 prefixEnd_1402618 := by exact prefixLift 1402618
  have htrace : WordTrace (prefixWord ++ tailWord_1402618) baseStart_1402618 baseEnd_1402618 := by
    simpa [prefixWord, tailWord_1402618, baseEnd_1402618] using wordTrace_append hprefix tailTrace_1402618
  have hstable : (prefixWord ++ tailWord_1402618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402618).length < 2 ^ (prefixWord ++ tailWord_1402618).sum := by decide
  have hdescent : baseEnd_1402618 < baseStart_1402618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402632 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_1402632 : Nat := 118140960795 + 1402632 * 2 ^ 59
def prefixEnd_1402632 : Nat := 4983230072969 + 3 ^ 40 * 1402632 * 2
def baseEnd_1402632 : Nat := 720224397377261429549419

theorem tailTrace_1402632 : CollatzResearch.WordTrace tailWord_1402632 prefixEnd_1402632 720224397377261429549419 := by
  unfold tailWord_1402632
  simp only [CollatzResearch.WordTrace]
  refine ⟨25579095927255644659561075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34105461236340859546081433 25579095927255644659561075)
  ·
    refine ⟨38368643890883466989341613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25579095927255644659561075 38368643890883466989341613)
    ·
      refine ⟨14388241459081300121003105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38368643890883466989341613 14388241459081300121003105)
      ·
        refine ⟨10791181094310975090752329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14388241459081300121003105 10791181094310975090752329)
        ·
          refine ⟨8093385820733231318064247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10791181094310975090752329 8093385820733231318064247)
          ·
            refine ⟨12140078731099846977096371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093385820733231318064247 12140078731099846977096371)
            ·
              refine ⟨18210118096649770465644557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12140078731099846977096371 18210118096649770465644557)
              ·
                refine ⟨6828794286243663924616709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18210118096649770465644557 6828794286243663924616709)
                ·
                  refine ⟨1280398928670686985865633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6828794286243663924616709 1280398928670686985865633)
                  ·
                    refine ⟨960299196503015239399225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1280398928670686985865633 960299196503015239399225)
                    ·
                      refine ⟨720224397377261429549419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960299196503015239399225 720224397377261429549419)
                      ·
                        rfl

theorem cell23_1402632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_1402632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402632 prefixEnd_1402632 := by exact prefixLift 1402632
  have htrace : WordTrace (prefixWord ++ tailWord_1402632) baseStart_1402632 baseEnd_1402632 := by
    simpa [prefixWord, tailWord_1402632, baseEnd_1402632] using wordTrace_append hprefix tailTrace_1402632
  have hstable : (prefixWord ++ tailWord_1402632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402632).length < 2 ^ (prefixWord ++ tailWord_1402632).sum := by decide
  have hdescent : baseEnd_1402632 < baseStart_1402632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402637 : List Nat := [1, 7, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1402637 : Nat := 118140960795 + 1402637 * 2 ^ 59
def prefixEnd_1402637 : Nat := 4983230072969 + 3 ^ 40 * 1402637 * 2
def baseEnd_1402637 : Nat := 240075654926844636662299

theorem tailTrace_1402637 : CollatzResearch.WordTrace tailWord_1402637 prefixEnd_1402637 240075654926844636662299 := by
  unfold tailWord_1402637
  simp only [CollatzResearch.WordTrace]
  refine ⟨51158374219493175173054165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34105582812995450115369443 51158374219493175173054165)
  ·
    refine ⟨1199024395769371293118457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 51158374219493175173054165 1199024395769371293118457)
    ·
      refine ⟨899268296827028469838843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1199024395769371293118457 899268296827028469838843)
      ·
        refine ⟨1348902445240542704758265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899268296827028469838843 1348902445240542704758265)
        ·
          refine ⟨1011676833930407028568699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1348902445240542704758265 1011676833930407028568699)
          ·
            refine ⟨1517515250895610542853049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011676833930407028568699 1517515250895610542853049)
            ·
              refine ⟨1138136438171707907139787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517515250895610542853049 1138136438171707907139787)
              ·
                refine ⟨1707204657257561860709681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138136438171707907139787 1707204657257561860709681)
                ·
                  refine ⟨1280403492943171395532261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1707204657257561860709681 1280403492943171395532261)
                  ·
                    refine ⟨240075654926844636662299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1280403492943171395532261 240075654926844636662299)
                    ·
                      rfl

theorem cell23_1402637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1402637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402637 prefixEnd_1402637 := by exact prefixLift 1402637
  have htrace : WordTrace (prefixWord ++ tailWord_1402637) baseStart_1402637 baseEnd_1402637 := by
    simpa [prefixWord, tailWord_1402637, baseEnd_1402637] using wordTrace_append hprefix tailTrace_1402637
  have hstable : (prefixWord ++ tailWord_1402637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402637).length < 2 ^ (prefixWord ++ tailWord_1402637).sum := by decide
  have hdescent : baseEnd_1402637 < baseStart_1402637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402688 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_1402688 : Nat := 118140960795 + 1402688 * 2 ^ 59
def prefixEnd_1402688 : Nat := 4983230072969 + 3 ^ 40 * 1402688 * 2
def baseEnd_1402688 : Nat := 720253152293913210449161

theorem tailTrace_1402688 : CollatzResearch.WordTrace tailWord_1402688 prefixEnd_1402688 720253152293913210449161 := by
  unfold tailWord_1402688
  simp only [CollatzResearch.WordTrace]
  refine ⟨25580117171154205441580359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34106822894872273922107145 25580117171154205441580359)
  ·
    refine ⟨38370175756731308162370539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25580117171154205441580359 38370175756731308162370539)
    ·
      refine ⟨57555263635096962243555809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38370175756731308162370539 57555263635096962243555809)
      ·
        refine ⟨43166447726322721682666857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57555263635096962243555809 43166447726322721682666857)
        ·
          refine ⟨32374835794742041262000143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43166447726322721682666857 32374835794742041262000143)
          ·
            refine ⟨48562253692113061893000215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32374835794742041262000143 48562253692113061893000215)
            ·
              refine ⟨72843380538169592839500323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48562253692113061893000215 72843380538169592839500323)
              ·
                refine ⟨109265070807254389259250485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72843380538169592839500323 109265070807254389259250485)
                ·
                  refine ⟨10243600388180098993054733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109265070807254389259250485 10243600388180098993054733)
                  ·
                    refine ⟨3841350145567537122395525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10243600388180098993054733 3841350145567537122395525)
                    ·
                      refine ⟨720253152293913210449161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3841350145567537122395525 720253152293913210449161)
                      ·
                        rfl

theorem cell23_1402688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_1402688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402688 prefixEnd_1402688 := by exact prefixLift 1402688
  have htrace : WordTrace (prefixWord ++ tailWord_1402688) baseStart_1402688 baseEnd_1402688 := by
    simpa [prefixWord, tailWord_1402688, baseEnd_1402688] using wordTrace_append hprefix tailTrace_1402688
  have hstable : (prefixWord ++ tailWord_1402688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402688).length < 2 ^ (prefixWord ++ tailWord_1402688).sum := by decide
  have hdescent : baseEnd_1402688 < baseStart_1402688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402722 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1402722 : Nat := 118140960795 + 1402722 * 2 ^ 59
def prefixEnd_1402722 : Nat := 4983230072969 + 3 ^ 40 * 1402722 * 2
def baseEnd_1402722 : Nat := 720270610636166077424005

theorem tailTrace_1402722 : CollatzResearch.WordTrace tailWord_1402722 prefixEnd_1402722 720270610636166077424005 := by
  unfold tailWord_1402722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12790368606046308672474605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34107649616123489793265613 12790368606046308672474605)
  ·
    refine ⟨4796388227267365752177977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12790368606046308672474605 4796388227267365752177977)
    ·
      refine ⟨3597291170450524314133483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4796388227267365752177977 3597291170450524314133483)
      ·
        refine ⟨5395936755675786471200225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3597291170450524314133483 5395936755675786471200225)
        ·
          refine ⟨4046952566756839853400169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5395936755675786471200225 4046952566756839853400169)
          ·
            refine ⟨3035214425067629890050127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4046952566756839853400169 3035214425067629890050127)
            ·
              refine ⟨4552821637601444835075191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035214425067629890050127 4552821637601444835075191)
              ·
                refine ⟨6829232456402167252612787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552821637601444835075191 6829232456402167252612787)
                ·
                  refine ⟨10243848684603250878919181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6829232456402167252612787 10243848684603250878919181)
                  ·
                    refine ⟨3841443256726219079594693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10243848684603250878919181 3841443256726219079594693)
                    ·
                      refine ⟨720270610636166077424005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3841443256726219079594693 720270610636166077424005)
                      ·
                        rfl

theorem cell23_1402722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1402722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402722 prefixEnd_1402722 := by exact prefixLift 1402722
  have htrace : WordTrace (prefixWord ++ tailWord_1402722) baseStart_1402722 baseEnd_1402722 := by
    simpa [prefixWord, tailWord_1402722, baseEnd_1402722] using wordTrace_append hprefix tailTrace_1402722
  have hstable : (prefixWord ++ tailWord_1402722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402722).length < 2 ^ (prefixWord ++ tailWord_1402722).sum := by decide
  have hdescent : baseEnd_1402722 < baseStart_1402722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402768 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_1402768 : Nat := 118140960795 + 1402768 * 2 ^ 59
def prefixEnd_1402768 : Nat := 4983230072969 + 3 ^ 40 * 1402768 * 2
def baseEnd_1402768 : Nat := 720294230746272897448793

theorem tailTrace_1402768 : CollatzResearch.WordTrace tailWord_1402768 prefixEnd_1402768 720294230746272897448793 := by
  unfold tailWord_1402768
  simp only [CollatzResearch.WordTrace]
  refine ⟨25581576091009292273036479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34108768121345723030715305 25581576091009292273036479)
  ·
    refine ⟨38372364136513938409554719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25581576091009292273036479 38372364136513938409554719)
    ·
      refine ⟨57558546204770907614332079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38372364136513938409554719 57558546204770907614332079)
      ·
        refine ⟨86337819307156361421498119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57558546204770907614332079 86337819307156361421498119)
        ·
          refine ⟨129506728960734542132247179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86337819307156361421498119 129506728960734542132247179)
          ·
            refine ⟨194260093441101813198370769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129506728960734542132247179 194260093441101813198370769)
            ·
              refine ⟨145695070080826359898778077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194260093441101813198370769 145695070080826359898778077)
              ·
                refine ⟨54635651280309884962041779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145695070080826359898778077 54635651280309884962041779)
                ·
                  refine ⟨81953476920464827443062669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54635651280309884962041779 81953476920464827443062669)
                  ·
                    refine ⟨30732553845174310291148501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81953476920464827443062669 30732553845174310291148501)
                    ·
                      refine ⟨720294230746272897448793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30732553845174310291148501 720294230746272897448793)
                      ·
                        rfl

theorem cell23_1402768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_1402768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402768 prefixEnd_1402768 := by exact prefixLift 1402768
  have htrace : WordTrace (prefixWord ++ tailWord_1402768) baseStart_1402768 baseEnd_1402768 := by
    simpa [prefixWord, tailWord_1402768, baseEnd_1402768] using wordTrace_append hprefix tailTrace_1402768
  have hstable : (prefixWord ++ tailWord_1402768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402768).length < 2 ^ (prefixWord ++ tailWord_1402768).sum := by decide
  have hdescent : baseEnd_1402768 < baseStart_1402768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402783 : List Nat := [1, 1, 2, 5, 4, 1, 1, 3, 1, 4]
def baseStart_1402783 : Nat := 118140960795 + 1402783 * 2 ^ 59
def prefixEnd_1402783 : Nat := 4983230072969 + 3 ^ 40 * 1402783 * 2
def baseEnd_1402783 : Nat := 240100644318696779587075

theorem tailTrace_1402783 : CollatzResearch.WordTrace tailWord_1402783 prefixEnd_1402783 240100644318696779587075 := by
  unfold tailWord_1402783
  simp only [CollatzResearch.WordTrace]
  refine ⟨51163699276964242107869003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34109132851309494738579335 51163699276964242107869003)
  ·
    refine ⟨76745548915446363161803505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51163699276964242107869003 76745548915446363161803505)
    ·
      refine ⟨57559161686584772371352629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76745548915446363161803505 57559161686584772371352629)
      ·
        refine ⟨5396171408117322409814309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57559161686584772371352629 5396171408117322409814309)
        ·
          refine ⟨1011782139021997951840183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5396171408117322409814309 1011782139021997951840183)
          ·
            refine ⟨1517673208532996927760275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011782139021997951840183 1517673208532996927760275)
            ·
              refine ⟨2276509812799495391640413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517673208532996927760275 2276509812799495391640413)
              ·
                refine ⟨853691179799810771865155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2276509812799495391640413 853691179799810771865155)
                ·
                  refine ⟨1280536769699716157797733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853691179799810771865155 1280536769699716157797733)
                  ·
                    refine ⟨240100644318696779587075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1280536769699716157797733 240100644318696779587075)
                    ·
                      rfl

theorem cell23_1402783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3, 1, 4].length) (baseStart_1402783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402783 prefixEnd_1402783 := by exact prefixLift 1402783
  have htrace : WordTrace (prefixWord ++ tailWord_1402783) baseStart_1402783 baseEnd_1402783 := by
    simpa [prefixWord, tailWord_1402783, baseEnd_1402783] using wordTrace_append hprefix tailTrace_1402783
  have hstable : (prefixWord ++ tailWord_1402783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402783).length < 2 ^ (prefixWord ++ tailWord_1402783).sum := by decide
  have hdescent : baseEnd_1402783 < baseStart_1402783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402815 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_1402815 : Nat := 118140960795 + 1402815 * 2 ^ 59
def prefixEnd_1402815 : Nat := 4983230072969 + 3 ^ 40 * 1402815 * 2
def baseEnd_1402815 : Nat := 720318364337034213561077

theorem tailTrace_1402815 : CollatzResearch.WordTrace tailWord_1402815 prefixEnd_1402815 720318364337034213561077 := by
  unfold tailWord_1402815
  simp only [CollatzResearch.WordTrace]
  refine ⟨51164866412848311573033899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34109910941898874382022599 51164866412848311573033899)
  ·
    refine ⟨76747299619272467359550849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51164866412848311573033899 76747299619272467359550849)
    ·
      refine ⟨57560474714454350519663137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76747299619272467359550849 57560474714454350519663137)
      ·
        refine ⟨43170356035840762889747353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57560474714454350519663137 43170356035840762889747353)
        ·
          refine ⟨32377767026880572167310515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43170356035840762889747353 32377767026880572167310515)
          ·
            refine ⟨48566650540320858250965773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32377767026880572167310515 48566650540320858250965773)
            ·
              refine ⟨18212493952620321844112165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48566650540320858250965773 18212493952620321844112165)
              ·
                refine ⟨3414842616116310345771031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18212493952620321844112165 3414842616116310345771031)
                ·
                  refine ⟨5122263924174465518656547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414842616116310345771031 5122263924174465518656547)
                  ·
                    refine ⟨7683395886261698277984821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5122263924174465518656547 7683395886261698277984821)
                    ·
                      refine ⟨720318364337034213561077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7683395886261698277984821 720318364337034213561077)
                      ·
                        rfl

theorem cell23_1402815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_1402815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402815 prefixEnd_1402815 := by exact prefixLift 1402815
  have htrace : WordTrace (prefixWord ++ tailWord_1402815) baseStart_1402815 baseEnd_1402815 := by
    simpa [prefixWord, tailWord_1402815, baseEnd_1402815] using wordTrace_append hprefix tailTrace_1402815
  have hstable : (prefixWord ++ tailWord_1402815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402815).length < 2 ^ (prefixWord ++ tailWord_1402815).sum := by decide
  have hdescent : baseEnd_1402815 < baseStart_1402815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402905 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_1402905 : Nat := 118140960795 + 1402905 * 2 ^ 59
def prefixEnd_1402905 : Nat := 4983230072969 + 3 ^ 40 * 1402905 * 2
def baseEnd_1402905 : Nat := 720364577595938861435663

theorem tailTrace_1402905 : CollatzResearch.WordTrace tailWord_1402905 prefixEnd_1402905 720364577595938861435663 := by
  unfold tailWord_1402905
  simp only [CollatzResearch.WordTrace]
  refine ⟨51168148982522256943810169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34112099321681504629206779 51168148982522256943810169)
  ·
    refine ⟨38376111736891692707857627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51168148982522256943810169 38376111736891692707857627)
    ·
      refine ⟨57564167605337539061786441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38376111736891692707857627 57564167605337539061786441)
      ·
        refine ⟨43173125704003154296339831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57564167605337539061786441 43173125704003154296339831)
        ·
          refine ⟨64759688556004731444509747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43173125704003154296339831 64759688556004731444509747)
          ·
            refine ⟨97139532834007097166764621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64759688556004731444509747 97139532834007097166764621)
            ·
              refine ⟨36427324812752661437536733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97139532834007097166764621 36427324812752661437536733)
              ·
                refine ⟨13660246804782248039076275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36427324812752661437536733 13660246804782248039076275)
                ·
                  refine ⟨20490370207173372058614413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13660246804782248039076275 20490370207173372058614413)
                  ·
                    refine ⟨7683888827690014521980405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20490370207173372058614413 7683888827690014521980405)
                    ·
                      refine ⟨720364577595938861435663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7683888827690014521980405 720364577595938861435663)
                      ·
                        rfl

theorem cell23_1402905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_1402905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402905 prefixEnd_1402905 := by exact prefixLift 1402905
  have htrace : WordTrace (prefixWord ++ tailWord_1402905) baseStart_1402905 baseEnd_1402905 := by
    simpa [prefixWord, tailWord_1402905, baseEnd_1402905] using wordTrace_append hprefix tailTrace_1402905
  have hstable : (prefixWord ++ tailWord_1402905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402905).length < 2 ^ (prefixWord ++ tailWord_1402905).sum := by decide
  have hdescent : baseEnd_1402905 < baseStart_1402905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402906 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2]
def baseStart_1402906 : Nat := 118140960795 + 1402906 * 2 ^ 59
def prefixEnd_1402906 : Nat := 4983230072969 + 3 ^ 40 * 1402906 * 2
def baseEnd_1402906 : Nat := 720365091076593357523159

theorem tailTrace_1402906 : CollatzResearch.WordTrace tailWord_1402906 prefixEnd_1402906 720365091076593357523159 := by
  unfold tailWord_1402906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12792046363879658528649143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34112123637012422743064381 12792046363879658528649143)
  ·
    refine ⟨19188069545819487792973715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12792046363879658528649143 19188069545819487792973715)
    ·
      refine ⟨28782104318729231689460573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19188069545819487792973715 28782104318729231689460573)
      ·
        refine ⟨10793289119523461883547715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28782104318729231689460573 10793289119523461883547715)
        ·
          refine ⟨16189933679285192825321573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10793289119523461883547715 16189933679285192825321573)
          ·
            refine ⟨3035612564865973654747795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16189933679285192825321573 3035612564865973654747795)
            ·
              refine ⟨4553418847298960482121693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035612564865973654747795 4553418847298960482121693)
              ·
                refine ⟨1707532067737110180795635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4553418847298960482121693 1707532067737110180795635)
                ·
                  refine ⟨2561298101605665271193453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707532067737110180795635 2561298101605665271193453)
                  ·
                    refine ⟨960486788102124476697545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561298101605665271193453 960486788102124476697545)
                    ·
                      refine ⟨720365091076593357523159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960486788102124476697545 720365091076593357523159)
                      ·
                        rfl

theorem cell23_1402906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_1402906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402906 prefixEnd_1402906 := by exact prefixLift 1402906
  have htrace : WordTrace (prefixWord ++ tailWord_1402906) baseStart_1402906 baseEnd_1402906 := by
    simpa [prefixWord, tailWord_1402906, baseEnd_1402906] using wordTrace_append hprefix tailTrace_1402906
  have hstable : (prefixWord ++ tailWord_1402906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402906).length < 2 ^ (prefixWord ++ tailWord_1402906).sum := by decide
  have hdescent : baseEnd_1402906 < baseStart_1402906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402913 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_1402913 : Nat := 118140960795 + 1402913 * 2 ^ 59
def prefixEnd_1402913 : Nat := 4983230072969 + 3 ^ 40 * 1402913 * 2
def baseEnd_1402913 : Nat := 720368685441174830135627

theorem tailTrace_1402913 : CollatzResearch.WordTrace tailWord_1402913 prefixEnd_1402913 720368685441174830135627 := by
  unfold tailWord_1402913
  simp only [CollatzResearch.WordTrace]
  refine ⟨51168440766493274310101393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34112293844328849540067595 51168440766493274310101393)
  ·
    refine ⟨38376330574869955732576045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51168440766493274310101393 38376330574869955732576045)
    ·
      refine ⟨14391123965576233399716017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38376330574869955732576045 14391123965576233399716017)
      ·
        refine ⟨10793342974182175049787013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14391123965576233399716017 10793342974182175049787013)
        ·
          refine ⟨2023751807659157821835065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10793342974182175049787013 2023751807659157821835065)
          ·
            refine ⟨1517813855744368366376299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2023751807659157821835065 1517813855744368366376299)
            ·
              refine ⟨2276720783616552549564449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517813855744368366376299 2276720783616552549564449)
              ·
                refine ⟨1707540587712414412173337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2276720783616552549564449 1707540587712414412173337)
                ·
                  refine ⟨1280655440784310809130003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1707540587712414412173337 1280655440784310809130003)
                  ·
                    refine ⟨1920983161176466213695005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1280655440784310809130003 1920983161176466213695005)
                    ·
                      refine ⟨720368685441174830135627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1920983161176466213695005 720368685441174830135627)
                      ·
                        rfl

theorem cell23_1402913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_1402913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402913 prefixEnd_1402913 := by exact prefixLift 1402913
  have htrace : WordTrace (prefixWord ++ tailWord_1402913) baseStart_1402913 baseEnd_1402913 := by
    simpa [prefixWord, tailWord_1402913, baseEnd_1402913] using wordTrace_append hprefix tailTrace_1402913
  have hstable : (prefixWord ++ tailWord_1402913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402913).length < 2 ^ (prefixWord ++ tailWord_1402913).sum := by decide
  have hdescent : baseEnd_1402913 < baseStart_1402913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402952 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_1402952 : Nat := 118140960795 + 1402952 * 2 ^ 59
def prefixEnd_1402952 : Nat := 4983230072969 + 3 ^ 40 * 1402952 * 2
def baseEnd_1402952 : Nat := 720388711186700177547947

theorem tailTrace_1402952 : CollatzResearch.WordTrace tailWord_1402952 prefixEnd_1402952 720388711186700177547947 := by
  unfold tailWord_1402952
  simp only [CollatzResearch.WordTrace]
  refine ⟨25584931606675991985385555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34113242142234655980514073 25584931606675991985385555)
  ·
    refine ⟨38377397410013987978078333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25584931606675991985385555 38377397410013987978078333)
    ·
      refine ⟨14391524028755245491779375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38377397410013987978078333 14391524028755245491779375)
      ·
        refine ⟨21587286043132868237669063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14391524028755245491779375 21587286043132868237669063)
        ·
          refine ⟨32380929064699302356503595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21587286043132868237669063 32380929064699302356503595)
          ·
            refine ⟨48571393597048953534755393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32380929064699302356503595 48571393597048953534755393)
            ·
              refine ⟨36428545197786715151066545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48571393597048953534755393 36428545197786715151066545)
              ·
                refine ⟨27321408898340036363299909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36428545197786715151066545 27321408898340036363299909)
                ·
                  refine ⟨5122764168438756818118733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27321408898340036363299909 5122764168438756818118733)
                  ·
                    refine ⟨1921036563164533806794525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5122764168438756818118733 1921036563164533806794525)
                    ·
                      refine ⟨720388711186700177547947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1921036563164533806794525 720388711186700177547947)
                      ·
                        rfl

theorem cell23_1402952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_1402952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402952 prefixEnd_1402952 := by exact prefixLift 1402952
  have htrace : WordTrace (prefixWord ++ tailWord_1402952) baseStart_1402952 baseEnd_1402952 := by
    simpa [prefixWord, tailWord_1402952, baseEnd_1402952] using wordTrace_append hprefix tailTrace_1402952
  have hstable : (prefixWord ++ tailWord_1402952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402952).length < 2 ^ (prefixWord ++ tailWord_1402952).sum := by decide
  have hdescent : baseEnd_1402952 < baseStart_1402952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402976 : List Nat := [2, 1, 1, 3, 2, 4, 3, 2, 5]
def baseStart_1402976 : Nat := 118140960795 + 1402976 * 2 ^ 59
def prefixEnd_1402976 : Nat := 4983230072969 + 3 ^ 40 * 1402976 * 2
def baseEnd_1402976 : Nat := 80044559413600898183093

theorem tailTrace_1402976 : CollatzResearch.WordTrace tailWord_1402976 prefixEnd_1402976 80044559413600898183093 := by
  unfold tailWord_1402976
  simp only [CollatzResearch.WordTrace]
  refine ⟨25585369282632518034822391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34113825710176690713096521 25585369282632518034822391)
  ·
    refine ⟨38378053923948777052233587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25585369282632518034822391 38378053923948777052233587)
    ·
      refine ⟨57567080885923165578350381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38378053923948777052233587 57567080885923165578350381)
      ·
        refine ⟨21587655332221187091881393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57567080885923165578350381 21587655332221187091881393)
        ·
          refine ⟨16190741499165890318911045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21587655332221187091881393 16190741499165890318911045)
          ·
            refine ⟨3035764031093604434795821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16190741499165890318911045 3035764031093604434795821)
            ·
              refine ⟨1138411511660101663048433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3035764031093604434795821 1138411511660101663048433)
              ·
                refine ⟨853808633745076247286325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138411511660101663048433 853808633745076247286325)
                ·
                  refine ⟨80044559413600898183093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 853808633745076247286325 80044559413600898183093)
                  ·
                    rfl

theorem cell23_1402976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 5].length) (baseStart_1402976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402976 prefixEnd_1402976 := by exact prefixLift 1402976
  have htrace : WordTrace (prefixWord ++ tailWord_1402976) baseStart_1402976 baseEnd_1402976 := by
    simpa [prefixWord, tailWord_1402976, baseEnd_1402976] using wordTrace_append hprefix tailTrace_1402976
  have hstable : (prefixWord ++ tailWord_1402976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402976).length < 2 ^ (prefixWord ++ tailWord_1402976).sum := by decide
  have hdescent : baseEnd_1402976 < baseStart_1402976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403026 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_1403026 : Nat := 118140960795 + 1403026 * 2 ^ 59
def prefixEnd_1403026 : Nat := 4983230072969 + 3 ^ 40 * 1403026 * 2
def baseEnd_1403026 : Nat := 720426708755132888022607

theorem tailTrace_1403026 : CollatzResearch.WordTrace tailWord_1403026 prefixEnd_1403026 720426708755132888022607 := by
  unfold tailWord_1403026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12793140553770973652241233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34115041476722596405976621 12793140553770973652241233)
  ·
    refine ⟨9594855415328230239180925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12793140553770973652241233 9594855415328230239180925)
    ·
      refine ⟨3598070780748086339692847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9594855415328230239180925 3598070780748086339692847)
      ·
        refine ⟨5397106171122129509539271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3598070780748086339692847 5397106171122129509539271)
        ·
          refine ⟨8095659256683194264308907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5397106171122129509539271 8095659256683194264308907)
          ·
            refine ⟨12143488885024791396463361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8095659256683194264308907 12143488885024791396463361)
            ·
              refine ⟨9107616663768593547347521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12143488885024791396463361 9107616663768593547347521)
              ·
                refine ⟨6830712497826445160510641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9107616663768593547347521 6830712497826445160510641)
                ·
                  refine ⟨5123034373369833870382981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6830712497826445160510641 5123034373369833870382981)
                  ·
                    refine ⟨960568945006843850696809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5123034373369833870382981 960568945006843850696809)
                    ·
                      refine ⟨720426708755132888022607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960568945006843850696809 720426708755132888022607)
                      ·
                        rfl

theorem cell23_1403026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_1403026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403026 prefixEnd_1403026 := by exact prefixLift 1403026
  have htrace : WordTrace (prefixWord ++ tailWord_1403026) baseStart_1403026 baseEnd_1403026 := by
    simpa [prefixWord, tailWord_1403026, baseEnd_1403026] using wordTrace_append hprefix tailTrace_1403026
  have hstable : (prefixWord ++ tailWord_1403026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403026).length < 2 ^ (prefixWord ++ tailWord_1403026).sum := by decide
  have hdescent : baseEnd_1403026 < baseStart_1403026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403029 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_1403029 : Nat := 118140960795 + 1403029 * 2 ^ 59
def prefixEnd_1403029 : Nat := 4983230072969 + 3 ^ 40 * 1403029 * 2
def baseEnd_1403029 : Nat := 720428249197096376285093

theorem tailTrace_1403029 : CollatzResearch.WordTrace tailWord_1403029 prefixEnd_1403029 720428249197096376285093 := by
  unfold tailWord_1403029
  simp only [CollatzResearch.WordTrace]
  refine ⟨51172671634073026121324141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34115114422715350747549427 51172671634073026121324141)
  ·
    refine ⟨19189751862777384795496553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51172671634073026121324141 19189751862777384795496553)
    ·
      refine ⟨14392313897083038596622415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19189751862777384795496553 14392313897083038596622415)
      ·
        refine ⟨21588470845624557894933623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14392313897083038596622415 21588470845624557894933623)
        ·
          refine ⟨32382706268436836842400435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21588470845624557894933623 32382706268436836842400435)
          ·
            refine ⟨48574059402655255263600653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32382706268436836842400435 48574059402655255263600653)
            ·
              refine ⟨18215272275995720723850245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48574059402655255263600653 18215272275995720723850245)
              ·
                refine ⟨3415363551749197635721921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18215272275995720723850245 3415363551749197635721921)
                ·
                  refine ⟨2561522663811898226791441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3415363551749197635721921 2561522663811898226791441)
                  ·
                    refine ⟨1921141997858923670093581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2561522663811898226791441 1921141997858923670093581)
                    ·
                      refine ⟨720428249197096376285093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1921141997858923670093581 720428249197096376285093)
                      ·
                        rfl

theorem cell23_1403029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_1403029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403029 prefixEnd_1403029 := by exact prefixLift 1403029
  have htrace : WordTrace (prefixWord ++ tailWord_1403029) baseStart_1403029 baseEnd_1403029 := by
    simpa [prefixWord, tailWord_1403029, baseEnd_1403029] using wordTrace_append hprefix tailTrace_1403029
  have hstable : (prefixWord ++ tailWord_1403029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403029).length < 2 ^ (prefixWord ++ tailWord_1403029).sum := by decide
  have hdescent : baseEnd_1403029 < baseStart_1403029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403060 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1403060 : Nat := 118140960795 + 1403060 * 2 ^ 59
def prefixEnd_1403060 : Nat := 4983230072969 + 3 ^ 40 * 1403060 * 2
def baseEnd_1403060 : Nat := 720444167097385754997451

theorem tailTrace_1403060 : CollatzResearch.WordTrace tailWord_1403060 prefixEnd_1403060 720444167097385754997451 := by
  unfold tailWord_1403060
  simp only [CollatzResearch.WordTrace]
  refine ⟨25586901148480359207851317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34115868197973812277135089 25586901148480359207851317)
  ·
    refine ⟨2398771982670033675736061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25586901148480359207851317 2398771982670033675736061)
    ·
      refine ⟨899539493501262628401023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2398771982670033675736061 899539493501262628401023)
      ·
        refine ⟨1349309240251893942601535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899539493501262628401023 1349309240251893942601535)
        ·
          refine ⟨2023963860377840913902303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349309240251893942601535 2023963860377840913902303)
          ·
            refine ⟨3035945790566761370853455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023963860377840913902303 3035945790566761370853455)
            ·
              refine ⟨4553918685850142056280183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3035945790566761370853455 4553918685850142056280183)
              ·
                refine ⟨6830878028775213084420275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4553918685850142056280183 6830878028775213084420275)
                ·
                  refine ⟨10246317043162819626630413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6830878028775213084420275 10246317043162819626630413)
                  ·
                    refine ⟨3842368891186057359986405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10246317043162819626630413 3842368891186057359986405)
                    ·
                      refine ⟨720444167097385754997451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3842368891186057359986405 720444167097385754997451)
                      ·
                        rfl

theorem cell23_1403060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1403060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403060 prefixEnd_1403060 := by exact prefixLift 1403060
  have htrace : WordTrace (prefixWord ++ tailWord_1403060) baseStart_1403060 baseEnd_1403060 := by
    simpa [prefixWord, tailWord_1403060, baseEnd_1403060] using wordTrace_append hprefix tailTrace_1403060
  have hstable : (prefixWord ++ tailWord_1403060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403060).length < 2 ^ (prefixWord ++ tailWord_1403060).sum := by decide
  have hdescent : baseEnd_1403060 < baseStart_1403060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403070 : List Nat := [4, 2, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_1403070 : Nat := 118140960795 + 1403070 * 2 ^ 59
def prefixEnd_1403070 : Nat := 4983230072969 + 3 ^ 40 * 1403070 * 2
def baseEnd_1403070 : Nat := 240149767301310238624135

theorem tailTrace_1403070 : CollatzResearch.WordTrace tailWord_1403070 prefixEnd_1403070 240149767301310238624135 := by
  unfold tailWord_1403070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6396770878365561265445833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34116111351282993415711109 6396770878365561265445833)
  ·
    refine ⟨4797578158774170949084375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6396770878365561265445833 4797578158774170949084375)
    ·
      refine ⟨7196367238161256423626563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797578158774170949084375 7196367238161256423626563)
      ·
        refine ⟨10794550857241884635439845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7196367238161256423626563 10794550857241884635439845)
        ·
          refine ⟨2023978285732853369144971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10794550857241884635439845 2023978285732853369144971)
          ·
            refine ⟨3035967428599280053717457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023978285732853369144971 3035967428599280053717457)
            ·
              refine ⟨2276975571449460040288093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3035967428599280053717457 2276975571449460040288093)
              ·
                refine ⟨853865839293547515108035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2276975571449460040288093 853865839293547515108035)
                ·
                  refine ⟨1280798758940321272662053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853865839293547515108035 1280798758940321272662053)
                  ·
                    refine ⟨240149767301310238624135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1280798758940321272662053 240149767301310238624135)
                    ·
                      rfl

theorem cell23_1403070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_1403070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403070 prefixEnd_1403070 := by exact prefixLift 1403070
  have htrace : WordTrace (prefixWord ++ tailWord_1403070) baseStart_1403070 baseEnd_1403070 := by
    simpa [prefixWord, tailWord_1403070, baseEnd_1403070] using wordTrace_append hprefix tailTrace_1403070
  have hstable : (prefixWord ++ tailWord_1403070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403070).length < 2 ^ (prefixWord ++ tailWord_1403070).sum := by decide
  have hdescent : baseEnd_1403070 < baseStart_1403070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403099 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 2, 6, 2]
def baseStart_1403099 : Nat := 118140960795 + 1403099 * 2 ^ 59
def prefixEnd_1403099 : Nat := 4983230072969 + 3 ^ 40 * 1403099 * 2
def baseEnd_1403099 : Nat := 720464192842911102409771

theorem tailTrace_1403099 : CollatzResearch.WordTrace tailWord_1403099 prefixEnd_1403099 720464192842911102409771 := by
  unfold tailWord_1403099
  simp only [CollatzResearch.WordTrace]
  refine ⟨51175224743819428076372351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34116816495879618717581567 51175224743819428076372351)
  ·
    refine ⟨76762837115729142114558527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51175224743819428076372351 76762837115729142114558527)
    ·
      refine ⟨115144255673593713171837791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76762837115729142114558527 115144255673593713171837791)
      ·
        refine ⟨172716383510390569757756687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115144255673593713171837791 172716383510390569757756687)
        ·
          refine ⟨259074575265585854636635031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172716383510390569757756687 259074575265585854636635031)
          ·
            refine ⟨388611862898378781954952547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259074575265585854636635031 388611862898378781954952547)
            ·
              refine ⟨582917794347568172932428821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388611862898378781954952547 582917794347568172932428821)
              ·
                refine ⟨27324271610042258106207601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 582917794347568172932428821 27324271610042258106207601)
                ·
                  refine ⟨20493203707531693579655701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27324271610042258106207601 20493203707531693579655701)
                  ·
                    refine ⟨960618923790548136546361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20493203707531693579655701 960618923790548136546361)
                    ·
                      refine ⟨720464192842911102409771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960618923790548136546361 720464192842911102409771)
                      ·
                        rfl

theorem cell23_1403099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 6, 2].length) (baseStart_1403099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403099 prefixEnd_1403099 := by exact prefixLift 1403099
  have htrace : WordTrace (prefixWord ++ tailWord_1403099) baseStart_1403099 baseEnd_1403099 := by
    simpa [prefixWord, tailWord_1403099, baseEnd_1403099] using wordTrace_append hprefix tailTrace_1403099
  have hstable : (prefixWord ++ tailWord_1403099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403099).length < 2 ^ (prefixWord ++ tailWord_1403099).sum := by decide
  have hdescent : baseEnd_1403099 < baseStart_1403099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403100 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 6]
def baseStart_1403100 : Nat := 118140960795 + 1403100 * 2 ^ 59
def prefixEnd_1403100 : Nat := 4983230072969 + 3 ^ 40 * 1403100 * 2
def baseEnd_1403100 : Nat := 80051634035951733166363

theorem tailTrace_1403100 : CollatzResearch.WordTrace tailWord_1403100 prefixEnd_1403100 80051634035951733166363 := by
  unfold tailWord_1403100
  simp only [CollatzResearch.WordTrace]
  refine ⟨25587630608407902623579377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34116840811210536831439169 25587630608407902623579377)
  ·
    refine ⟨19190722956305926967684533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25587630608407902623579377 19190722956305926967684533)
    ·
      refine ⟨1799130277153680653220425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19190722956305926967684533 1799130277153680653220425)
      ·
        refine ⟨1349347707865260489915319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1799130277153680653220425 1349347707865260489915319)
        ·
          refine ⟨2024021561797890734872979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349347707865260489915319 2024021561797890734872979)
          ·
            refine ⟨3036032342696836102309469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024021561797890734872979 3036032342696836102309469)
            ·
              refine ⟨1138512128511313538366051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3036032342696836102309469 1138512128511313538366051)
              ·
                refine ⟨1707768192766970307549077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138512128511313538366051 1707768192766970307549077)
                ·
                  refine ⟨80051634035951733166363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1707768192766970307549077 80051634035951733166363)
                  ·
                    rfl

theorem cell23_1403100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_1403100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403100 prefixEnd_1403100 := by exact prefixLift 1403100
  have htrace : WordTrace (prefixWord ++ tailWord_1403100) baseStart_1403100 baseEnd_1403100 := by
    simpa [prefixWord, tailWord_1403100, baseEnd_1403100] using wordTrace_append hprefix tailTrace_1403100
  have hstable : (prefixWord ++ tailWord_1403100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403100).length < 2 ^ (prefixWord ++ tailWord_1403100).sum := by decide
  have hdescent : baseEnd_1403100 < baseStart_1403100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403116 : List Nat := [2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 4]
def baseStart_1403116 : Nat := 118140960795 + 1403116 * 2 ^ 59
def prefixEnd_1403116 : Nat := 4983230072969 + 3 ^ 40 * 1403116 * 2
def baseEnd_1403116 : Nat := 720472922014037535897193

theorem tailTrace_1403116 : CollatzResearch.WordTrace tailWord_1403116 prefixEnd_1403116 720472922014037535897193 := by
  unfold tailWord_1403116
  simp only [CollatzResearch.WordTrace]
  refine ⟨25587922392378919989870601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34117229856505226653160801 25587922392378919989870601)
  ·
    refine ⟨19190941794284189992402951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25587922392378919989870601 19190941794284189992402951)
    ·
      refine ⟨28786412691426284988604427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19190941794284189992402951 28786412691426284988604427)
      ·
        refine ⟨43179619037139427482906641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28786412691426284988604427 43179619037139427482906641)
        ·
          refine ⟨32384714277854570612179981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43179619037139427482906641 32384714277854570612179981)
          ·
            refine ⟨12144267854195463979567493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32384714277854570612179981 12144267854195463979567493)
            ·
              refine ⟨2277050222661649496168905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12144267854195463979567493 2277050222661649496168905)
              ·
                refine ⟨1707787666996237122126679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277050222661649496168905 1707787666996237122126679)
                ·
                  refine ⟨2561681500494355683190019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707787666996237122126679 2561681500494355683190019)
                  ·
                    refine ⟨3842522250741533524785029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2561681500494355683190019 3842522250741533524785029)
                    ·
                      refine ⟨720472922014037535897193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3842522250741533524785029 720472922014037535897193)
                      ·
                        rfl

theorem cell23_1403116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_1403116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403116 prefixEnd_1403116 := by exact prefixLift 1403116
  have htrace : WordTrace (prefixWord ++ tailWord_1403116) baseStart_1403116 baseEnd_1403116 := by
    simpa [prefixWord, tailWord_1403116, baseEnd_1403116] using wordTrace_append hprefix tailTrace_1403116
  have hstable : (prefixWord ++ tailWord_1403116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403116).length < 2 ^ (prefixWord ++ tailWord_1403116).sum := by decide
  have hdescent : baseEnd_1403116 < baseStart_1403116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403126 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_1403126 : Nat := 118140960795 + 1403126 * 2 ^ 59
def prefixEnd_1403126 : Nat := 4983230072969 + 3 ^ 40 * 1403126 * 2
def baseEnd_1403126 : Nat := 240159352273527498924049

theorem tailTrace_1403126 : CollatzResearch.WordTrace tailWord_1403126 prefixEnd_1403126 240159352273527498924049 := by
  unfold tailWord_1403126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3198513094670100730475327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34117473009814407791736821 3198513094670100730475327)
  ·
    refine ⟨4797769642005151095712991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3198513094670100730475327 4797769642005151095712991)
    ·
      refine ⟨7196654463007726643569487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797769642005151095712991 7196654463007726643569487)
      ·
        refine ⟨10794981694511589965354231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7196654463007726643569487 10794981694511589965354231)
        ·
          refine ⟨16192472541767384948031347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10794981694511589965354231 16192472541767384948031347)
          ·
            refine ⟨24288708812651077422047021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16192472541767384948031347 24288708812651077422047021)
            ·
              refine ⟨9108265804744154033267633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24288708812651077422047021 9108265804744154033267633)
              ·
                refine ⟨6831199353558115524950725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9108265804744154033267633 6831199353558115524950725)
                ·
                  refine ⟨1280849878792146660928261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6831199353558115524950725 1280849878792146660928261)
                  ·
                    refine ⟨240159352273527498924049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1280849878792146660928261 240159352273527498924049)
                    ·
                      rfl

theorem cell23_1403126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_1403126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403126 prefixEnd_1403126 := by exact prefixLift 1403126
  have htrace : WordTrace (prefixWord ++ tailWord_1403126) baseStart_1403126 baseEnd_1403126 := by
    simpa [prefixWord, tailWord_1403126, baseEnd_1403126] using wordTrace_append hprefix tailTrace_1403126
  have hstable : (prefixWord ++ tailWord_1403126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403126).length < 2 ^ (prefixWord ++ tailWord_1403126).sum := by decide
  have hdescent : baseEnd_1403126 < baseStart_1403126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403136 : List Nat := [2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 3]
def baseStart_1403136 : Nat := 118140960795 + 1403136 * 2 ^ 59
def prefixEnd_1403136 : Nat := 4983230072969 + 3 ^ 40 * 1403136 * 2
def baseEnd_1403136 : Nat := 720483191627127457647101

theorem tailTrace_1403136 : CollatzResearch.WordTrace tailWord_1403136 prefixEnd_1403136 720483191627127457647101 := by
  unfold tailWord_1403136
  simp only [CollatzResearch.WordTrace]
  refine ⟨25588287122342691697734631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34117716163123588930312841 25588287122342691697734631)
  ·
    refine ⟨38382430683514037546601947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25588287122342691697734631 38382430683514037546601947)
    ·
      refine ⟨57573646025271056319902921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38382430683514037546601947 57573646025271056319902921)
      ·
        refine ⟨43180234518953292239927191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57573646025271056319902921 43180234518953292239927191)
        ·
          refine ⟨64770351778429938359890787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43180234518953292239927191 64770351778429938359890787)
          ·
            refine ⟨97155527667644907539836181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64770351778429938359890787 97155527667644907539836181)
            ·
              refine ⟨4554165359420855040929821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97155527667644907539836181 4554165359420855040929821)
              ·
                refine ⟨1707812009782820640348683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4554165359420855040929821 1707812009782820640348683)
                ·
                  refine ⟨2561718014674230960523025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707812009782820640348683 2561718014674230960523025)
                  ·
                    refine ⟨1921288511005673220392269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2561718014674230960523025 1921288511005673220392269)
                    ·
                      refine ⟨720483191627127457647101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1921288511005673220392269 720483191627127457647101)
                      ·
                        rfl

theorem cell23_1403136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_1403136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403136 prefixEnd_1403136 := by exact prefixLift 1403136
  have htrace : WordTrace (prefixWord ++ tailWord_1403136) baseStart_1403136 baseEnd_1403136 := by
    simpa [prefixWord, tailWord_1403136, baseEnd_1403136] using wordTrace_append hprefix tailTrace_1403136
  have hstable : (prefixWord ++ tailWord_1403136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403136).length < 2 ^ (prefixWord ++ tailWord_1403136).sum := by decide
  have hdescent : baseEnd_1403136 < baseStart_1403136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403170 : List Nat := [3, 3, 1, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_1403170 : Nat := 118140960795 + 1403170 * 2 ^ 59
def prefixEnd_1403170 : Nat := 4983230072969 + 3 ^ 40 * 1403170 * 2
def baseEnd_1403170 : Nat := 720500649969380324621945

theorem tailTrace_1403170 : CollatzResearch.WordTrace tailWord_1403170 prefixEnd_1403170 720500649969380324621945 := by
  unfold tailWord_1403170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12794453581640551800551741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34118542884374804801471309 12794453581640551800551741)
  ·
    refine ⟨4797920093115206925206903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12794453581640551800551741 4797920093115206925206903)
    ·
      refine ⟨7196880139672810387810355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797920093115206925206903 7196880139672810387810355)
      ·
        refine ⟨10795320209509215581715533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7196880139672810387810355 10795320209509215581715533)
        ·
          refine ⟨4048245078565955843143325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10795320209509215581715533 4048245078565955843143325)
          ·
            refine ⟨1518091904462233441178747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4048245078565955843143325 1518091904462233441178747)
            ·
              refine ⟨2277137856693350161768121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518091904462233441178747 2277137856693350161768121)
              ·
                refine ⟨1707853392520012621326091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277137856693350161768121 1707853392520012621326091)
                ·
                  refine ⟨2561780088780018931989137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707853392520012621326091 2561780088780018931989137)
                  ·
                    refine ⟨1921335066585014198991853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2561780088780018931989137 1921335066585014198991853)
                    ·
                      refine ⟨720500649969380324621945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1921335066585014198991853 720500649969380324621945)
                      ·
                        rfl

theorem cell23_1403170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_1403170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403170 prefixEnd_1403170 := by exact prefixLift 1403170
  have htrace : WordTrace (prefixWord ++ tailWord_1403170) baseStart_1403170 baseEnd_1403170 := by
    simpa [prefixWord, tailWord_1403170, baseEnd_1403170] using wordTrace_append hprefix tailTrace_1403170
  have hstable : (prefixWord ++ tailWord_1403170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403170).length < 2 ^ (prefixWord ++ tailWord_1403170).sum := by decide
  have hdescent : baseEnd_1403170 < baseStart_1403170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403199 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 2, 6]
def baseStart_1403199 : Nat := 118140960795 + 1403199 * 2 ^ 59
def prefixEnd_1403199 : Nat := 4983230072969 + 3 ^ 40 * 1403199 * 2
def baseEnd_1403199 : Nat := 240171846969453570386437

theorem tailTrace_1403199 : CollatzResearch.WordTrace tailWord_1403199 prefixEnd_1403199 240171846969453570386437 := by
  unfold tailWord_1403199
  simp only [CollatzResearch.WordTrace]
  refine ⟨51178872043457145155012651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34119248028971430103341767 51178872043457145155012651)
  ·
    refine ⟨76768308065185717732518977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51178872043457145155012651 76768308065185717732518977)
    ·
      refine ⟨57576231048889288299389233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76768308065185717732518977 57576231048889288299389233)
      ·
        refine ⟨43182173286666966224541925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57576231048889288299389233 43182173286666966224541925)
        ·
          refine ⟨8096657491250056167101611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43182173286666966224541925 8096657491250056167101611)
          ·
            refine ⟨12144986236875084250652417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8096657491250056167101611 12144986236875084250652417)
            ·
              refine ⟨9108739677656313187989313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12144986236875084250652417 9108739677656313187989313)
              ·
                refine ⟨6831554758242234890991985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9108739677656313187989313 6831554758242234890991985)
                ·
                  refine ⟨5123666068681676168243989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6831554758242234890991985 5123666068681676168243989)
                  ·
                    refine ⟨240171846969453570386437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5123666068681676168243989 240171846969453570386437)
                    ·
                      rfl

theorem cell23_1403199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_1403199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403199 prefixEnd_1403199 := by exact prefixLift 1403199
  have htrace : WordTrace (prefixWord ++ tailWord_1403199) baseStart_1403199 baseEnd_1403199 := by
    simpa [prefixWord, tailWord_1403199, baseEnd_1403199] using wordTrace_append hprefix tailTrace_1403199
  have hstable : (prefixWord ++ tailWord_1403199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403199).length < 2 ^ (prefixWord ++ tailWord_1403199).sum := by decide
  have hdescent : baseEnd_1403199 < baseStart_1403199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403201 : List Nat := [1, 2, 5, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1403201 : Nat := 118140960795 + 1403201 * 2 ^ 59
def prefixEnd_1403201 : Nat := 4983230072969 + 3 ^ 40 * 1403201 * 2
def baseEnd_1403201 : Nat := 720516567869669703334303

theorem tailTrace_1403201 : CollatzResearch.WordTrace tailWord_1403201 prefixEnd_1403201 720516567869669703334303 := by
  unfold tailWord_1403201
  simp only [CollatzResearch.WordTrace]
  refine ⟨51178944989449899496585457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34119296659633266331056971 51178944989449899496585457)
  ·
    refine ⟨38384208742087424622439093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51178944989449899496585457 38384208742087424622439093)
    ·
      refine ⟨3598519569570696058353665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38384208742087424622439093 3598519569570696058353665)
      ·
        refine ⟨2698889677178022043765249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3598519569570696058353665 2698889677178022043765249)
        ·
          refine ⟨2024167257883516532823937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2698889677178022043765249 2024167257883516532823937)
          ·
            refine ⟨1518125443412637399617953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2024167257883516532823937 1518125443412637399617953)
            ·
              refine ⟨1138594082559478049713465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518125443412637399617953 1138594082559478049713465)
              ·
                refine ⟨853945561919608537285099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138594082559478049713465 853945561919608537285099)
                ·
                  refine ⟨1280918342879412805927649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853945561919608537285099 1280918342879412805927649)
                  ·
                    refine ⟨960688757159559604445737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1280918342879412805927649 960688757159559604445737)
                    ·
                      refine ⟨720516567869669703334303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960688757159559604445737 720516567869669703334303)
                      ·
                        rfl

theorem cell23_1403201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1403201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403201 prefixEnd_1403201 := by exact prefixLift 1403201
  have htrace : WordTrace (prefixWord ++ tailWord_1403201) baseStart_1403201 baseEnd_1403201 := by
    simpa [prefixWord, tailWord_1403201, baseEnd_1403201] using wordTrace_append hprefix tailTrace_1403201
  have hstable : (prefixWord ++ tailWord_1403201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403201).length < 2 ^ (prefixWord ++ tailWord_1403201).sum := by decide
  have hdescent : baseEnd_1403201 < baseStart_1403201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403223 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 1, 4, 2]
def baseStart_1403223 : Nat := 118140960795 + 1403223 * 2 ^ 59
def prefixEnd_1403223 : Nat := 4983230072969 + 3 ^ 40 * 1403223 * 2
def baseEnd_1403223 : Nat := 720527864444068617259201

theorem tailTrace_1403223 : CollatzResearch.WordTrace tailWord_1403223 prefixEnd_1403223 720527864444068617259201 := by
  unfold tailWord_1403223
  simp only [CollatzResearch.WordTrace]
  refine ⟨51179747395370197253886323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34119831596913464835924215 51179747395370197253886323)
  ·
    refine ⟨76769621093055295880829485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51179747395370197253886323 76769621093055295880829485)
    ·
      refine ⟨28788607909895735955311057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76769621093055295880829485 28788607909895735955311057)
      ·
        refine ⟨21591455932421801966483293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28788607909895735955311057 21591455932421801966483293)
        ·
          refine ⟨8096795974658175737431235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21591455932421801966483293 8096795974658175737431235)
          ·
            refine ⟨12145193961987263606146853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8096795974658175737431235 12145193961987263606146853)
            ·
              refine ⟨2277223867872611926152535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12145193961987263606146853 2277223867872611926152535)
              ·
                refine ⟨3415835801808917889228803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277223867872611926152535 3415835801808917889228803)
                ·
                  refine ⟨5123753702713376833843205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415835801808917889228803 5123753702713376833843205)
                  ·
                    refine ⟨960703819258758156345601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5123753702713376833843205 960703819258758156345601)
                    ·
                      refine ⟨720527864444068617259201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960703819258758156345601 720527864444068617259201)
                      ·
                        rfl

theorem cell23_1403223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_1403223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403223 prefixEnd_1403223 := by exact prefixLift 1403223
  have htrace : WordTrace (prefixWord ++ tailWord_1403223) baseStart_1403223 baseEnd_1403223 := by
    simpa [prefixWord, tailWord_1403223, baseEnd_1403223] using wordTrace_append hprefix tailTrace_1403223
  have hstable : (prefixWord ++ tailWord_1403223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403223).length < 2 ^ (prefixWord ++ tailWord_1403223).sum := by decide
  have hdescent : baseEnd_1403223 < baseStart_1403223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403244 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 1, 3, 2]
def baseStart_1403244 : Nat := 118140960795 + 1403244 * 2 ^ 59
def prefixEnd_1403244 : Nat := 4983230072969 + 3 ^ 40 * 1403244 * 2
def baseEnd_1403244 : Nat := 720538647537813035096605

theorem tailTrace_1403244 : CollatzResearch.WordTrace tailWord_1403244 prefixEnd_1403244 720538647537813035096605 := by
  unfold tailWord_1403244
  simp only [CollatzResearch.WordTrace]
  refine ⟨25590256664147058920200393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34120342218862745226933857 25590256664147058920200393)
  ·
    refine ⟨19192692498110294190150295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25590256664147058920200393 19192692498110294190150295)
    ·
      refine ⟨28789038747165441285225443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19192692498110294190150295 28789038747165441285225443)
      ·
        refine ⟨43183558120748161927838165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28789038747165441285225443 43183558120748161927838165)
        ·
          refine ⟨1012114643455035045183707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43183558120748161927838165 1012114643455035045183707)
          ·
            refine ⟨1518171965182552567775561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012114643455035045183707 1518171965182552567775561)
            ·
              refine ⟨1138628973886914425831671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518171965182552567775561 1138628973886914425831671)
              ·
                refine ⟨1707943460830371638747507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138628973886914425831671 1707943460830371638747507)
                ·
                  refine ⟨2561915191245557458121261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1707943460830371638747507 2561915191245557458121261)
                  ·
                    refine ⟨960718196717084046795473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2561915191245557458121261 960718196717084046795473)
                    ·
                      refine ⟨720538647537813035096605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960718196717084046795473 720538647537813035096605)
                      ·
                        rfl

theorem cell23_1403244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_1403244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403244 prefixEnd_1403244 := by exact prefixLift 1403244
  have htrace : WordTrace (prefixWord ++ tailWord_1403244) baseStart_1403244 baseEnd_1403244 := by
    simpa [prefixWord, tailWord_1403244, baseEnd_1403244] using wordTrace_append hprefix tailTrace_1403244
  have hstable : (prefixWord ++ tailWord_1403244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403244).length < 2 ^ (prefixWord ++ tailWord_1403244).sum := by decide
  have hdescent : baseEnd_1403244 < baseStart_1403244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403269 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_1403269 : Nat := 118140960795 + 1403269 * 2 ^ 59
def prefixEnd_1403269 : Nat := 4983230072969 + 3 ^ 40 * 1403269 * 2
def baseEnd_1403269 : Nat := 720551484554175437283989

theorem tailTrace_1403269 : CollatzResearch.WordTrace tailWord_1403269 prefixEnd_1403269 720551484554175437283989 := by
  unfold tailWord_1403269
  simp only [CollatzResearch.WordTrace]
  refine ⟨51181425153203547110060861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34120950102135698073373907 51181425153203547110060861)
  ·
    refine ⟨19193034432451330166272823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51181425153203547110060861 19193034432451330166272823)
    ·
      refine ⟨28789551648676995249409235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19193034432451330166272823 28789551648676995249409235)
      ·
        refine ⟨43184327473015492874113853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28789551648676995249409235 43184327473015492874113853)
        ·
          refine ⟨16194122802380809827792695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43184327473015492874113853 16194122802380809827792695)
          ·
            refine ⟨24291184203571214741689043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16194122802380809827792695 24291184203571214741689043)
            ·
              refine ⟨36436776305356822112533565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24291184203571214741689043 36436776305356822112533565)
              ·
                refine ⟨13663791114508808292200087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36436776305356822112533565 13663791114508808292200087)
                ·
                  refine ⟨20495686671763212438300131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13663791114508808292200087 20495686671763212438300131)
                  ·
                    refine ⟨30743530007644818657450197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20495686671763212438300131 30743530007644818657450197)
                    ·
                      refine ⟨720551484554175437283989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30743530007644818657450197 720551484554175437283989)
                      ·
                        rfl

theorem cell23_1403269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_1403269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403269 prefixEnd_1403269 := by exact prefixLift 1403269
  have htrace : WordTrace (prefixWord ++ tailWord_1403269) baseStart_1403269 baseEnd_1403269 := by
    simpa [prefixWord, tailWord_1403269, baseEnd_1403269] using wordTrace_append hprefix tailTrace_1403269
  have hstable : (prefixWord ++ tailWord_1403269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403269).length < 2 ^ (prefixWord ++ tailWord_1403269).sum := by decide
  have hdescent : baseEnd_1403269 < baseStart_1403269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403274 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1403274 : Nat := 118140960795 + 1403274 * 2 ^ 59
def prefixEnd_1403274 : Nat := 4983230072969 + 3 ^ 40 * 1403274 * 2
def baseEnd_1403274 : Nat := 720554051957447917721467

theorem tailTrace_1403274 : CollatzResearch.WordTrace tailWord_1403274 prefixEnd_1403274 720554051957447917721467 := by
  unfold tailWord_1403274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795401879546358240998219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34121071678790288642661917 12795401879546358240998219)
  ·
    refine ⟨19193102819319537361497329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12795401879546358240998219 19193102819319537361497329)
    ·
      refine ⟨14394827114489653021122997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19193102819319537361497329 14394827114489653021122997)
      ·
        refine ⟨1349515041983404970730281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14394827114489653021122997 1349515041983404970730281)
        ·
          refine ⟨1012136281487553728047711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1349515041983404970730281 1012136281487553728047711)
          ·
            refine ⟨1518204422231330592071567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012136281487553728047711 1518204422231330592071567)
            ·
              refine ⟨2277306633346995888107351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518204422231330592071567 2277306633346995888107351)
              ·
                refine ⟨3415959950020493832161027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277306633346995888107351 3415959950020493832161027)
                ·
                  refine ⟨5123939925030740748241541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415959950020493832161027 5123939925030740748241541)
                  ·
                    refine ⟨960738735943263890295289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5123939925030740748241541 960738735943263890295289)
                    ·
                      refine ⟨720554051957447917721467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960738735943263890295289 720554051957447917721467)
                      ·
                        rfl

theorem cell23_1403274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1403274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403274 prefixEnd_1403274 := by exact prefixLift 1403274
  have htrace : WordTrace (prefixWord ++ tailWord_1403274) baseStart_1403274 baseEnd_1403274 := by
    simpa [prefixWord, tailWord_1403274, baseEnd_1403274] using wordTrace_append hprefix tailTrace_1403274
  have hstable : (prefixWord ++ tailWord_1403274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403274).length < 2 ^ (prefixWord ++ tailWord_1403274).sum := by decide
  have hdescent : baseEnd_1403274 < baseStart_1403274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403289 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 2, 8]
def baseStart_1403289 : Nat := 118140960795 + 1403289 * 2 ^ 59
def prefixEnd_1403289 : Nat := 4983230072969 + 3 ^ 40 * 1403289 * 2
def baseEnd_1403289 : Nat := 240187251389088453011299

theorem tailTrace_1403289 : CollatzResearch.WordTrace tailWord_1403289 prefixEnd_1403289 240187251389088453011299 := by
  unfold tailWord_1403289
  simp only [CollatzResearch.WordTrace]
  refine ⟨51182154613131090525788921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34121436408754060350525947 51182154613131090525788921)
  ·
    refine ⟨38386615959848317894341691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51182154613131090525788921 38386615959848317894341691)
    ·
      refine ⟨57579923939772476841512537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38386615959848317894341691 57579923939772476841512537)
      ·
        refine ⟨43184942954829357631134403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57579923939772476841512537 43184942954829357631134403)
        ·
          refine ⟨64777414432244036446701605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43184942954829357631134403 64777414432244036446701605)
          ·
            refine ⟨12145765206045756833756551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64777414432244036446701605 12145765206045756833756551)
            ·
              refine ⟨18218647809068635250634827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12145765206045756833756551 18218647809068635250634827)
              ·
                refine ⟨27327971713602952875952241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18218647809068635250634827 27327971713602952875952241)
                ·
                  refine ⟨20495978785202214656964181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27327971713602952875952241 20495978785202214656964181)
                  ·
                    refine ⟨240187251389088453011299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20495978785202214656964181 240187251389088453011299)
                    ·
                      rfl

theorem cell23_1403289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_1403289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403289 prefixEnd_1403289 := by exact prefixLift 1403289
  have htrace : WordTrace (prefixWord ++ tailWord_1403289) baseStart_1403289 baseEnd_1403289 := by
    simpa [prefixWord, tailWord_1403289, baseEnd_1403289] using wordTrace_append hprefix tailTrace_1403289
  have hstable : (prefixWord ++ tailWord_1403289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403289).length < 2 ^ (prefixWord ++ tailWord_1403289).sum := by decide
  have hdescent : baseEnd_1403289 < baseStart_1403289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403296 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1403296 : Nat := 118140960795 + 1403296 * 2 ^ 59
def prefixEnd_1403296 : Nat := 4983230072969 + 3 ^ 40 * 1403296 * 2
def baseEnd_1403296 : Nat := 720565348531846831646365

theorem tailTrace_1403296 : CollatzResearch.WordTrace tailWord_1403296 prefixEnd_1403296 720565348531846831646365 := by
  unfold tailWord_1403296
  simp only [CollatzResearch.WordTrace]
  refine ⟨25591204962052865360646871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34121606616070487147529161 25591204962052865360646871)
  ·
    refine ⟨38386807443079298040970307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25591204962052865360646871 38386807443079298040970307)
    ·
      refine ⟨57580211164618947061455461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38386807443079298040970307 57580211164618947061455461)
      ·
        refine ⟨10796289593366052574022899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57580211164618947061455461 10796289593366052574022899)
        ·
          refine ⟨16194434390049078861034349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10796289593366052574022899 16194434390049078861034349)
          ·
            refine ⟨6072912896268404572887881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16194434390049078861034349 6072912896268404572887881)
            ·
              refine ⟨4554684672201303429665911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6072912896268404572887881 4554684672201303429665911)
              ·
                refine ⟨6832027008301955144498867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4554684672201303429665911 6832027008301955144498867)
                ·
                  refine ⟨10248040512452932716748301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6832027008301955144498867 10248040512452932716748301)
                  ·
                    refine ⟨3843015192169849768780613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10248040512452932716748301 3843015192169849768780613)
                    ·
                      refine ⟨720565348531846831646365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3843015192169849768780613 720565348531846831646365)
                      ·
                        rfl

theorem cell23_1403296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1403296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403296 prefixEnd_1403296 := by exact prefixLift 1403296
  have htrace : WordTrace (prefixWord ++ tailWord_1403296) baseStart_1403296 baseEnd_1403296 := by
    simpa [prefixWord, tailWord_1403296, baseEnd_1403296] using wordTrace_append hprefix tailTrace_1403296
  have hstable : (prefixWord ++ tailWord_1403296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403296).length < 2 ^ (prefixWord ++ tailWord_1403296).sum := by decide
  have hdescent : baseEnd_1403296 < baseStart_1403296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403297 : List Nat := [1, 2, 3, 5, 1, 2, 1, 3, 5]
def baseStart_1403297 : Nat := 118140960795 + 1403297 * 2 ^ 59
def prefixEnd_1403297 : Nat := 4983230072969 + 3 ^ 40 * 1403297 * 2
def baseEnd_1403297 : Nat := 80062873556944591970429

theorem tailTrace_1403297 : CollatzResearch.WordTrace tailWord_1403297 prefixEnd_1403297 80062873556944591970429 := by
  unfold tailWord_1403297
  simp only [CollatzResearch.WordTrace]
  refine ⟨51182446397102107892080145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34121630931401405261386763 51182446397102107892080145)
  ·
    refine ⟨38386834797826580919060109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51182446397102107892080145 38386834797826580919060109)
    ·
      refine ⟨14395063049184967844647541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38386834797826580919060109 14395063049184967844647541)
      ·
        refine ⟨1349537160861090735435707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14395063049184967844647541 1349537160861090735435707)
        ·
          refine ⟨2024305741291636103153561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349537160861090735435707 2024305741291636103153561)
          ·
            refine ⟨1518229305968727077365171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2024305741291636103153561 1518229305968727077365171)
            ·
              refine ⟨2277343958953090616047757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518229305968727077365171 2277343958953090616047757)
              ·
                refine ⟨854003984607408981017909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2277343958953090616047757 854003984607408981017909)
                ·
                  refine ⟨80062873556944591970429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 854003984607408981017909 80062873556944591970429)
                  ·
                    rfl

theorem cell23_1403297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 5].length) (baseStart_1403297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403297 prefixEnd_1403297 := by exact prefixLift 1403297
  have htrace : WordTrace (prefixWord ++ tailWord_1403297) baseStart_1403297 baseEnd_1403297 := by
    simpa [prefixWord, tailWord_1403297, baseEnd_1403297] using wordTrace_append hprefix tailTrace_1403297
  have hstable : (prefixWord ++ tailWord_1403297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403297).length < 2 ^ (prefixWord ++ tailWord_1403297).sum := by decide
  have hdescent : baseEnd_1403297 < baseStart_1403297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403313 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1403313 : Nat := 118140960795 + 1403313 * 2 ^ 59
def prefixEnd_1403313 : Nat := 4983230072969 + 3 ^ 40 * 1403313 * 2
def baseEnd_1403313 : Nat := 720574077702973265133787

theorem tailTrace_1403313 : CollatzResearch.WordTrace tailWord_1403313 prefixEnd_1403313 720574077702973265133787 := by
  unfold tailWord_1403313
  simp only [CollatzResearch.WordTrace]
  refine ⟨51183029965044142624662593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34122019976696095083108395 51183029965044142624662593)
  ·
    refine ⟨38387272473783106968496945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51183029965044142624662593 38387272473783106968496945)
    ·
      refine ⟨28790454355337330226372709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38387272473783106968496945 28790454355337330226372709)
      ·
        refine ⟨5398210191625749417444883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28790454355337330226372709 5398210191625749417444883)
        ·
          refine ⟨8097315287438624126167325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398210191625749417444883 8097315287438624126167325)
          ·
            refine ⟨3036493232789484047312747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8097315287438624126167325 3036493232789484047312747)
            ·
              refine ⟨4554739849184226070969121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036493232789484047312747 4554739849184226070969121)
              ·
                refine ⟨3416054886888169553226841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4554739849184226070969121 3416054886888169553226841)
                ·
                  refine ⟨2562041165166127164920131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3416054886888169553226841 2562041165166127164920131)
                  ·
                    refine ⟨3843061747749190747380197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2562041165166127164920131 3843061747749190747380197)
                    ·
                      refine ⟨720574077702973265133787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3843061747749190747380197 720574077702973265133787)
                      ·
                        rfl

theorem cell23_1403313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1403313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403313 prefixEnd_1403313 := by exact prefixLift 1403313
  have htrace : WordTrace (prefixWord ++ tailWord_1403313) baseStart_1403313 baseEnd_1403313 := by
    simpa [prefixWord, tailWord_1403313, baseEnd_1403313] using wordTrace_append hprefix tailTrace_1403313
  have hstable : (prefixWord ++ tailWord_1403313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403313).length < 2 ^ (prefixWord ++ tailWord_1403313).sum := by decide
  have hdescent : baseEnd_1403313 < baseStart_1403313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403326 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1403326 : Nat := 118140960795 + 1403326 * 2 ^ 59
def prefixEnd_1403326 : Nat := 4983230072969 + 3 ^ 40 * 1403326 * 2
def baseEnd_1403326 : Nat := 720580752951481714271227

theorem tailTrace_1403326 : CollatzResearch.WordTrace tailWord_1403326 prefixEnd_1403326 720580752951481714271227 := by
  unfold tailWord_1403326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6397938014249630730610729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34122336075998030563257221 6397938014249630730610729)
  ·
    refine ⟨4798453510687223047958047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6397938014249630730610729 4798453510687223047958047)
    ·
      refine ⟨7197680266030834571937071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4798453510687223047958047 7197680266030834571937071)
      ·
        refine ⟨10796520399046251857905607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7197680266030834571937071 10796520399046251857905607)
        ·
          refine ⟨16194780598569377786858411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10796520399046251857905607 16194780598569377786858411)
          ·
            refine ⟨24292170897854066680287617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16194780598569377786858411 24292170897854066680287617)
            ·
              refine ⟨18219128173390550010215713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24292170897854066680287617 18219128173390550010215713)
              ·
                refine ⟨13664346130042912507661785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18219128173390550010215713 13664346130042912507661785)
                ·
                  refine ⟨10248259597532184380746339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13664346130042912507661785 10248259597532184380746339)
                  ·
                    refine ⟨15372389396298276571119509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10248259597532184380746339 15372389396298276571119509)
                    ·
                      refine ⟨720580752951481714271227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15372389396298276571119509 720580752951481714271227)
                      ·
                        rfl

theorem cell23_1403326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1403326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403326 prefixEnd_1403326 := by exact prefixLift 1403326
  have htrace : WordTrace (prefixWord ++ tailWord_1403326) baseStart_1403326 baseEnd_1403326 := by
    simpa [prefixWord, tailWord_1403326, baseEnd_1403326] using wordTrace_append hprefix tailTrace_1403326
  have hstable : (prefixWord ++ tailWord_1403326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403326).length < 2 ^ (prefixWord ++ tailWord_1403326).sum := by decide
  have hdescent : baseEnd_1403326 < baseStart_1403326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403374 : List Nat := [4, 1, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1403374 : Nat := 118140960795 + 1403374 * 2 ^ 59
def prefixEnd_1403374 : Nat := 4983230072969 + 3 ^ 40 * 1403374 * 2
def baseEnd_1403374 : Nat := 240201800007632508823669

theorem tailTrace_1403374 : CollatzResearch.WordTrace tailWord_1403374 prefixEnd_1403374 240201800007632508823669 := by
  unfold tailWord_1403374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6398156852227893755329147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34123503211882100028422117 6398156852227893755329147)
  ·
    refine ⟨9597235278341840632993721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6398156852227893755329147 9597235278341840632993721)
    ·
      refine ⟨7197926458756380474745291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9597235278341840632993721 7197926458756380474745291)
      ·
        refine ⟨10796889688134570712117937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7197926458756380474745291 10796889688134570712117937)
        ·
          refine ⟨8097667266100928034088453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10796889688134570712117937 8097667266100928034088453)
          ·
            refine ⟨1518312612393924006391585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8097667266100928034088453 1518312612393924006391585)
            ·
              refine ⟨1138734459295443004793689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518312612393924006391585 1138734459295443004793689)
              ·
                refine ⟨854050844471582253595267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138734459295443004793689 854050844471582253595267)
                ·
                  refine ⟨1281076266707373380392901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854050844471582253595267 1281076266707373380392901)
                  ·
                    refine ⟨240201800007632508823669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1281076266707373380392901 240201800007632508823669)
                    ·
                      rfl

theorem cell23_1403374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1403374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403374 prefixEnd_1403374 := by exact prefixLift 1403374
  have htrace : WordTrace (prefixWord ++ tailWord_1403374) baseStart_1403374 baseEnd_1403374 := by
    simpa [prefixWord, tailWord_1403374, baseEnd_1403374] using wordTrace_append hprefix tailTrace_1403374
  have hstable : (prefixWord ++ tailWord_1403374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403374).length < 2 ^ (prefixWord ++ tailWord_1403374).sum := by decide
  have hdescent : baseEnd_1403374 < baseStart_1403374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403403 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 4]
def baseStart_1403403 : Nat := 118140960795 + 1403403 * 2 ^ 59
def prefixEnd_1403403 : Nat := 4983230072969 + 3 ^ 40 * 1403403 * 2
def baseEnd_1403403 : Nat := 720620290961877913008373

theorem tailTrace_1403403 : CollatzResearch.WordTrace tailWord_1403403 prefixEnd_1403403 720620290961877913008373 := by
  unfold tailWord_1403403
  simp only [CollatzResearch.WordTrace]
  refine ⟨51186312534718087995438863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34124208356478725330292575 51186312534718087995438863)
  ·
    refine ⟨76779468802077131993158295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51186312534718087995438863 76779468802077131993158295)
    ·
      refine ⟨115169203203115697989737443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76779468802077131993158295 115169203203115697989737443)
      ·
        refine ⟨172753804804673546984606165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115169203203115697989737443 172753804804673546984606165)
        ·
          refine ⟨4048917300109536257451707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 172753804804673546984606165 4048917300109536257451707)
          ·
            refine ⟨6073375950164304386177561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4048917300109536257451707 6073375950164304386177561)
            ·
              refine ⟨4555031962623228289633171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6073375950164304386177561 4555031962623228289633171)
              ·
                refine ⟨6832547943934842434449757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555031962623228289633171 6832547943934842434449757)
                ·
                  refine ⟨2562205478975565912918659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6832547943934842434449757 2562205478975565912918659)
                  ·
                    refine ⟨3843308218463348869377989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2562205478975565912918659 3843308218463348869377989)
                    ·
                      refine ⟨720620290961877913008373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3843308218463348869377989 720620290961877913008373)
                      ·
                        rfl

theorem cell23_1403403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 4].length) (baseStart_1403403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403403 prefixEnd_1403403 := by exact prefixLift 1403403
  have htrace : WordTrace (prefixWord ++ tailWord_1403403) baseStart_1403403 baseEnd_1403403 := by
    simpa [prefixWord, tailWord_1403403, baseEnd_1403403] using wordTrace_append hprefix tailTrace_1403403
  have hstable : (prefixWord ++ tailWord_1403403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403403).length < 2 ^ (prefixWord ++ tailWord_1403403).sum := by decide
  have hdescent : baseEnd_1403403 < baseStart_1403403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403413 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_1403413 : Nat := 118140960795 + 1403413 * 2 ^ 59
def prefixEnd_1403413 : Nat := 4983230072969 + 3 ^ 40 * 1403413 * 2
def baseEnd_1403413 : Nat := 240208475256140957961109

theorem tailTrace_1403413 : CollatzResearch.WordTrace tailWord_1403413 prefixEnd_1403413 240208475256140957961109 := by
  unfold tailWord_1403413
  simp only [CollatzResearch.WordTrace]
  refine ⟨51186677264681859703302893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34124451509787906468868595 51186677264681859703302893)
  ·
    refine ⟨19195003974255697388738585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51186677264681859703302893 19195003974255697388738585)
    ·
      refine ⟨14396252980691773041553939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19195003974255697388738585 14396252980691773041553939)
      ·
        refine ⟨21594379471037659562330909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14396252980691773041553939 21594379471037659562330909)
        ·
          refine ⟨8097892301639122335874091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21594379471037659562330909 8097892301639122335874091)
          ·
            refine ⟨12146838452458683503811137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8097892301639122335874091 12146838452458683503811137)
            ·
              refine ⟨9110128839344012627858353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12146838452458683503811137 9110128839344012627858353)
              ·
                refine ⟨6832596629508009470893765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9110128839344012627858353 6832596629508009470893765)
                ·
                  refine ⟨1281111868032751775792581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6832596629508009470893765 1281111868032751775792581)
                  ·
                    refine ⟨240208475256140957961109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1281111868032751775792581 240208475256140957961109)
                    ·
                      rfl

theorem cell23_1403413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_1403413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403413 prefixEnd_1403413 := by exact prefixLift 1403413
  have htrace : WordTrace (prefixWord ++ tailWord_1403413) baseStart_1403413 baseEnd_1403413 := by
    simpa [prefixWord, tailWord_1403413, baseEnd_1403413] using wordTrace_append hprefix tailTrace_1403413
  have hstable : (prefixWord ++ tailWord_1403413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403413).length < 2 ^ (prefixWord ++ tailWord_1403413).sum := by decide
  have hdescent : baseEnd_1403413 < baseStart_1403413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403420 : List Nat := [2, 2, 3, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_1403420 : Nat := 118140960795 + 1403420 * 2 ^ 59
def prefixEnd_1403420 : Nat := 4983230072969 + 3 ^ 40 * 1403420 * 2
def baseEnd_1403420 : Nat := 720629020133004346495795

theorem tailTrace_1403420 : CollatzResearch.WordTrace tailWord_1403420 prefixEnd_1403420 720629020133004346495795 := by
  unfold tailWord_1403420
  simp only [CollatzResearch.WordTrace]
  refine ⟨25593466287828249949403857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34124621717104333265871809 25593466287828249949403857)
  ·
    refine ⟨19195099715871187462052893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25593466287828249949403857 19195099715871187462052893)
    ·
      refine ⟨7198162393451695298269835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19195099715871187462052893 7198162393451695298269835)
      ·
        refine ⟨10797243590177542947404753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7198162393451695298269835 10797243590177542947404753)
        ·
          refine ⟨8097932692633157210553565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10797243590177542947404753 8097932692633157210553565)
          ·
            refine ⟨3036724759737433953957587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8097932692633157210553565 3036724759737433953957587)
            ·
              refine ⟨4555087139606150930936381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3036724759737433953957587 4555087139606150930936381)
              ·
                refine ⟨1708157677352306599101143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4555087139606150930936381 1708157677352306599101143)
                ·
                  refine ⟨2562236516028459898651715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708157677352306599101143 2562236516028459898651715)
                  ·
                    refine ⟨3843354774042689847977573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2562236516028459898651715 3843354774042689847977573)
                    ·
                      refine ⟨720629020133004346495795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3843354774042689847977573 720629020133004346495795)
                      ·
                        rfl

theorem cell23_1403420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_1403420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403420 prefixEnd_1403420 := by exact prefixLift 1403420
  have htrace : WordTrace (prefixWord ++ tailWord_1403420) baseStart_1403420 baseEnd_1403420 := by
    simpa [prefixWord, tailWord_1403420, baseEnd_1403420] using wordTrace_append hprefix tailTrace_1403420
  have hstable : (prefixWord ++ tailWord_1403420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403420).length < 2 ^ (prefixWord ++ tailWord_1403420).sum := by decide
  have hdescent : baseEnd_1403420 < baseStart_1403420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403450 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4]
def baseStart_1403450 : Nat := 118140960795 + 1403450 * 2 ^ 59
def prefixEnd_1403450 : Nat := 4983230072969 + 3 ^ 40 * 1403450 * 2
def baseEnd_1403450 : Nat := 720644424552639229120657

theorem tailTrace_1403450 : CollatzResearch.WordTrace tailWord_1403450 prefixEnd_1403450 720644424552639229120657 := by
  unfold tailWord_1403450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12797006691386953755599951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34125351177031876681599869 12797006691386953755599951)
  ·
    refine ⟨19195510037080430633399927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12797006691386953755599951 19195510037080430633399927)
    ·
      refine ⟨28793265055620645950099891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19195510037080430633399927 28793265055620645950099891)
      ·
        refine ⟨43189897583430968925149837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28793265055620645950099891 43189897583430968925149837)
        ·
          refine ⟨16196211593786613346931189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43189897583430968925149837 16196211593786613346931189)
          ·
            refine ⟨1518394836917495001274799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16196211593786613346931189 1518394836917495001274799)
            ·
              refine ⟨2277592255376242501912199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518394836917495001274799 2277592255376242501912199)
              ·
                refine ⟨3416388383064363752868299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2277592255376242501912199 3416388383064363752868299)
                ·
                  refine ⟨5124582574596545629302449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3416388383064363752868299 5124582574596545629302449)
                  ·
                    refine ⟨3843436930947409221976837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5124582574596545629302449 3843436930947409221976837)
                    ·
                      refine ⟨720644424552639229120657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3843436930947409221976837 720644424552639229120657)
                      ·
                        rfl

theorem cell23_1403450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_1403450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403450 prefixEnd_1403450 := by exact prefixLift 1403450
  have htrace : WordTrace (prefixWord ++ tailWord_1403450) baseStart_1403450 baseEnd_1403450 := by
    simpa [prefixWord, tailWord_1403450, baseEnd_1403450] using wordTrace_append hprefix tailTrace_1403450
  have hstable : (prefixWord ++ tailWord_1403450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403450).length < 2 ^ (prefixWord ++ tailWord_1403450).sum := by decide
  have hdescent : baseEnd_1403450 < baseStart_1403450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403454 : List Nat := [4, 2, 1, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1403454 : Nat := 118140960795 + 1403454 * 2 ^ 59
def prefixEnd_1403454 : Nat := 4983230072969 + 3 ^ 40 * 1403454 * 2
def baseEnd_1403454 : Nat := 720646478475257213470639

theorem tailTrace_1403454 : CollatzResearch.WordTrace tailWord_1403454 prefixEnd_1403454 720646478475257213470639 := by
  unfold tailWord_1403454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6398521582191665463193177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34125448438355549137030277 6398521582191665463193177)
  ·
    refine ⟨4798891186643749097394883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6398521582191665463193177 4798891186643749097394883)
    ·
      refine ⟨7198336779965623646092325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4798891186643749097394883 7198336779965623646092325)
      ·
        refine ⟨1349688146243554433642311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7198336779965623646092325 1349688146243554433642311)
        ·
          refine ⟨2024532219365331650463467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349688146243554433642311 2024532219365331650463467)
          ·
            refine ⟨3036798329047997475695201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024532219365331650463467 3036798329047997475695201)
            ·
              refine ⟨2277598746785998106771401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3036798329047997475695201 2277598746785998106771401)
              ·
                refine ⟨1708199060089498580078551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277598746785998106771401 1708199060089498580078551)
                ·
                  refine ⟨2562298590134247870117827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708199060089498580078551 2562298590134247870117827)
                  ·
                    refine ⟨3843447885201371805176741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2562298590134247870117827 3843447885201371805176741)
                    ·
                      refine ⟨720646478475257213470639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3843447885201371805176741 720646478475257213470639)
                      ·
                        rfl

theorem cell23_1403454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1403454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403454 prefixEnd_1403454 := by exact prefixLift 1403454
  have htrace : WordTrace (prefixWord ++ tailWord_1403454) baseStart_1403454 baseEnd_1403454 := by
    simpa [prefixWord, tailWord_1403454, baseEnd_1403454] using wordTrace_append hprefix tailTrace_1403454
  have hstable : (prefixWord ++ tailWord_1403454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403454).length < 2 ^ (prefixWord ++ tailWord_1403454).sum := by decide
  have hdescent : baseEnd_1403454 < baseStart_1403454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403456 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 2, 7]
def baseStart_1403456 : Nat := 118140960795 + 1403456 * 2 ^ 59
def prefixEnd_1403456 : Nat := 4983230072969 + 3 ^ 40 * 1403456 * 2
def baseEnd_1403456 : Nat := 240215835145522068548543

theorem tailTrace_1403456 : CollatzResearch.WordTrace tailWord_1403456 prefixEnd_1403456 240215835145522068548543 := by
  unfold tailWord_1403456
  simp only [CollatzResearch.WordTrace]
  refine ⟨25594122801763039023559111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34125497069017385364745481 25594122801763039023559111)
  ·
    refine ⟨38391184202644558535338667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25594122801763039023559111 38391184202644558535338667)
    ·
      refine ⟨57586776303966837803008001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38391184202644558535338667 57586776303966837803008001)
      ·
        refine ⟨43190082227975128352256001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57586776303966837803008001 43190082227975128352256001)
        ·
          refine ⟨32392561670981346264192001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43190082227975128352256001 32392561670981346264192001)
          ·
            refine ⟨24294421253236009698144001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32392561670981346264192001 24294421253236009698144001)
            ·
              refine ⟨18220815939927007273608001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24294421253236009698144001 18220815939927007273608001)
              ·
                refine ⟨13665611954945255455206001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18220815939927007273608001 13665611954945255455206001)
                ·
                  refine ⟨10249208966208941591404501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13665611954945255455206001 10249208966208941591404501)
                  ·
                    refine ⟨240215835145522068548543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10249208966208941591404501 240215835145522068548543)
                    ·
                      rfl

theorem cell23_1403456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_1403456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403456 prefixEnd_1403456 := by exact prefixLift 1403456
  have htrace : WordTrace (prefixWord ++ tailWord_1403456) baseStart_1403456 baseEnd_1403456 := by
    simpa [prefixWord, tailWord_1403456, baseEnd_1403456] using wordTrace_append hprefix tailTrace_1403456
  have hstable : (prefixWord ++ tailWord_1403456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403456).length < 2 ^ (prefixWord ++ tailWord_1403456).sum := by decide
  have hdescent : baseEnd_1403456 < baseStart_1403456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403457 : List Nat := [1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1403457 : Nat := 118140960795 + 1403457 * 2 ^ 59
def prefixEnd_1403457 : Nat := 4983230072969 + 3 ^ 40 * 1403457 * 2
def baseEnd_1403457 : Nat := 720648018917220701733125

theorem tailTrace_1403457 : CollatzResearch.WordTrace tailWord_1403457 prefixEnd_1403457 720648018917220701733125 := by
  unfold tailWord_1403457
  simp only [CollatzResearch.WordTrace]
  refine ⟨51188282076522455217904625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34125521384348303478603083 51188282076522455217904625)
  ·
    refine ⟨38391211557391841413428469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51188282076522455217904625 38391211557391841413428469)
    ·
      refine ⟨3599176083505485132508919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38391211557391841413428469 3599176083505485132508919)
      ·
        refine ⟨5398764125258227698763379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3599176083505485132508919 5398764125258227698763379)
        ·
          refine ⟨8098146187887341548145069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398764125258227698763379 8098146187887341548145069)
          ·
            refine ⟨3036804820457753080554401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8098146187887341548145069 3036804820457753080554401)
            ·
              refine ⟨2277603615343314810415801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3036804820457753080554401 2277603615343314810415801)
              ·
                refine ⟨1708202711507486107811851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277603615343314810415801 1708202711507486107811851)
                ·
                  refine ⟨2562304067261229161717777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708202711507486107811851 2562304067261229161717777)
                  ·
                    refine ⟨1921728050445921871288333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2562304067261229161717777 1921728050445921871288333)
                    ·
                      refine ⟨720648018917220701733125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1921728050445921871288333 720648018917220701733125)
                      ·
                        rfl

theorem cell23_1403457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1403457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403457 prefixEnd_1403457 := by exact prefixLift 1403457
  have htrace : WordTrace (prefixWord ++ tailWord_1403457) baseStart_1403457 baseEnd_1403457 := by
    simpa [prefixWord, tailWord_1403457, baseEnd_1403457] using wordTrace_append hprefix tailTrace_1403457
  have hstable : (prefixWord ++ tailWord_1403457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403457).length < 2 ^ (prefixWord ++ tailWord_1403457).sum := by decide
  have hdescent : baseEnd_1403457 < baseStart_1403457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403470 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_1403470 : Nat := 118140960795 + 1403470 * 2 ^ 59
def prefixEnd_1403470 : Nat := 4983230072969 + 3 ^ 40 * 1403470 * 2
def baseEnd_1403470 : Nat := 720654694165729150870565

theorem tailTrace_1403470 : CollatzResearch.WordTrace tailWord_1403470 prefixEnd_1403470 720654694165729150870565 := by
  unfold tailWord_1403470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6398594528184419804765983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34125837483650238958751909 6398594528184419804765983)
  ·
    refine ⟨9597891792276629707148975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6398594528184419804765983 9597891792276629707148975)
    ·
      refine ⟨14396837688414944560723463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9597891792276629707148975 14396837688414944560723463)
      ·
        refine ⟨21595256532622416841085195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14396837688414944560723463 21595256532622416841085195)
        ·
          refine ⟨32392884798933625261627793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21595256532622416841085195 32392884798933625261627793)
          ·
            refine ⟨24294663599200218946220845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32392884798933625261627793 24294663599200218946220845)
            ·
              refine ⟨9110498849700082104832817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24294663599200218946220845 9110498849700082104832817)
              ·
                refine ⟨6832874137275061578624613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9110498849700082104832817 6832874137275061578624613)
                ·
                  refine ⟨1281163900739074045992115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6832874137275061578624613 1281163900739074045992115)
                  ·
                    refine ⟨1921745851108611068988173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1281163900739074045992115 1921745851108611068988173)
                    ·
                      refine ⟨720654694165729150870565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1921745851108611068988173 720654694165729150870565)
                      ·
                        rfl

theorem cell23_1403470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_1403470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403470 prefixEnd_1403470 := by exact prefixLift 1403470
  have htrace : WordTrace (prefixWord ++ tailWord_1403470) baseStart_1403470 baseEnd_1403470 := by
    simpa [prefixWord, tailWord_1403470, baseEnd_1403470] using wordTrace_append hprefix tailTrace_1403470
  have hstable : (prefixWord ++ tailWord_1403470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403470).length < 2 ^ (prefixWord ++ tailWord_1403470).sum := by decide
  have hdescent : baseEnd_1403470 < baseStart_1403470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403513 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1403513 : Nat := 118140960795 + 1403513 * 2 ^ 59
def prefixEnd_1403513 : Nat := 4983230072969 + 3 ^ 40 * 1403513 * 2
def baseEnd_1403513 : Nat := 720676773833872482632867

theorem tailTrace_1403513 : CollatzResearch.WordTrace tailWord_1403513 prefixEnd_1403513 720676773833872482632867 := by
  unfold tailWord_1403513
  simp only [CollatzResearch.WordTrace]
  refine ⟨51190324564319576781943193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34126883042879717854628795 51190324564319576781943193)
  ·
    refine ⟨38392743423239682586457395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51190324564319576781943193 38392743423239682586457395)
    ·
      refine ⟨57589115134859523879686093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38392743423239682586457395 57589115134859523879686093)
      ·
        refine ⟨21595918175572321454882285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57589115134859523879686093 21595918175572321454882285)
        ·
          refine ⟨8098469315839620545580857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21595918175572321454882285 8098469315839620545580857)
          ·
            refine ⟨6073851986879715409185643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8098469315839620545580857 6073851986879715409185643)
            ·
              refine ⟨9110777980319573113778465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073851986879715409185643 9110777980319573113778465)
              ·
                refine ⟨6833083485239679835333849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9110777980319573113778465 6833083485239679835333849)
                ·
                  refine ⟨5124812613929759876500387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6833083485239679835333849 5124812613929759876500387)
                  ·
                    refine ⟨7687218920894639814750581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5124812613929759876500387 7687218920894639814750581)
                    ·
                      refine ⟨720676773833872482632867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7687218920894639814750581 720676773833872482632867)
                      ·
                        rfl

theorem cell23_1403513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1403513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403513 prefixEnd_1403513 := by exact prefixLift 1403513
  have htrace : WordTrace (prefixWord ++ tailWord_1403513) baseStart_1403513 baseEnd_1403513 := by
    simpa [prefixWord, tailWord_1403513, baseEnd_1403513] using wordTrace_append hprefix tailTrace_1403513
  have hstable : (prefixWord ++ tailWord_1403513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403513).length < 2 ^ (prefixWord ++ tailWord_1403513).sum := by decide
  have hdescent : baseEnd_1403513 < baseStart_1403513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403544 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 2, 2, 2]
def baseStart_1403544 : Nat := 118140960795 + 1403544 * 2 ^ 59
def prefixEnd_1403544 : Nat := 4983230072969 + 3 ^ 40 * 1403544 * 2
def baseEnd_1403544 : Nat := 720692691734161861345225

theorem tailTrace_1403544 : CollatzResearch.WordTrace tailWord_1403544 prefixEnd_1403544 720692691734161861345225 := by
  unfold tailWord_1403544
  simp only [CollatzResearch.WordTrace]
  refine ⟨25595727613603634538160843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34127636818138179384214457 25595727613603634538160843)
  ·
    refine ⟨38393591420405451807241265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25595727613603634538160843 38393591420405451807241265)
    ·
      refine ⟨28795193565304088855430949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38393591420405451807241265 28795193565304088855430949)
      ·
        refine ⟨5399098793494516660393303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28795193565304088855430949 5399098793494516660393303)
        ·
          refine ⟨8098648190241774990589955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399098793494516660393303 8098648190241774990589955)
          ·
            refine ⟨12147972285362662485884933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8098648190241774990589955 12147972285362662485884933)
            ·
              refine ⟨2277744803505499216103425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12147972285362662485884933 2277744803505499216103425)
              ·
                refine ⟨1708308602629124412077569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2277744803505499216103425 1708308602629124412077569)
                ·
                  refine ⟨1281231451971843309058177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1708308602629124412077569 1281231451971843309058177)
                  ·
                    refine ⟨960923588978882481793633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1281231451971843309058177 960923588978882481793633)
                    ·
                      refine ⟨720692691734161861345225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960923588978882481793633 720692691734161861345225)
                      ·
                        rfl

theorem cell23_1403544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_1403544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403544 prefixEnd_1403544 := by exact prefixLift 1403544
  have htrace : WordTrace (prefixWord ++ tailWord_1403544) baseStart_1403544 baseEnd_1403544 := by
    simpa [prefixWord, tailWord_1403544, baseEnd_1403544] using wordTrace_append hprefix tailTrace_1403544
  have hstable : (prefixWord ++ tailWord_1403544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403544).length < 2 ^ (prefixWord ++ tailWord_1403544).sum := by decide
  have hdescent : baseEnd_1403544 < baseStart_1403544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403550 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_1403550 : Nat := 118140960795 + 1403550 * 2 ^ 59
def prefixEnd_1403550 : Nat := 4983230072969 + 3 ^ 40 * 1403550 * 2
def baseEnd_1403550 : Nat := 80077308068676537541133

theorem tailTrace_1403550 : CollatzResearch.WordTrace tailWord_1403550 prefixEnd_1403550 80077308068676537541133 := by
  unfold tailWord_1403550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6398959258148191512630013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34127782710123688067360069 6398959258148191512630013)
  ·
    refine ⟨2399609721805571817236255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6398959258148191512630013 2399609721805571817236255)
    ·
      refine ⟨3599414582708357725854383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2399609721805571817236255 3599414582708357725854383)
      ·
        refine ⟨5399121874062536588781575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3599414582708357725854383 5399121874062536588781575)
        ·
          refine ⟨8098682811093804883172363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399121874062536588781575 8098682811093804883172363)
          ·
            refine ⟨12148024216640707324758545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8098682811093804883172363 12148024216640707324758545)
            ·
              refine ⟨9111018162480530493568909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12148024216640707324758545 9111018162480530493568909)
              ·
                refine ⟨3416631810930198935088341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9111018162480530493568909 3416631810930198935088341)
                ·
                  refine ⟨80077308068676537541133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3416631810930198935088341 80077308068676537541133)
                  ·
                    rfl

theorem cell23_1403550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_1403550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403550 prefixEnd_1403550 := by exact prefixLift 1403550
  have htrace : WordTrace (prefixWord ++ tailWord_1403550) baseStart_1403550 baseEnd_1403550 := by
    simpa [prefixWord, tailWord_1403550, baseEnd_1403550] using wordTrace_append hprefix tailTrace_1403550
  have hstable : (prefixWord ++ tailWord_1403550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403550).length < 2 ^ (prefixWord ++ tailWord_1403550).sum := by decide
  have hdescent : baseEnd_1403550 < baseStart_1403550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403570 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_1403570 : Nat := 118140960795 + 1403570 * 2 ^ 59
def prefixEnd_1403570 : Nat := 4983230072969 + 3 ^ 40 * 1403570 * 2
def baseEnd_1403570 : Nat := 720706042231178759620105

theorem tailTrace_1403570 : CollatzResearch.WordTrace tailWord_1403570 prefixEnd_1403570 720706042231178759620105 := by
  unfold tailWord_1403570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12798100881278268879192041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34128269016742050344512109 12798100881278268879192041)
  ·
    refine ⟨9598575660958701659394031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12798100881278268879192041 9598575660958701659394031)
    ·
      refine ⟨14397863491438052489091047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9598575660958701659394031 14397863491438052489091047)
      ·
        refine ⟨21596795237157078733636571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14397863491438052489091047 21596795237157078733636571)
        ·
          refine ⟨32395192855735618100454857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21596795237157078733636571 32395192855735618100454857)
          ·
            refine ⟨24296394641801713575341143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32395192855735618100454857 24296394641801713575341143)
            ·
              refine ⟨36444591962702570363011715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24296394641801713575341143 36444591962702570363011715)
              ·
                refine ⟨54666887944053855544517573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36444591962702570363011715 54666887944053855544517573)
                ·
                  refine ⟨10250041489510097914597045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54666887944053855544517573 10250041489510097914597045)
                  ·
                    refine ⟨960941389641571679493473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10250041489510097914597045 960941389641571679493473)
                    ·
                      refine ⟨720706042231178759620105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960941389641571679493473 720706042231178759620105)
                      ·
                        rfl

theorem cell23_1403570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_1403570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403570 prefixEnd_1403570 := by exact prefixLift 1403570
  have htrace : WordTrace (prefixWord ++ tailWord_1403570) baseStart_1403570 baseEnd_1403570 := by
    simpa [prefixWord, tailWord_1403570, baseEnd_1403570] using wordTrace_append hprefix tailTrace_1403570
  have hstable : (prefixWord ++ tailWord_1403570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403570).length < 2 ^ (prefixWord ++ tailWord_1403570).sum := by decide
  have hdescent : baseEnd_1403570 < baseStart_1403570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403617 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_1403617 : Nat := 118140960795 + 1403617 * 2 ^ 59
def prefixEnd_1403617 : Nat := 4983230072969 + 3 ^ 40 * 1403617 * 2
def baseEnd_1403617 : Nat := 720730175821940075732389

theorem tailTrace_1403617 : CollatzResearch.WordTrace tailWord_1403617 prefixEnd_1403617 720730175821940075732389 := by
  unfold tailWord_1403617
  simp only [CollatzResearch.WordTrace]
  refine ⟨51194117755942802543729105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34129411837295201695819403 51194117755942802543729105)
  ·
    refine ⟨38395588316957101907796829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51194117755942802543729105 38395588316957101907796829)
    ·
      refine ⟨14398345618858913215423811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38395588316957101907796829 14398345618858913215423811)
      ·
        refine ⟨21597518428288369823135717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14398345618858913215423811 21597518428288369823135717)
        ·
          refine ⟨4049534705304069341837947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21597518428288369823135717 4049534705304069341837947)
          ·
            refine ⟨6074302057956104012756921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049534705304069341837947 6074302057956104012756921)
            ·
              refine ⟨4555726543467078009567691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6074302057956104012756921 4555726543467078009567691)
              ·
                refine ⟨6833589815200617014351537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555726543467078009567691 6833589815200617014351537)
                ·
                  refine ⟨5125192361400462760763653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6833589815200617014351537 5125192361400462760763653)
                  ·
                    refine ⟨960973567762586767643185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5125192361400462760763653 960973567762586767643185)
                    ·
                      refine ⟨720730175821940075732389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960973567762586767643185 720730175821940075732389)
                      ·
                        rfl

theorem cell23_1403617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_1403617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403617 prefixEnd_1403617 := by exact prefixLift 1403617
  have htrace : WordTrace (prefixWord ++ tailWord_1403617) baseStart_1403617 baseEnd_1403617 := by
    simpa [prefixWord, tailWord_1403617, baseEnd_1403617] using wordTrace_append hprefix tailTrace_1403617
  have hstable : (prefixWord ++ tailWord_1403617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403617).length < 2 ^ (prefixWord ++ tailWord_1403617).sum := by decide
  have hdescent : baseEnd_1403617 < baseStart_1403617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403620 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_1403620 : Nat := 118140960795 + 1403620 * 2 ^ 59
def prefixEnd_1403620 : Nat := 4983230072969 + 3 ^ 40 * 1403620 * 2
def baseEnd_1403620 : Nat := 720731716263903563994875

theorem tailTrace_1403620 : CollatzResearch.WordTrace tailWord_1403620 prefixEnd_1403620 720731716263903563994875 := by
  unfold tailWord_1403620
  simp only [CollatzResearch.WordTrace]
  refine ⟨25597113587465967028044157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34129484783287956037392209 25597113587465967028044157)
  ·
    refine ⟨9598917595299737635516559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25597113587465967028044157 9598917595299737635516559)
    ·
      refine ⟨14398376392949606453274839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9598917595299737635516559 14398376392949606453274839)
      ·
        refine ⟨21597564589424409679912259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14398376392949606453274839 21597564589424409679912259)
        ·
          refine ⟨32396346884136614519868389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21597564589424409679912259 32396346884136614519868389)
          ·
            refine ⟨6074315040775615222475323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32396346884136614519868389 6074315040775615222475323)
            ·
              refine ⟨9111472561163422833712985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6074315040775615222475323 9111472561163422833712985)
              ·
                refine ⟨6833604420872567125284739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9111472561163422833712985 6833604420872567125284739)
                ·
                  refine ⟨10250406631308850687927109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6833604420872567125284739 10250406631308850687927109)
                  ·
                    refine ⟨1921951243370409503986333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10250406631308850687927109 1921951243370409503986333)
                    ·
                      refine ⟨720731716263903563994875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1921951243370409503986333 720731716263903563994875)
                      ·
                        rfl

theorem cell23_1403620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_1403620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403620 prefixEnd_1403620 := by exact prefixLift 1403620
  have htrace : WordTrace (prefixWord ++ tailWord_1403620) baseStart_1403620 baseEnd_1403620 := by
    simpa [prefixWord, tailWord_1403620, baseEnd_1403620] using wordTrace_append hprefix tailTrace_1403620
  have hstable : (prefixWord ++ tailWord_1403620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403620).length < 2 ^ (prefixWord ++ tailWord_1403620).sum := by decide
  have hdescent : baseEnd_1403620 < baseStart_1403620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403644 : List Nat := [2, 2, 2, 1, 3, 2, 3, 3, 1, 4]
def baseStart_1403644 : Nat := 118140960795 + 1403644 * 2 ^ 59
def prefixEnd_1403644 : Nat := 4983230072969 + 3 ^ 40 * 1403644 * 2
def baseEnd_1403644 : Nat := 240248013266537156698255

theorem tailTrace_1403644 : CollatzResearch.WordTrace tailWord_1403644 prefixEnd_1403644 240248013266537156698255 := by
  unfold tailWord_1403644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25597551263422493077480993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34130068351229990769974657 25597551263422493077480993)
  ·
    refine ⟨19198163447566869808110745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25597551263422493077480993 19198163447566869808110745)
    ·
      refine ⟨14398622585675152356083059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19198163447566869808110745 14398622585675152356083059)
      ·
        refine ⟨21597933878512728534124589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14398622585675152356083059 21597933878512728534124589)
        ·
          refine ⟨8099225204442273200296721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21597933878512728534124589 8099225204442273200296721)
          ·
            refine ⟨6074418903331704900222541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8099225204442273200296721 6074418903331704900222541)
            ·
              refine ⟨2277907088749389337583453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6074418903331704900222541 2277907088749389337583453)
              ·
                refine ⟨854215158281021001593795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2277907088749389337583453 854215158281021001593795)
                ·
                  refine ⟨1281322737421531502390693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854215158281021001593795 1281322737421531502390693)
                  ·
                    refine ⟨240248013266537156698255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1281322737421531502390693 240248013266537156698255)
                    ·
                      rfl

theorem cell23_1403644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_1403644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403644 prefixEnd_1403644 := by exact prefixLift 1403644
  have htrace : WordTrace (prefixWord ++ tailWord_1403644) baseStart_1403644 baseEnd_1403644 := by
    simpa [prefixWord, tailWord_1403644, baseEnd_1403644] using wordTrace_append hprefix tailTrace_1403644
  have hstable : (prefixWord ++ tailWord_1403644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403644).length < 2 ^ (prefixWord ++ tailWord_1403644).sum := by decide
  have hdescent : baseEnd_1403644 < baseStart_1403644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403720 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_1403720 : Nat := 118140960795 + 1403720 * 2 ^ 59
def prefixEnd_1403720 : Nat := 4983230072969 + 3 ^ 40 * 1403720 * 2
def baseEnd_1403720 : Nat := 720783064329353172744415

theorem tailTrace_1403720 : CollatzResearch.WordTrace tailWord_1403720 prefixEnd_1403720 720783064329353172744415 := by
  unfold tailWord_1403720
  simp only [CollatzResearch.WordTrace]
  refine ⟨25598937237284825567364307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34131916316379767423152409 25598937237284825567364307)
  ·
    refine ⟨38398405855927238351046461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25598937237284825567364307 38398405855927238351046461)
    ·
      refine ⟨14399402195972714381642423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38398405855927238351046461 14399402195972714381642423)
      ·
        refine ⟨21599103293959071572463635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14399402195972714381642423 21599103293959071572463635)
        ·
          refine ⟨32398654940938607358695453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21599103293959071572463635 32398654940938607358695453)
          ·
            refine ⟨12149495602851977759510795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32398654940938607358695453 12149495602851977759510795)
            ·
              refine ⟨18224243404277966639266193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12149495602851977759510795 18224243404277966639266193)
              ·
                refine ⟨13668182553208474979449645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18224243404277966639266193 13668182553208474979449645)
                ·
                  refine ⟨5125568457453178117293617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13668182553208474979449645 5125568457453178117293617)
                  ·
                    refine ⟨3844176343089883587970213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5125568457453178117293617 3844176343089883587970213)
                    ·
                      refine ⟨720783064329353172744415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3844176343089883587970213 720783064329353172744415)
                      ·
                        rfl

theorem cell23_1403720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_1403720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403720 prefixEnd_1403720 := by exact prefixLift 1403720
  have htrace : WordTrace (prefixWord ++ tailWord_1403720) baseStart_1403720 baseEnd_1403720 := by
    simpa [prefixWord, tailWord_1403720, baseEnd_1403720] using wordTrace_append hprefix tailTrace_1403720
  have hstable : (prefixWord ++ tailWord_1403720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403720).length < 2 ^ (prefixWord ++ tailWord_1403720).sum := by decide
  have hdescent : baseEnd_1403720 < baseStart_1403720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403737 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 4]
def baseStart_1403737 : Nat := 118140960795 + 1403737 * 2 ^ 59
def prefixEnd_1403737 : Nat := 4983230072969 + 3 ^ 40 * 1403737 * 2
def baseEnd_1403737 : Nat := 720791793500479606231837

theorem tailTrace_1403737 : CollatzResearch.WordTrace tailWord_1403737 prefixEnd_1403737 720791793500479606231837 := by
  unfold tailWord_1403737
  simp only [CollatzResearch.WordTrace]
  refine ⟨51198494515508063038097465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34132329677005375358731643 51198494515508063038097465)
  ·
    refine ⟨38398870886631047278573099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51198494515508063038097465 38398870886631047278573099)
    ·
      refine ⟨57598306329946570917859649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38398870886631047278573099 57598306329946570917859649)
      ·
        refine ⟨43198729747459928188394737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57598306329946570917859649 43198729747459928188394737)
        ·
          refine ⟨32399047310594946141296053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43198729747459928188394737 32399047310594946141296053)
          ·
            refine ⟨3037410685368276200746505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32399047310594946141296053 3037410685368276200746505)
            ·
              refine ⟨2278058014026207150559879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3037410685368276200746505 2278058014026207150559879)
              ·
                refine ⟨3417087021039310725839819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278058014026207150559879 3417087021039310725839819)
                ·
                  refine ⟨5125630531558966088759729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3417087021039310725839819 5125630531558966088759729)
                  ·
                    refine ⟨3844222898669224566569797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5125630531558966088759729 3844222898669224566569797)
                    ·
                      refine ⟨720791793500479606231837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3844222898669224566569797 720791793500479606231837)
                      ·
                        rfl

theorem cell23_1403737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_1403737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403737 prefixEnd_1403737 := by exact prefixLift 1403737
  have htrace : WordTrace (prefixWord ++ tailWord_1403737) baseStart_1403737 baseEnd_1403737 := by
    simpa [prefixWord, tailWord_1403737, baseEnd_1403737] using wordTrace_append hprefix tailTrace_1403737
  have hstable : (prefixWord ++ tailWord_1403737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403737).length < 2 ^ (prefixWord ++ tailWord_1403737).sum := by decide
  have hdescent : baseEnd_1403737 < baseStart_1403737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403747 : List Nat := [1, 1, 1, 5, 3, 2, 3, 7]
def baseStart_1403747 : Nat := 118140960795 + 1403747 * 2 ^ 59
def prefixEnd_1403747 : Nat := 4983230072969 + 3 ^ 40 * 1403747 * 2
def baseEnd_1403747 : Nat := 26696182529889798781733

theorem tailTrace_1403747 : CollatzResearch.WordTrace tailWord_1403747 prefixEnd_1403747 26696182529889798781733 := by
  unfold tailWord_1403747
  simp only [CollatzResearch.WordTrace]
  refine ⟨51198859245471834745961495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34132572830314556497307663 51198859245471834745961495)
  ·
    refine ⟨76798288868207752118942243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51198859245471834745961495 76798288868207752118942243)
    ·
      refine ⟨115197433302311628178413365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76798288868207752118942243 115197433302311628178413365)
      ·
        refine ⟨10799759372091715141726253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115197433302311628178413365 10799759372091715141726253)
        ·
          refine ⟨4049909764534393178147345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10799759372091715141726253 4049909764534393178147345)
          ·
            refine ⟨3037432323400794883610509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4049909764534393178147345 3037432323400794883610509)
            ·
              refine ⟨1139037121275298081353941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3037432323400794883610509 1139037121275298081353941)
              ·
                refine ⟨26696182529889798781733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1139037121275298081353941 26696182529889798781733)
                ·
                  rfl

theorem cell23_1403747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 7].length) (baseStart_1403747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403747 prefixEnd_1403747 := by exact prefixLift 1403747
  have htrace : WordTrace (prefixWord ++ tailWord_1403747) baseStart_1403747 baseEnd_1403747 := by
    simpa [prefixWord, tailWord_1403747, baseEnd_1403747] using wordTrace_append hprefix tailTrace_1403747
  have hstable : (prefixWord ++ tailWord_1403747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403747).length < 2 ^ (prefixWord ++ tailWord_1403747).sum := by decide
  have hdescent : baseEnd_1403747 < baseStart_1403747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403758 : List Nat := [4, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_1403758 : Nat := 118140960795 + 1403758 * 2 ^ 59
def prefixEnd_1403758 : Nat := 4983230072969 + 3 ^ 40 * 1403758 * 2
def baseEnd_1403758 : Nat := 720802576594224024069241

theorem tailTrace_1403758 : CollatzResearch.WordTrace tailWord_1403758 prefixEnd_1403758 720802576594224024069241 := by
  unfold tailWord_1403758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399907556053997953076491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34132840298954655749741285 6399907556053997953076491)
  ·
    refine ⟨9599861334080996929614737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6399907556053997953076491 9599861334080996929614737)
    ·
      refine ⟨7199896000560747697211053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9599861334080996929614737 7199896000560747697211053)
      ·
        refine ⟨2699961000210280386454145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7199896000560747697211053 2699961000210280386454145)
        ·
          refine ⟨2024970750157710289840609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2699961000210280386454145 2024970750157710289840609)
          ·
            refine ⟨1518728062618282717380457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2024970750157710289840609 1518728062618282717380457)
            ·
              refine ⟨1139046046963712038035343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518728062618282717380457 1139046046963712038035343)
              ·
                refine ⟨1708569070445568057053015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139046046963712038035343 1708569070445568057053015)
                ·
                  refine ⟨2562853605668352085579523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708569070445568057053015 2562853605668352085579523)
                  ·
                    refine ⟨3844280408502528128369285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2562853605668352085579523 3844280408502528128369285)
                    ·
                      refine ⟨720802576594224024069241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3844280408502528128369285 720802576594224024069241)
                      ·
                        rfl

theorem cell23_1403758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_1403758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403758 prefixEnd_1403758 := by exact prefixLift 1403758
  have htrace : WordTrace (prefixWord ++ tailWord_1403758) baseStart_1403758 baseEnd_1403758 := by
    simpa [prefixWord, tailWord_1403758, baseEnd_1403758] using wordTrace_append hprefix tailTrace_1403758
  have hstable : (prefixWord ++ tailWord_1403758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403758).length < 2 ^ (prefixWord ++ tailWord_1403758).sum := by decide
  have hdescent : baseEnd_1403758 < baseStart_1403758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403761 : List Nat := [1, 2, 2, 2, 1, 6, 2, 1, 1, 2, 3]
def baseStart_1403761 : Nat := 118140960795 + 1403761 * 2 ^ 59
def prefixEnd_1403761 : Nat := 4983230072969 + 3 ^ 40 * 1403761 * 2
def baseEnd_1403761 : Nat := 720804117036187512331727

theorem tailTrace_1403761 : CollatzResearch.WordTrace tailWord_1403761 prefixEnd_1403761 720804117036187512331727 := by
  unfold tailWord_1403761
  simp only [CollatzResearch.WordTrace]
  refine ⟨51199369867421115136971137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34132913244947410091314091 51199369867421115136971137)
  ·
    refine ⟨38399527400565836352728353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51199369867421115136971137 38399527400565836352728353)
    ·
      refine ⟨28799645550424377264546265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38399527400565836352728353 28799645550424377264546265)
      ·
        refine ⟨21599734162818282948409699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28799645550424377264546265 21599734162818282948409699)
        ·
          refine ⟨32399601244227424422614549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21599734162818282948409699 32399601244227424422614549)
          ·
            refine ⟨1518731308323160519810057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32399601244227424422614549 1518731308323160519810057)
            ·
              refine ⟨1139048481242370389857543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518731308323160519810057 1139048481242370389857543)
              ·
                refine ⟨1708572721863555584786315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139048481242370389857543 1708572721863555584786315)
                ·
                  refine ⟨2562859082795333377179473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1708572721863555584786315 2562859082795333377179473)
                  ·
                    refine ⟨1922144312096500032884605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2562859082795333377179473 1922144312096500032884605)
                    ·
                      refine ⟨720804117036187512331727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1922144312096500032884605 720804117036187512331727)
                      ·
                        rfl

theorem cell23_1403761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_1403761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403761 prefixEnd_1403761 := by exact prefixLift 1403761
  have htrace : WordTrace (prefixWord ++ tailWord_1403761) baseStart_1403761 baseEnd_1403761 := by
    simpa [prefixWord, tailWord_1403761, baseEnd_1403761] using wordTrace_append hprefix tailTrace_1403761
  have hstable : (prefixWord ++ tailWord_1403761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403761).length < 2 ^ (prefixWord ++ tailWord_1403761).sum := by decide
  have hdescent : baseEnd_1403761 < baseStart_1403761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403798 : List Nat := [5, 3, 1, 1, 1, 3, 2, 7]
def baseStart_1403798 : Nat := 118140960795 + 1403798 * 2 ^ 59
def prefixEnd_1403798 : Nat := 4983230072969 + 3 ^ 40 * 1403798 * 2
def baseEnd_1403798 : Nat := 26697152437792735835891

theorem tailTrace_1403798 : CollatzResearch.WordTrace tailWord_1403798 prefixEnd_1403798 26697152437792735835891 := by
  unfold tailWord_1403798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3200044960517941903504253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34133812912191380304045365 3200044960517941903504253)
  ·
    refine ⟨1200016860194228213814095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3200044960517941903504253 1200016860194228213814095)
    ·
      refine ⟨1800025290291342320721143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200016860194228213814095 1800025290291342320721143)
      ·
        refine ⟨2700037935437013481081715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800025290291342320721143 2700037935437013481081715)
        ·
          refine ⟨4050056903155520221622573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700037935437013481081715 4050056903155520221622573)
          ·
            refine ⟨1518771338683320083108465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4050056903155520221622573 1518771338683320083108465)
            ·
              refine ⟨1139078504012490062331349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518771338683320083108465 1139078504012490062331349)
              ·
                refine ⟨26697152437792735835891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1139078504012490062331349 26697152437792735835891)
                ·
                  rfl

theorem cell23_1403798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_1403798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403798 prefixEnd_1403798 := by exact prefixLift 1403798
  have htrace : WordTrace (prefixWord ++ tailWord_1403798) baseStart_1403798 baseEnd_1403798 := by
    simpa [prefixWord, tailWord_1403798, baseEnd_1403798] using wordTrace_append hprefix tailTrace_1403798
  have hstable : (prefixWord ++ tailWord_1403798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403798).length < 2 ^ (prefixWord ++ tailWord_1403798).sum := by decide
  have hdescent : baseEnd_1403798 < baseStart_1403798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403847 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_1403847 : Nat := 118140960795 + 1403847 * 2 ^ 59
def prefixEnd_1403847 : Nat := 4983230072969 + 3 ^ 40 * 1403847 * 2
def baseEnd_1403847 : Nat := 720848276372474175856331

theorem tailTrace_1403847 : CollatzResearch.WordTrace tailWord_1403847 prefixEnd_1403847 720848276372474175856331 := by
  unfold tailWord_1403847
  simp only [CollatzResearch.WordTrace]
  refine ⟨51202506545109551824601795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34135004363406367883067863 51202506545109551824601795)
  ·
    refine ⟨76803759817664327736902693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51202506545109551824601795 76803759817664327736902693)
    ·
      refine ⟨14400704965812061450669255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76803759817664327736902693 14400704965812061450669255)
      ·
        refine ⟨21601057448718092176003883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14400704965812061450669255 21601057448718092176003883)
        ·
          refine ⟨32401586173077138264005825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21601057448718092176003883 32401586173077138264005825)
          ·
            refine ⟨24301189629807853698004369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32401586173077138264005825 24301189629807853698004369)
            ·
              refine ⟨18225892222355890273503277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24301189629807853698004369 18225892222355890273503277)
              ·
                refine ⟨6834709583383458852563729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18225892222355890273503277 6834709583383458852563729)
                ·
                  refine ⟨5126032187537594139422797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6834709583383458852563729 5126032187537594139422797)
                  ·
                    refine ⟨1922262070326597802283549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5126032187537594139422797 1922262070326597802283549)
                    ·
                      refine ⟨720848276372474175856331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1922262070326597802283549 720848276372474175856331)
                      ·
                        rfl

theorem cell23_1403847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_1403847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403847 prefixEnd_1403847 := by exact prefixLift 1403847
  have htrace : WordTrace (prefixWord ++ tailWord_1403847) baseStart_1403847 baseEnd_1403847 := by
    simpa [prefixWord, tailWord_1403847, baseEnd_1403847] using wordTrace_append hprefix tailTrace_1403847
  have hstable : (prefixWord ++ tailWord_1403847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403847).length < 2 ^ (prefixWord ++ tailWord_1403847).sum := by decide
  have hdescent : baseEnd_1403847 < baseStart_1403847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403848 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_1403848 : Nat := 118140960795 + 1403848 * 2 ^ 59
def prefixEnd_1403848 : Nat := 4983230072969 + 3 ^ 40 * 1403848 * 2
def baseEnd_1403848 : Nat := 720848789853128671943827

theorem tailTrace_1403848 : CollatzResearch.WordTrace tailWord_1403848 prefixEnd_1403848 720848789853128671943827 := by
  unfold tailWord_1403848
  simp only [CollatzResearch.WordTrace]
  refine ⟨25601271509052964497694099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34135028678737285996925465 25601271509052964497694099)
  ·
    refine ⟨38401907263579446746541149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25601271509052964497694099 38401907263579446746541149)
    ·
      refine ⟨14400715223842292529952931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38401907263579446746541149 14400715223842292529952931)
      ·
        refine ⟨21601072835763438794929397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14400715223842292529952931 21601072835763438794929397)
        ·
          refine ⟨2025100578352822387024631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21601072835763438794929397 2025100578352822387024631)
          ·
            refine ⟨3037650867529233580536947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025100578352822387024631 3037650867529233580536947)
            ·
              refine ⟨4556476301293850370805421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037650867529233580536947 4556476301293850370805421)
              ·
                refine ⟨1708678612985193889052033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4556476301293850370805421 1708678612985193889052033)
                ·
                  refine ⟨1281508959738895416789025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1708678612985193889052033 1281508959738895416789025)
                  ·
                    refine ⟨961131719804171562591769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1281508959738895416789025 961131719804171562591769)
                    ·
                      refine ⟨720848789853128671943827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 961131719804171562591769 720848789853128671943827)
                      ·
                        rfl

theorem cell23_1403848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_1403848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403848 prefixEnd_1403848 := by exact prefixLift 1403848
  have htrace : WordTrace (prefixWord ++ tailWord_1403848) baseStart_1403848 baseEnd_1403848 := by
    simpa [prefixWord, tailWord_1403848, baseEnd_1403848] using wordTrace_append hprefix tailTrace_1403848
  have hstable : (prefixWord ++ tailWord_1403848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403848).length < 2 ^ (prefixWord ++ tailWord_1403848).sum := by decide
  have hdescent : baseEnd_1403848 < baseStart_1403848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403894 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1403894 : Nat := 118140960795 + 1403894 * 2 ^ 59
def prefixEnd_1403894 : Nat := 4983230072969 + 3 ^ 40 * 1403894 * 2
def baseEnd_1403894 : Nat := 720872409963235491968615

theorem tailTrace_1403894 : CollatzResearch.WordTrace tailWord_1403894 prefixEnd_1403894 720872409963235491968615 := by
  unfold tailWord_1403894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3200263798496204928222671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34136147183959519234375157 3200263798496204928222671)
  ·
    refine ⟨4800395697744307392334007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3200263798496204928222671 4800395697744307392334007)
    ·
      refine ⟨7200593546616461088501011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4800395697744307392334007 7200593546616461088501011)
      ·
        refine ⟨10800890319924691632751517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7200593546616461088501011 10800890319924691632751517)
        ·
          refine ⟨4050333869971759362281819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10800890319924691632751517 4050333869971759362281819)
          ·
            refine ⟨6075500804957639043422729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4050333869971759362281819 6075500804957639043422729)
            ·
              refine ⟨4556625603718229282567047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6075500804957639043422729 4556625603718229282567047)
              ·
                refine ⟨6834938405577343923850571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4556625603718229282567047 6834938405577343923850571)
                ·
                  refine ⟨10252407608366015885775857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6834938405577343923850571 10252407608366015885775857)
                  ·
                    refine ⟨7689305706274511914331893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10252407608366015885775857 7689305706274511914331893)
                    ·
                      refine ⟨720872409963235491968615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7689305706274511914331893 720872409963235491968615)
                      ·
                        rfl

theorem cell23_1403894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1403894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403894 prefixEnd_1403894 := by exact prefixLift 1403894
  have htrace : WordTrace (prefixWord ++ tailWord_1403894) baseStart_1403894 baseEnd_1403894 := by
    simpa [prefixWord, tailWord_1403894, baseEnd_1403894] using wordTrace_append hprefix tailTrace_1403894
  have hstable : (prefixWord ++ tailWord_1403894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403894).length < 2 ^ (prefixWord ++ tailWord_1403894).sum := by decide
  have hdescent : baseEnd_1403894 < baseStart_1403894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403914 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 5, 4]
def baseStart_1403914 : Nat := 118140960795 + 1403914 * 2 ^ 59
def prefixEnd_1403914 : Nat := 4983230072969 + 3 ^ 40 * 1403914 * 2
def baseEnd_1403914 : Nat := 240294226525441804572841

theorem tailTrace_1403914 : CollatzResearch.WordTrace tailWord_1403914 prefixEnd_1403914 240294226525441804572841 := by
  unfold tailWord_1403914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12801237558966705566822699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34136633490577881511527197 12801237558966705566822699)
  ·
    refine ⟨19201856338450058350234049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12801237558966705566822699 19201856338450058350234049)
    ·
      refine ⟨14401392253837543762675537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19201856338450058350234049 14401392253837543762675537)
      ·
        refine ⟨10801044190378157822006653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14401392253837543762675537 10801044190378157822006653)
        ·
          refine ⟨4050391571391809183252495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10801044190378157822006653 4050391571391809183252495)
          ·
            refine ⟨6075587357087713774878743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4050391571391809183252495 6075587357087713774878743)
            ·
              refine ⟨9113381035631570662318115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6075587357087713774878743 9113381035631570662318115)
              ·
                refine ⟨13670071553447355993477173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9113381035631570662318115 13670071553447355993477173)
                ·
                  refine ⟨1281569208135689624388485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13670071553447355993477173 1281569208135689624388485)
                  ·
                    refine ⟨240294226525441804572841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1281569208135689624388485 240294226525441804572841)
                    ·
                      rfl

theorem cell23_1403914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_1403914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403914 prefixEnd_1403914 := by exact prefixLift 1403914
  have htrace : WordTrace (prefixWord ++ tailWord_1403914) baseStart_1403914 baseEnd_1403914 := by
    simpa [prefixWord, tailWord_1403914, baseEnd_1403914] using wordTrace_append hprefix tailTrace_1403914
  have hstable : (prefixWord ++ tailWord_1403914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403914).length < 2 ^ (prefixWord ++ tailWord_1403914).sum := by decide
  have hdescent : baseEnd_1403914 < baseStart_1403914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1403961 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 6]
def baseStart_1403961 : Nat := 118140960795 + 1403961 * 2 ^ 59
def prefixEnd_1403961 : Nat := 4983230072969 + 3 ^ 40 * 1403961 * 2
def baseEnd_1403961 : Nat := 80100757018565192203423

theorem tailTrace_1403961 : CollatzResearch.WordTrace tailWord_1403961 prefixEnd_1403961 80100757018565192203423 := by
  unfold tailWord_1403961
  simp only [CollatzResearch.WordTrace]
  refine ⟨51206664466696549294251737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34137776311131032862834491 51206664466696549294251737)
  ·
    refine ⟨38404998350022411970688803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51206664466696549294251737 38404998350022411970688803)
    ·
      refine ⟨57607497525033617956033205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38404998350022411970688803 57607497525033617956033205)
      ·
        refine ⟨5400702892971901683378113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57607497525033617956033205 5400702892971901683378113)
        ·
          refine ⟨4050527169728926262533585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5400702892971901683378113 4050527169728926262533585)
          ·
            refine ⟨3037895377296694696900189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4050527169728926262533585 3037895377296694696900189)
            ·
              refine ⟨1139210766486260511337571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3037895377296694696900189 1139210766486260511337571)
              ·
                refine ⟨1708816149729390767006357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139210766486260511337571 1708816149729390767006357)
                ·
                  refine ⟨80100757018565192203423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1708816149729390767006357 80100757018565192203423)
                  ·
                    rfl

theorem cell23_1403961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 6].length) (baseStart_1403961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1403961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1403961 prefixEnd_1403961 := by exact prefixLift 1403961
  have htrace : WordTrace (prefixWord ++ tailWord_1403961) baseStart_1403961 baseEnd_1403961 := by
    simpa [prefixWord, tailWord_1403961, baseEnd_1403961] using wordTrace_append hprefix tailTrace_1403961
  have hstable : (prefixWord ++ tailWord_1403961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1403961).length < 2 ^ (prefixWord ++ tailWord_1403961).sum := by decide
  have hdescent : baseEnd_1403961 < baseStart_1403961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1403961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404005 : List Nat := [1, 3, 1, 3, 2, 1, 5, 2, 1, 1, 3]
def baseStart_1404005 : Nat := 118140960795 + 1404005 * 2 ^ 59
def prefixEnd_1404005 : Nat := 4983230072969 + 3 ^ 40 * 1404005 * 2
def baseEnd_1404005 : Nat := 720929406315884557680605

theorem tailTrace_1404005 : CollatzResearch.WordTrace tailWord_1404005 prefixEnd_1404005 720929406315884557680605 := by
  unfold tailWord_1404005
  simp only [CollatzResearch.WordTrace]
  refine ⟨51208269278537144808853469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34138846185691429872568979 51208269278537144808853469)
  ·
    refine ⟨19203100979451429303320051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51208269278537144808853469 19203100979451429303320051)
    ·
      refine ⟨28804651469177143954980077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19203100979451429303320051 28804651469177143954980077)
      ·
        refine ⟨10801744300941428983117529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28804651469177143954980077 10801744300941428983117529)
        ·
          refine ⟨8101308225706071737338147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10801744300941428983117529 8101308225706071737338147)
          ·
            refine ⟨12151962338559107606007221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8101308225706071737338147 12151962338559107606007221)
            ·
              refine ⟨1139246469239916338063177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12151962338559107606007221 1139246469239916338063177)
              ·
                refine ⟨854434851929937253547383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139246469239916338063177 854434851929937253547383)
                ·
                  refine ⟨1281652277894905880321075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854434851929937253547383 1281652277894905880321075)
                  ·
                    refine ⟨1922478416842358820481613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1281652277894905880321075 1922478416842358820481613)
                    ·
                      refine ⟨720929406315884557680605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1922478416842358820481613 720929406315884557680605)
                      ·
                        rfl

theorem cell23_1404005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_1404005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404005 prefixEnd_1404005 := by exact prefixLift 1404005
  have htrace : WordTrace (prefixWord ++ tailWord_1404005) baseStart_1404005 baseEnd_1404005 := by
    simpa [prefixWord, tailWord_1404005, baseEnd_1404005] using wordTrace_append hprefix tailTrace_1404005
  have hstable : (prefixWord ++ tailWord_1404005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404005).length < 2 ^ (prefixWord ++ tailWord_1404005).sum := by decide
  have hdescent : baseEnd_1404005 < baseStart_1404005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404057 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_1404057 : Nat := 118140960795 + 1404057 * 2 ^ 59
def prefixEnd_1404057 : Nat := 4983230072969 + 3 ^ 40 * 1404057 * 2
def baseEnd_1404057 : Nat := 720956107309918354230365

theorem tailTrace_1404057 : CollatzResearch.WordTrace tailWord_1404057 prefixEnd_1404057 720956107309918354230365 := by
  unfold tailWord_1404057
  simp only [CollatzResearch.WordTrace]
  refine ⟨51210165874348757689746425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34140110582899171793164283 51210165874348757689746425)
  ·
    refine ⟨38407624405761568267309819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51210165874348757689746425 38407624405761568267309819)
    ·
      refine ⟨57611436608642352400964729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38407624405761568267309819 57611436608642352400964729)
      ·
        refine ⟨43208577456481764300723547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57611436608642352400964729 43208577456481764300723547)
        ·
          refine ⟨64812866184722646451085321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43208577456481764300723547 64812866184722646451085321)
          ·
            refine ⟨48609649638541984838313991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64812866184722646451085321 48609649638541984838313991)
            ·
              refine ⟨72914474457812977257470987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48609649638541984838313991 72914474457812977257470987)
              ·
                refine ⟨109371711686719465886206481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72914474457812977257470987 109371711686719465886206481)
                ·
                  refine ⟨82028783765039599414654861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109371711686719465886206481 82028783765039599414654861)
                  ·
                    refine ⟨30760793911889849780495573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82028783765039599414654861 30760793911889849780495573)
                    ·
                      refine ⟨720956107309918354230365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30760793911889849780495573 720956107309918354230365)
                      ·
                        rfl

theorem cell23_1404057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_1404057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404057 prefixEnd_1404057 := by exact prefixLift 1404057
  have htrace : WordTrace (prefixWord ++ tailWord_1404057) baseStart_1404057 baseEnd_1404057 := by
    simpa [prefixWord, tailWord_1404057, baseEnd_1404057] using wordTrace_append hprefix tailTrace_1404057
  have hstable : (prefixWord ++ tailWord_1404057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404057).length < 2 ^ (prefixWord ++ tailWord_1404057).sum := by decide
  have hdescent : baseEnd_1404057 < baseStart_1404057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404104 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_1404104 : Nat := 118140960795 + 1404104 * 2 ^ 59
def prefixEnd_1404104 : Nat := 4983230072969 + 3 ^ 40 * 1404104 * 2
def baseEnd_1404104 : Nat := 720980240900679670342649

theorem tailTrace_1404104 : CollatzResearch.WordTrace tailWord_1404104 prefixEnd_1404104 720980240900679670342649 := by
  unfold tailWord_1404104
  simp only [CollatzResearch.WordTrace]
  refine ⟨25605940052589242358353683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34141253403452323144471577 25605940052589242358353683)
  ·
    refine ⟨38408910078883863537530525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25605940052589242358353683 38408910078883863537530525)
    ·
      refine ⟨14403341279581448826573947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38408910078883863537530525 14403341279581448826573947)
      ·
        refine ⟨21605011919372173239860921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14403341279581448826573947 21605011919372173239860921)
        ·
          refine ⟨16203758939529129929895691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21605011919372173239860921 16203758939529129929895691)
          ·
            refine ⟨24305638409293694894843537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16203758939529129929895691 24305638409293694894843537)
            ·
              refine ⟨18229228806970271171132653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24305638409293694894843537 18229228806970271171132653)
              ·
                refine ⟨6835960802613851689174745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18229228806970271171132653 6835960802613851689174745)
                ·
                  refine ⟨5126970601960388766881059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6835960802613851689174745 5126970601960388766881059)
                  ·
                    refine ⟨7690455902940583150321589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5126970601960388766881059 7690455902940583150321589)
                    ·
                      refine ⟨720980240900679670342649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7690455902940583150321589 720980240900679670342649)
                      ·
                        rfl

theorem cell23_1404104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_1404104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404104 prefixEnd_1404104 := by exact prefixLift 1404104
  have htrace : WordTrace (prefixWord ++ tailWord_1404104) baseStart_1404104 baseEnd_1404104 := by
    simpa [prefixWord, tailWord_1404104, baseEnd_1404104] using wordTrace_append hprefix tailTrace_1404104
  have hstable : (prefixWord ++ tailWord_1404104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404104).length < 2 ^ (prefixWord ++ tailWord_1404104).sum := by decide
  have hdescent : baseEnd_1404104 < baseStart_1404104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404141 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 7]
def baseStart_1404141 : Nat := 118140960795 + 1404141 * 2 ^ 59
def prefixEnd_1404141 : Nat := 4983230072969 + 3 ^ 40 * 1404141 * 2
def baseEnd_1404141 : Nat := 80111026631655113953331

theorem tailTrace_1404141 : CollatzResearch.WordTrace tailWord_1404141 prefixEnd_1404141 80111026631655113953331 := by
  unfold tailWord_1404141
  simp only [CollatzResearch.WordTrace]
  refine ⟨51213229606044440035804277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34142153070696293357202851 51213229606044440035804277)
  ·
    refine ⟨4801240275566666253356651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51213229606044440035804277 4801240275566666253356651)
    ·
      refine ⟨7201860413349999380034977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4801240275566666253356651 7201860413349999380034977)
      ·
        refine ⟨5401395310012499535026233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7201860413349999380034977 5401395310012499535026233)
        ·
          refine ⟨4051046482509374651269675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5401395310012499535026233 4051046482509374651269675)
          ·
            refine ⟨6076569723764061976904513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051046482509374651269675 6076569723764061976904513)
            ·
              refine ⟨4557427292823046482678385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6076569723764061976904513 4557427292823046482678385)
              ·
                refine ⟨3418070469617284862008789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4557427292823046482678385 3418070469617284862008789)
                ·
                  refine ⟨80111026631655113953331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3418070469617284862008789 80111026631655113953331)
                  ·
                    rfl

theorem cell23_1404141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_1404141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404141 prefixEnd_1404141 := by exact prefixLift 1404141
  have htrace : WordTrace (prefixWord ++ tailWord_1404141) baseStart_1404141 baseEnd_1404141 := by
    simpa [prefixWord, tailWord_1404141, baseEnd_1404141] using wordTrace_append hprefix tailTrace_1404141
  have hstable : (prefixWord ++ tailWord_1404141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404141).length < 2 ^ (prefixWord ++ tailWord_1404141).sum := by decide
  have hdescent : baseEnd_1404141 < baseStart_1404141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404154 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 1, 7]
def baseStart_1404154 : Nat := 118140960795 + 1404154 * 2 ^ 59
def prefixEnd_1404154 : Nat := 4983230072969 + 3 ^ 40 * 1404154 * 2
def baseEnd_1404154 : Nat := 240335304977801491572473

theorem tailTrace_1404154 : CollatzResearch.WordTrace tailWord_1404154 prefixEnd_1404154 240335304977801491572473 := by
  unfold tailWord_1404154
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803425938749335814006879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34142469169998228837351677 12803425938749335814006879)
  ·
    refine ⟨19205138908124003721010319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12803425938749335814006879 19205138908124003721010319)
    ·
      refine ⟨28807708362186005581515479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19205138908124003721010319 28807708362186005581515479)
      ·
        refine ⟨43211562543279008372273219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28807708362186005581515479 43211562543279008372273219)
        ·
          refine ⟨64817343814918512558409829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43211562543279008372273219 64817343814918512558409829)
          ·
            refine ⟨12153251965297221104701843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64817343814918512558409829 12153251965297221104701843)
            ·
              refine ⟨18229877947945831657052765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12153251965297221104701843 18229877947945831657052765)
              ·
                refine ⟨6836204230479686871394787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18229877947945831657052765 6836204230479686871394787)
                ·
                  refine ⟨10254306345719530307092181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6836204230479686871394787 10254306345719530307092181)
                  ·
                    refine ⟨240335304977801491572473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10254306345719530307092181 240335304977801491572473)
                    ·
                      rfl

theorem cell23_1404154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_1404154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404154 prefixEnd_1404154 := by exact prefixLift 1404154
  have htrace : WordTrace (prefixWord ++ tailWord_1404154) baseStart_1404154 baseEnd_1404154 := by
    simpa [prefixWord, tailWord_1404154, baseEnd_1404154] using wordTrace_append hprefix tailTrace_1404154
  have hstable : (prefixWord ++ tailWord_1404154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404154).length < 2 ^ (prefixWord ++ tailWord_1404154).sum := by decide
  have hdescent : baseEnd_1404154 < baseStart_1404154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404171 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 2, 5]
def baseStart_1404171 : Nat := 118140960795 + 1404171 * 2 ^ 59
def prefixEnd_1404171 : Nat := 4983230072969 + 3 ^ 40 * 1404171 * 2
def baseEnd_1404171 : Nat := 240338214701510302734947

theorem tailTrace_1404171 : CollatzResearch.WordTrace tailWord_1404171 prefixEnd_1404171 240338214701510302734947 := by
  unfold tailWord_1404171
  simp only [CollatzResearch.WordTrace]
  refine ⟨51214323795935755159396367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34142882530623836772930911 51214323795935755159396367)
  ·
    refine ⟨76821485693903632739094551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51214323795935755159396367 76821485693903632739094551)
    ·
      refine ⟨115232228540855449108641827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76821485693903632739094551 115232228540855449108641827)
      ·
        refine ⟨172848342811283173662962741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115232228540855449108641827 172848342811283173662962741)
        ·
          refine ⟨16204532138557797530902757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172848342811283173662962741 16204532138557797530902757)
          ·
            refine ⟨3038349775979587037044267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16204532138557797530902757 3038349775979587037044267)
            ·
              refine ⟨4557524663969380555566401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3038349775979587037044267 4557524663969380555566401)
              ·
                refine ⟨3418143497977035416674801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4557524663969380555566401 3418143497977035416674801)
                ·
                  refine ⟨2563607623482776562506101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3418143497977035416674801 2563607623482776562506101)
                  ·
                    refine ⟨240338214701510302734947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2563607623482776562506101 240338214701510302734947)
                    ·
                      rfl

theorem cell23_1404171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 5].length) (baseStart_1404171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404171 prefixEnd_1404171 := by exact prefixLift 1404171
  have htrace : WordTrace (prefixWord ++ tailWord_1404171) baseStart_1404171 baseEnd_1404171 := by
    simpa [prefixWord, tailWord_1404171, baseEnd_1404171] using wordTrace_append hprefix tailTrace_1404171
  have hstable : (prefixWord ++ tailWord_1404171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404171).length < 2 ^ (prefixWord ++ tailWord_1404171).sum := by decide
  have hdescent : baseEnd_1404171 < baseStart_1404171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404204 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_1404204 : Nat := 118140960795 + 1404204 * 2 ^ 59
def prefixEnd_1404204 : Nat := 4983230072969 + 3 ^ 40 * 1404204 * 2
def baseEnd_1404204 : Nat := 721031588966129279092189

theorem tailTrace_1404204 : CollatzResearch.WordTrace tailWord_1404204 prefixEnd_1404204 721031588966129279092189 := by
  unfold tailWord_1404204
  simp only [CollatzResearch.WordTrace]
  refine ⟨25607763702408100897673833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34143684936544134530231777 25607763702408100897673833)
  ·
    refine ⟨19205822776806075673255375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25607763702408100897673833 19205822776806075673255375)
    ·
      refine ⟨28808734165209113509883063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19205822776806075673255375 28808734165209113509883063)
      ·
        refine ⟨43213101247813670264824595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28808734165209113509883063 43213101247813670264824595)
        ·
          refine ⟨64819651871720505397236893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43213101247813670264824595 64819651871720505397236893)
          ·
            refine ⟨24307369451895189523963835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64819651871720505397236893 24307369451895189523963835)
            ·
              refine ⟨36461054177842784285945753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24307369451895189523963835 36461054177842784285945753)
              ·
                refine ⟨27345790633382088214459315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36461054177842784285945753 27345790633382088214459315)
                ·
                  refine ⟨41018685950073132321688973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27345790633382088214459315 41018685950073132321688973)
                  ·
                    refine ⟨15382007231277424620633365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41018685950073132321688973 15382007231277424620633365)
                    ·
                      refine ⟨721031588966129279092189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15382007231277424620633365 721031588966129279092189)
                      ·
                        rfl

theorem cell23_1404204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_1404204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404204 prefixEnd_1404204 := by exact prefixLift 1404204
  have htrace : WordTrace (prefixWord ++ tailWord_1404204) baseStart_1404204 baseEnd_1404204 := by
    simpa [prefixWord, tailWord_1404204, baseEnd_1404204] using wordTrace_append hprefix tailTrace_1404204
  have hstable : (prefixWord ++ tailWord_1404204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404204).length < 2 ^ (prefixWord ++ tailWord_1404204).sum := by decide
  have hdescent : baseEnd_1404204 < baseStart_1404204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404205 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_1404205 : Nat := 118140960795 + 1404205 * 2 ^ 59
def prefixEnd_1404205 : Nat := 4983230072969 + 3 ^ 40 * 1404205 * 2
def baseEnd_1404205 : Nat := 240344034148927925059895

theorem tailTrace_1404205 : CollatzResearch.WordTrace tailWord_1404205 prefixEnd_1404205 240344034148927925059895 := by
  unfold tailWord_1404205
  simp only [CollatzResearch.WordTrace]
  refine ⟨51215563877812578966134069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34143709251875052644089379 51215563877812578966134069)
  ·
    refine ⟨4801459113544929278075069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51215563877812578966134069 4801459113544929278075069)
    ·
      refine ⟨1800547167579348479278151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4801459113544929278075069 1800547167579348479278151)
      ·
        refine ⟨2700820751369022718917227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800547167579348479278151 2700820751369022718917227)
        ·
          refine ⟨4051231127053534078375841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700820751369022718917227 4051231127053534078375841)
          ·
            refine ⟨3038423345290150558781881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4051231127053534078375841 3038423345290150558781881)
            ·
              refine ⟨2278817508967612919086411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3038423345290150558781881 2278817508967612919086411)
              ·
                refine ⟨3418226263451419378629617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278817508967612919086411 3418226263451419378629617)
                ·
                  refine ⟨2563669697588564533972213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3418226263451419378629617 2563669697588564533972213)
                  ·
                    refine ⟨240344034148927925059895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2563669697588564533972213 240344034148927925059895)
                    ·
                      rfl

theorem cell23_1404205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_1404205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404205 prefixEnd_1404205 := by exact prefixLift 1404205
  have htrace : WordTrace (prefixWord ++ tailWord_1404205) baseStart_1404205 baseEnd_1404205 := by
    simpa [prefixWord, tailWord_1404205, baseEnd_1404205] using wordTrace_append hprefix tailTrace_1404205
  have hstable : (prefixWord ++ tailWord_1404205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404205).length < 2 ^ (prefixWord ++ tailWord_1404205).sum := by decide
  have hdescent : baseEnd_1404205 < baseStart_1404205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404231 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 6]
def baseStart_1404231 : Nat := 118140960795 + 1404231 * 2 ^ 59
def prefixEnd_1404231 : Nat := 4983230072969 + 3 ^ 40 * 1404231 * 2
def baseEnd_1404231 : Nat := 80116161438200074828285

theorem tailTrace_1404231 : CollatzResearch.WordTrace tailWord_1404231 prefixEnd_1404231 80116161438200074828285 := by
  unfold tailWord_1404231
  simp only [CollatzResearch.WordTrace]
  refine ⟨51216512175718385406580547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34144341450478923604387031 51216512175718385406580547)
  ·
    refine ⟨76824768263577578109870821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51216512175718385406580547 76824768263577578109870821)
    ·
      refine ⟨14404644049420795895600779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76824768263577578109870821 14404644049420795895600779)
      ·
        refine ⟨21606966074131193843401169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14404644049420795895600779 21606966074131193843401169)
        ·
          refine ⟨16205224555598395382550877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21606966074131193843401169 16205224555598395382550877)
          ·
            refine ⟨6076959208349398268456579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16205224555598395382550877 6076959208349398268456579)
            ·
              refine ⟨9115438812524097402684869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6076959208349398268456579 9115438812524097402684869)
              ·
                refine ⟨1709144777348268263003413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9115438812524097402684869 1709144777348268263003413)
                ·
                  refine ⟨80116161438200074828285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1709144777348268263003413 80116161438200074828285)
                  ·
                    rfl

theorem cell23_1404231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 6].length) (baseStart_1404231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404231 prefixEnd_1404231 := by exact prefixLift 1404231
  have htrace : WordTrace (prefixWord ++ tailWord_1404231) baseStart_1404231 baseEnd_1404231 := by
    simpa [prefixWord, tailWord_1404231, baseEnd_1404231] using wordTrace_append hprefix tailTrace_1404231
  have hstable : (prefixWord ++ tailWord_1404231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404231).length < 2 ^ (prefixWord ++ tailWord_1404231).sum := by decide
  have hdescent : baseEnd_1404231 < baseStart_1404231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404261 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_1404261 : Nat := 118140960795 + 1404261 * 2 ^ 59
def prefixEnd_1404261 : Nat := 4983230072969 + 3 ^ 40 * 1404261 * 2
def baseEnd_1404261 : Nat := 240353619121145185359809

theorem tailTrace_1404261 : CollatzResearch.WordTrace tailWord_1404261 prefixEnd_1404261 240353619121145185359809 := by
  unfold tailWord_1404261
  simp only [CollatzResearch.WordTrace]
  refine ⟨51217606365609700530172637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34145070910406467020115091 51217606365609700530172637)
  ·
    refine ⟨19206602387103637698814739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51217606365609700530172637 19206602387103637698814739)
    ·
      refine ⟨28809903580655456548222109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19206602387103637698814739 28809903580655456548222109)
      ·
        refine ⟨10803713842745796205583291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28809903580655456548222109 10803713842745796205583291)
        ·
          refine ⟨16205570764118694308374937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10803713842745796205583291 16205570764118694308374937)
          ·
            refine ⟨12154178073089020731281203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16205570764118694308374937 12154178073089020731281203)
            ·
              refine ⟨18231267109633531096921805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12154178073089020731281203 18231267109633531096921805)
              ·
                refine ⟨6836725166112574161345677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18231267109633531096921805 6836725166112574161345677)
                ·
                  refine ⟨2563771937292215310504629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6836725166112574161345677 2563771937292215310504629)
                  ·
                    refine ⟨240353619121145185359809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2563771937292215310504629 240353619121145185359809)
                    ·
                      rfl

theorem cell23_1404261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_1404261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404261 prefixEnd_1404261 := by exact prefixLift 1404261
  have htrace : WordTrace (prefixWord ++ tailWord_1404261) baseStart_1404261 baseEnd_1404261 := by
    simpa [prefixWord, tailWord_1404261, baseEnd_1404261] using wordTrace_append hprefix tailTrace_1404261
  have hstable : (prefixWord ++ tailWord_1404261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404261).length < 2 ^ (prefixWord ++ tailWord_1404261).sum := by decide
  have hdescent : baseEnd_1404261 < baseStart_1404261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404292 : List Nat := [2, 3, 2, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_1404292 : Nat := 118140960795 + 1404292 * 2 ^ 59
def prefixEnd_1404292 : Nat := 4983230072969 + 3 ^ 40 * 1404292 * 2
def baseEnd_1404292 : Nat := 721076775263724934791785

theorem tailTrace_1404292 : CollatzResearch.WordTrace tailWord_1404292 prefixEnd_1404292 721076775263724934791785 := by
  unfold tailWord_1404292
  simp only [CollatzResearch.WordTrace]
  refine ⟨25609368514248696412275565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34145824685664928549700753 25609368514248696412275565)
  ·
    refine ⟨9603513192843261154603337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25609368514248696412275565 9603513192843261154603337)
    ·
      refine ⟨7202634894632445865952503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9603513192843261154603337 7202634894632445865952503)
      ·
        refine ⟨10803952341948668798928755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7202634894632445865952503 10803952341948668798928755)
        ·
          refine ⟨16205928512923003198393133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10803952341948668798928755 16205928512923003198393133)
          ·
            refine ⟨6077223192346126199397425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16205928512923003198393133 6077223192346126199397425)
            ·
              refine ⟨4557917394259594649548069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6077223192346126199397425 4557917394259594649548069)
              ·
                refine ⟨854609511423673996790263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4557917394259594649548069 854609511423673996790263)
                ·
                  refine ⟨1281914267135510995185395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854609511423673996790263 1281914267135510995185395)
                  ·
                    refine ⟨1922871400703266492778093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1281914267135510995185395 1922871400703266492778093)
                    ·
                      refine ⟨721076775263724934791785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1922871400703266492778093 721076775263724934791785)
                      ·
                        rfl

theorem cell23_1404292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_1404292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404292 prefixEnd_1404292 := by exact prefixLift 1404292
  have htrace : WordTrace (prefixWord ++ tailWord_1404292) baseStart_1404292 baseEnd_1404292 := by
    simpa [prefixWord, tailWord_1404292, baseEnd_1404292] using wordTrace_append hprefix tailTrace_1404292
  have hstable : (prefixWord ++ tailWord_1404292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404292).length < 2 ^ (prefixWord ++ tailWord_1404292).sum := by decide
  have hdescent : baseEnd_1404292 < baseStart_1404292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404398 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1404398 : Nat := 118140960795 + 1404398 * 2 ^ 59
def prefixEnd_1404398 : Nat := 4983230072969 + 3 ^ 40 * 1404398 * 2
def baseEnd_1404398 : Nat := 240377068071033840022099

theorem tailTrace_1404398 : CollatzResearch.WordTrace tailWord_1404398 prefixEnd_1404398 240377068071033840022099 := by
  unfold tailWord_1404398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402825395764171615988731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34148402110742248618606565 6402825395764171615988731)
  ·
    refine ⟨9604238093646257423983097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6402825395764171615988731 9604238093646257423983097)
    ·
      refine ⟨7203178570234693067987323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9604238093646257423983097 7203178570234693067987323)
      ·
        refine ⟨10804767855352039601980985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7203178570234693067987323 10804767855352039601980985)
        ·
          refine ⟨8103575891514029701485739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10804767855352039601980985 8103575891514029701485739)
          ·
            refine ⟨12155363837271044552228609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103575891514029701485739 12155363837271044552228609)
            ·
              refine ⟨9116522877953283414171457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12155363837271044552228609 9116522877953283414171457)
              ·
                refine ⟨6837392158464962560628593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9116522877953283414171457 6837392158464962560628593)
                ·
                  refine ⟨5128044118848721920471445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6837392158464962560628593 5128044118848721920471445)
                  ·
                    refine ⟨240377068071033840022099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5128044118848721920471445 240377068071033840022099)
                    ·
                      rfl

theorem cell23_1404398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1404398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404398 prefixEnd_1404398 := by exact prefixLift 1404398
  have htrace : WordTrace (prefixWord ++ tailWord_1404398) baseStart_1404398 baseEnd_1404398 := by
    simpa [prefixWord, tailWord_1404398, baseEnd_1404398] using wordTrace_append hprefix tailTrace_1404398
  have hstable : (prefixWord ++ tailWord_1404398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404398).length < 2 ^ (prefixWord ++ tailWord_1404398).sum := by decide
  have hdescent : baseEnd_1404398 < baseStart_1404398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404405 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1404405 : Nat := 118140960795 + 1404405 * 2 ^ 59
def prefixEnd_1404405 : Nat := 4983230072969 + 3 ^ 40 * 1404405 * 2
def baseEnd_1404405 : Nat := 721134798577682992678765

theorem tailTrace_1404405 : CollatzResearch.WordTrace tailWord_1404405 prefixEnd_1404405 721134798577682992678765 := by
  unfold tailWord_1404405
  simp only [CollatzResearch.WordTrace]
  refine ⟨51222858477088013123414669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34148572318058675415609779 51222858477088013123414669)
  ·
    refine ⟨19208571928908004921280501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51222858477088013123414669 19208571928908004921280501)
    ·
      refine ⟨1800803618335125461370047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19208571928908004921280501 1800803618335125461370047)
      ·
        refine ⟨2701205427502688192055071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800803618335125461370047 2701205427502688192055071)
        ·
          refine ⟨4051808141254032288082607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701205427502688192055071 4051808141254032288082607)
          ·
            refine ⟨6077712211881048432123911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051808141254032288082607 6077712211881048432123911)
            ·
              refine ⟨9116568317821572648185867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077712211881048432123911 9116568317821572648185867)
              ·
                refine ⟨13674852476732358972278801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9116568317821572648185867 13674852476732358972278801)
                ·
                  refine ⟨10256139357549269229209101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13674852476732358972278801 10256139357549269229209101)
                  ·
                    refine ⟨3846052259080975960953413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10256139357549269229209101 3846052259080975960953413)
                    ·
                      refine ⟨721134798577682992678765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3846052259080975960953413 721134798577682992678765)
                      ·
                        rfl

theorem cell23_1404405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1404405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404405 prefixEnd_1404405 := by exact prefixLift 1404405
  have htrace : WordTrace (prefixWord ++ tailWord_1404405) baseStart_1404405 baseEnd_1404405 := by
    simpa [prefixWord, tailWord_1404405, baseEnd_1404405] using wordTrace_append hprefix tailTrace_1404405
  have hstable : (prefixWord ++ tailWord_1404405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404405).length < 2 ^ (prefixWord ++ tailWord_1404405).sum := by decide
  have hdescent : baseEnd_1404405 < baseStart_1404405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404408 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_1404408 : Nat := 118140960795 + 1404408 * 2 ^ 59
def prefixEnd_1404408 : Nat := 4983230072969 + 3 ^ 40 * 1404408 * 2
def baseEnd_1404408 : Nat := 721136339019646480941251

theorem tailTrace_1404408 : CollatzResearch.WordTrace tailWord_1404408 prefixEnd_1404408 721136339019646480941251 := by
  unfold tailWord_1404408
  simp only [CollatzResearch.WordTrace]
  refine ⟨25611483948038572317886939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34148645264051429757182585 25611483948038572317886939)
  ·
    refine ⟨38417225922057858476830409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25611483948038572317886939 38417225922057858476830409)
    ·
      refine ⟨28812919441543393857622807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38417225922057858476830409 28812919441543393857622807)
      ·
        refine ⟨43219379162315090786434211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28812919441543393857622807 43219379162315090786434211)
        ·
          refine ⟨64829068743472636179651317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43219379162315090786434211 64829068743472636179651317)
          ·
            refine ⟨6077725194700559641842311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64829068743472636179651317 6077725194700559641842311)
            ·
              refine ⟨9116587792050839462763467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077725194700559641842311 9116587792050839462763467)
              ·
                refine ⟨13674881688076259194145201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9116587792050839462763467 13674881688076259194145201)
                ·
                  refine ⟨10256161266057194395608901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13674881688076259194145201 10256161266057194395608901)
                  ·
                    refine ⟨1923030237385723949176669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10256161266057194395608901 1923030237385723949176669)
                    ·
                      refine ⟨721136339019646480941251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1923030237385723949176669 721136339019646480941251)
                      ·
                        rfl

theorem cell23_1404408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_1404408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404408 prefixEnd_1404408 := by exact prefixLift 1404408
  have htrace : WordTrace (prefixWord ++ tailWord_1404408) baseStart_1404408 baseEnd_1404408 := by
    simpa [prefixWord, tailWord_1404408, baseEnd_1404408] using wordTrace_append hprefix tailTrace_1404408
  have hstable : (prefixWord ++ tailWord_1404408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404408).length < 2 ^ (prefixWord ++ tailWord_1404408).sum := by decide
  have hdescent : baseEnd_1404408 < baseStart_1404408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404431 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 6]
def baseStart_1404431 : Nat := 118140960795 + 1404431 * 2 ^ 59
def prefixEnd_1404431 : Nat := 4983230072969 + 3 ^ 40 * 1404431 * 2
def baseEnd_1404431 : Nat := 721148149074699890953645

theorem tailTrace_1404431 : CollatzResearch.WordTrace tailWord_1404431 prefixEnd_1404431 721148149074699890953645 := by
  unfold tailWord_1404431
  simp only [CollatzResearch.WordTrace]
  refine ⟨51223806774993819563861147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34149204516662546375907431 51223806774993819563861147)
  ·
    refine ⟨76835710162490729345791721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51223806774993819563861147 76835710162490729345791721)
    ·
      refine ⟨57626782621868047009343791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76835710162490729345791721 57626782621868047009343791)
      ·
        refine ⟨86440173932802070514015687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57626782621868047009343791 86440173932802070514015687)
        ·
          refine ⟨129660260899203105771023531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86440173932802070514015687 129660260899203105771023531)
          ·
            refine ⟨194490391348804658656535297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129660260899203105771023531 194490391348804658656535297)
            ·
              refine ⟨145867793511603493992401473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194490391348804658656535297 145867793511603493992401473)
              ·
                refine ⟨109400845133702620494301105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145867793511603493992401473 109400845133702620494301105)
                ·
                  refine ⟨82050633850276965370725829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109400845133702620494301105 82050633850276965370725829)
                  ·
                    refine ⟨15384493846926931007011093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82050633850276965370725829 15384493846926931007011093)
                    ·
                      refine ⟨721148149074699890953645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15384493846926931007011093 721148149074699890953645)
                      ·
                        rfl

theorem cell23_1404431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_1404431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404431 prefixEnd_1404431 := by exact prefixLift 1404431
  have htrace : WordTrace (prefixWord ++ tailWord_1404431) baseStart_1404431 baseEnd_1404431 := by
    simpa [prefixWord, tailWord_1404431, baseEnd_1404431] using wordTrace_append hprefix tailTrace_1404431
  have hstable : (prefixWord ++ tailWord_1404431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404431).length < 2 ^ (prefixWord ++ tailWord_1404431).sum := by decide
  have hdescent : baseEnd_1404431 < baseStart_1404431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404462 : List Nat := [4, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_1404462 : Nat := 118140960795 + 1404462 * 2 ^ 59
def prefixEnd_1404462 : Nat := 4983230072969 + 3 ^ 40 * 1404462 * 2
def baseEnd_1404462 : Nat := 80129340774998807740667

theorem tailTrace_1404462 : CollatzResearch.WordTrace tailWord_1404462 prefixEnd_1404462 80129340774998807740667 := by
  unfold tailWord_1404462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403117179735188982279955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34149958291921007905493093 6403117179735188982279955)
  ·
    refine ⟨9604675769602783473419933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6403117179735188982279955 9604675769602783473419933)
    ·
      refine ⟨3601753413601043802532475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9604675769602783473419933 3601753413601043802532475)
      ·
        refine ⟨5402630120401565703798713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3601753413601043802532475 5402630120401565703798713)
        ·
          refine ⟨4051972590301174277849035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5402630120401565703798713 4051972590301174277849035)
          ·
            refine ⟨6077958885451761416773553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051972590301174277849035 6077958885451761416773553)
            ·
              refine ⟨4558469164088821062580165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6077958885451761416773553 4558469164088821062580165)
              ·
                refine ⟨854712968266653949233781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4558469164088821062580165 854712968266653949233781)
                ·
                  refine ⟨80129340774998807740667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 854712968266653949233781 80129340774998807740667)
                  ·
                    rfl

theorem cell23_1404462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_1404462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404462 prefixEnd_1404462 := by exact prefixLift 1404462
  have htrace : WordTrace (prefixWord ++ tailWord_1404462) baseStart_1404462 baseEnd_1404462 := by
    simpa [prefixWord, tailWord_1404462, baseEnd_1404462] using wordTrace_append hprefix tailTrace_1404462
  have hstable : (prefixWord ++ tailWord_1404462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404462).length < 2 ^ (prefixWord ++ tailWord_1404462).sum := by decide
  have hdescent : baseEnd_1404462 < baseStart_1404462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404509 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1404509 : Nat := 118140960795 + 1404509 * 2 ^ 59
def prefixEnd_1404509 : Nat := 4983230072969 + 3 ^ 40 * 1404509 * 2
def baseEnd_1404509 : Nat := 240396066855250195259429

theorem tailTrace_1404509 : CollatzResearch.WordTrace tailWord_1404509 prefixEnd_1404509 240396066855250195259429 := by
  unfold tailWord_1404509
  simp only [CollatzResearch.WordTrace]
  refine ⟨51226651668711238885200581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34151101112474159256800387 51226651668711238885200581)
  ·
    refine ⟨9604997187883357290975109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51226651668711238885200581 9604997187883357290975109)
    ·
      refine ⟨1800936972728129492057833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9604997187883357290975109 1800936972728129492057833)
      ·
        refine ⟨1350702729546097119043375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1800936972728129492057833 1350702729546097119043375)
        ·
          refine ⟨2026054094319145678565063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350702729546097119043375 2026054094319145678565063)
          ·
            refine ⟨3039081141478718517847595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026054094319145678565063 3039081141478718517847595)
            ·
              refine ⟨4558621712218077776771393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3039081141478718517847595 4558621712218077776771393)
              ·
                refine ⟨3418966284163558332578545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4558621712218077776771393 3418966284163558332578545)
                ·
                  refine ⟨2564224713122668749433909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3418966284163558332578545 2564224713122668749433909)
                  ·
                    refine ⟨240396066855250195259429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2564224713122668749433909 240396066855250195259429)
                    ·
                      rfl

theorem cell23_1404509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1404509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404509 prefixEnd_1404509 := by exact prefixLift 1404509
  have htrace : WordTrace (prefixWord ++ tailWord_1404509) baseStart_1404509 baseEnd_1404509 := by
    simpa [prefixWord, tailWord_1404509, baseEnd_1404509] using wordTrace_append hprefix tailTrace_1404509
  have hstable : (prefixWord ++ tailWord_1404509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404509).length < 2 ^ (prefixWord ++ tailWord_1404509).sum := by decide
  have hdescent : baseEnd_1404509 < baseStart_1404509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404515 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 3]
def baseStart_1404515 : Nat := 118140960795 + 1404515 * 2 ^ 59
def prefixEnd_1404515 : Nat := 4983230072969 + 3 ^ 40 * 1404515 * 2
def baseEnd_1404515 : Nat := 721191281449677562303259

theorem tailTrace_1404515 : CollatzResearch.WordTrace tailWord_1404515 prefixEnd_1404515 721191281449677562303259 := by
  unfold tailWord_1404515
  simp only [CollatzResearch.WordTrace]
  refine ⟨51226870506689501909918999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34151247004459667939945999 51226870506689501909918999)
  ·
    refine ⟨76840305760034252864878499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51226870506689501909918999 76840305760034252864878499)
    ·
      refine ⟨115260458640051379297317749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76840305760034252864878499 115260458640051379297317749)
      ·
        refine ⟨10805667997504816809123539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115260458640051379297317749 10805667997504816809123539)
        ·
          refine ⟨16208501996257225213685309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10805667997504816809123539 16208501996257225213685309)
          ·
            refine ⟨6078188248596459455131991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16208501996257225213685309 6078188248596459455131991)
            ·
              refine ⟨9117282372894689182697987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6078188248596459455131991 9117282372894689182697987)
              ·
                refine ⟨13675923559342033774046981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9117282372894689182697987 13675923559342033774046981)
                ·
                  refine ⟨2564235667376631332633809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13675923559342033774046981 2564235667376631332633809)
                  ·
                    refine ⟨1923176750532473499475357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2564235667376631332633809 1923176750532473499475357)
                    ·
                      refine ⟨721191281449677562303259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1923176750532473499475357 721191281449677562303259)
                      ·
                        rfl

theorem cell23_1404515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_1404515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404515 prefixEnd_1404515 := by exact prefixLift 1404515
  have htrace : WordTrace (prefixWord ++ tailWord_1404515) baseStart_1404515 baseEnd_1404515 := by
    simpa [prefixWord, tailWord_1404515, baseEnd_1404515] using wordTrace_append hprefix tailTrace_1404515
  have hstable : (prefixWord ++ tailWord_1404515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404515).length < 2 ^ (prefixWord ++ tailWord_1404515).sum := by decide
  have hdescent : baseEnd_1404515 < baseStart_1404515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404522 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1404522 : Nat := 118140960795 + 1404522 * 2 ^ 59
def prefixEnd_1404522 : Nat := 4983230072969 + 3 ^ 40 * 1404522 * 2
def baseEnd_1404522 : Nat := 240398291938086344971909

theorem tailTrace_1404522 : CollatzResearch.WordTrace tailWord_1404522 prefixEnd_1404522 240398291938086344971909 := by
  unfold tailWord_1404522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12806781454416035526355955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34151417211776094736949213 12806781454416035526355955)
  ·
    refine ⟨19210172181624053289533933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12806781454416035526355955 19210172181624053289533933)
    ·
      refine ⟨7203814568109019983575225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19210172181624053289533933 7203814568109019983575225)
      ·
        refine ⟨5402860926081764987681419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7203814568109019983575225 5402860926081764987681419)
        ·
          refine ⟨8104291389122647481522129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402860926081764987681419 8104291389122647481522129)
          ·
            refine ⟨6078218541841985611141597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8104291389122647481522129 6078218541841985611141597)
            ·
              refine ⟨2279331953190744604178099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6078218541841985611141597 2279331953190744604178099)
              ·
                refine ⟨3418997929786116906267149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279331953190744604178099 3418997929786116906267149)
                ·
                  refine ⟨1282124223669793839850181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3418997929786116906267149 1282124223669793839850181)
                  ·
                    refine ⟨240398291938086344971909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282124223669793839850181 240398291938086344971909)
                    ·
                      rfl

theorem cell23_1404522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1404522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404522 prefixEnd_1404522 := by exact prefixLift 1404522
  have htrace : WordTrace (prefixWord ++ tailWord_1404522) baseStart_1404522 baseEnd_1404522 := by
    simpa [prefixWord, tailWord_1404522, baseEnd_1404522] using wordTrace_append hprefix tailTrace_1404522
  have hstable : (prefixWord ++ tailWord_1404522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404522).length < 2 ^ (prefixWord ++ tailWord_1404522).sum := by decide
  have hdescent : baseEnd_1404522 < baseStart_1404522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404565 : List Nat := [1, 3, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_1404565 : Nat := 118140960795 + 1404565 * 2 ^ 59
def prefixEnd_1404565 : Nat := 4983230072969 + 3 ^ 40 * 1404565 * 2
def baseEnd_1404565 : Nat := 240405651827467455559343

theorem tailTrace_1404565 : CollatzResearch.WordTrace tailWord_1404565 prefixEnd_1404565 240405651827467455559343 := by
  unfold tailWord_1404565
  simp only [CollatzResearch.WordTrace]
  refine ⟨51228694156508360449239149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34152462771005573632826099 51228694156508360449239149)
  ·
    refine ⟨19210760308690635168464681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51228694156508360449239149 19210760308690635168464681)
    ·
      refine ⟨14408070231517976376348511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19210760308690635168464681 14408070231517976376348511)
      ·
        refine ⟨21612105347276964564522767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14408070231517976376348511 21612105347276964564522767)
        ·
          refine ⟨32418158020915446846784151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21612105347276964564522767 32418158020915446846784151)
          ·
            refine ⟨48627237031373170270176227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32418158020915446846784151 48627237031373170270176227)
            ·
              refine ⟨72940855547059755405264341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48627237031373170270176227 72940855547059755405264341)
              ·
                refine ⟨1709551301884213017310883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72940855547059755405264341 1709551301884213017310883)
                ·
                  refine ⟨2564326952826319525966325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709551301884213017310883 2564326952826319525966325)
                  ·
                    refine ⟨240405651827467455559343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2564326952826319525966325 240405651827467455559343)
                    ·
                      rfl

theorem cell23_1404565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_1404565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404565 prefixEnd_1404565 := by exact prefixLift 1404565
  have htrace : WordTrace (prefixWord ++ tailWord_1404565) baseStart_1404565 baseEnd_1404565 := by
    simpa [prefixWord, tailWord_1404565, baseEnd_1404565] using wordTrace_append hprefix tailTrace_1404565
  have hstable : (prefixWord ++ tailWord_1404565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404565).length < 2 ^ (prefixWord ++ tailWord_1404565).sum := by decide
  have hdescent : baseEnd_1404565 < baseStart_1404565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404579 : List Nat := [1, 1, 1, 4, 1, 1, 5, 4, 1, 1, 3]
def baseStart_1404579 : Nat := 118140960795 + 1404579 * 2 ^ 59
def prefixEnd_1404579 : Nat := 4983230072969 + 3 ^ 40 * 1404579 * 2
def baseEnd_1404579 : Nat := 721224144211565311902965

theorem tailTrace_1404579 : CollatzResearch.WordTrace tailWord_1404579 prefixEnd_1404579 721224144211565311902965 := by
  unfold tailWord_1404579
  simp only [CollatzResearch.WordTrace]
  refine ⟨51229204778457640840248791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34152803185638427226832527 51229204778457640840248791)
  ·
    refine ⟨76843807167686461260373187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51229204778457640840248791 76843807167686461260373187)
    ·
      refine ⟨115265710751529691890559781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76843807167686461260373187 115265710751529691890559781)
      ·
        refine ⟨21612320765911817229479959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115265710751529691890559781 21612320765911817229479959)
        ·
          refine ⟨32418481148867725844219939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21612320765911817229479959 32418481148867725844219939)
          ·
            refine ⟨48627721723301588766329909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32418481148867725844219939 48627721723301588766329909)
            ·
              refine ⟨4558848911559523946843429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48627721723301588766329909 4558848911559523946843429)
              ·
                refine ⟨854784170917410740033143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4558848911559523946843429 854784170917410740033143)
                ·
                  refine ⟨1282176256376116110049715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 854784170917410740033143 1282176256376116110049715)
                  ·
                    refine ⟨1923264384564174165074573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1282176256376116110049715 1923264384564174165074573)
                    ·
                      refine ⟨721224144211565311902965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1923264384564174165074573 721224144211565311902965)
                      ·
                        rfl

theorem cell23_1404579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_1404579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404579 prefixEnd_1404579 := by exact prefixLift 1404579
  have htrace : WordTrace (prefixWord ++ tailWord_1404579) baseStart_1404579 baseEnd_1404579 := by
    simpa [prefixWord, tailWord_1404579, baseEnd_1404579] using wordTrace_append hprefix tailTrace_1404579
  have hstable : (prefixWord ++ tailWord_1404579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404579).length < 2 ^ (prefixWord ++ tailWord_1404579).sum := by decide
  have hdescent : baseEnd_1404579 < baseStart_1404579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404595 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 1, 6]
def baseStart_1404595 : Nat := 118140960795 + 1404595 * 2 ^ 59
def prefixEnd_1404595 : Nat := 4983230072969 + 3 ^ 40 * 1404595 * 2
def baseEnd_1404595 : Nat := 240410786634012416434297

theorem tailTrace_1404595 : CollatzResearch.WordTrace tailWord_1404595 prefixEnd_1404595 240410786634012416434297 := by
  unfold tailWord_1404595
  simp only [CollatzResearch.WordTrace]
  refine ⟨51229788346399675572831239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34153192230933117048554159 51229788346399675572831239)
  ·
    refine ⟨76844682519599513359246859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51229788346399675572831239 76844682519599513359246859)
    ·
      refine ⟨115267023779399270038870289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76844682519599513359246859 115267023779399270038870289)
      ·
        refine ⟨86450267834549452529152717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115267023779399270038870289 86450267834549452529152717)
        ·
          refine ⟨32418850437956044698432269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86450267834549452529152717 32418850437956044698432269)
          ·
            refine ⟨12157068914233516761912101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32418850437956044698432269 12157068914233516761912101)
            ·
              refine ⟨2279450421418784392858519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12157068914233516761912101 2279450421418784392858519)
              ·
                refine ⟨3419175632128176589287779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279450421418784392858519 3419175632128176589287779)
                ·
                  refine ⟨5128763448192264883931669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419175632128176589287779 5128763448192264883931669)
                  ·
                    refine ⟨240410786634012416434297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5128763448192264883931669 240410786634012416434297)
                    ·
                      rfl

theorem cell23_1404595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 6].length) (baseStart_1404595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404595 prefixEnd_1404595 := by exact prefixLift 1404595
  have htrace : WordTrace (prefixWord ++ tailWord_1404595) baseStart_1404595 baseEnd_1404595 := by
    simpa [prefixWord, tailWord_1404595, baseEnd_1404595] using wordTrace_append hprefix tailTrace_1404595
  have hstable : (prefixWord ++ tailWord_1404595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404595).length < 2 ^ (prefixWord ++ tailWord_1404595).sum := by decide
  have hdescent : baseEnd_1404595 < baseStart_1404595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404606 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_1404606 : Nat := 118140960795 + 1404606 * 2 ^ 59
def prefixEnd_1404606 : Nat := 4983230072969 + 3 ^ 40 * 1404606 * 2
def baseEnd_1404606 : Nat := 721238008189236706265341

theorem tailTrace_1404606 : CollatzResearch.WordTrace tailWord_1404606 prefixEnd_1404606 721238008189236706265341 := by
  unfold tailWord_1404606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403773693669978056435209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34153459699573216300987781 6403773693669978056435209)
  ·
    refine ⟨4802830270252483542326407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6403773693669978056435209 4802830270252483542326407)
    ·
      refine ⟨7204245405378725313489611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4802830270252483542326407 7204245405378725313489611)
      ·
        refine ⟨10806368108068087970234417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7204245405378725313489611 10806368108068087970234417)
        ·
          refine ⟨8104776081051065977675813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10806368108068087970234417 8104776081051065977675813)
          ·
            refine ⟨1519645515197074870814215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8104776081051065977675813 1519645515197074870814215)
            ·
              refine ⟨2279468272795612306221323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519645515197074870814215 2279468272795612306221323)
              ·
                refine ⟨3419202409193418459331985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279468272795612306221323 3419202409193418459331985)
                ·
                  refine ⟨2564401806895063844498989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3419202409193418459331985 2564401806895063844498989)
                  ·
                    refine ⟨961650677585648941687121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2564401806895063844498989 961650677585648941687121)
                    ·
                      refine ⟨721238008189236706265341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 961650677585648941687121 721238008189236706265341)
                      ·
                        rfl

theorem cell23_1404606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_1404606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404606 prefixEnd_1404606 := by exact prefixLift 1404606
  have htrace : WordTrace (prefixWord ++ tailWord_1404606) baseStart_1404606 baseEnd_1404606 := by
    simpa [prefixWord, tailWord_1404606, baseEnd_1404606] using wordTrace_append hprefix tailTrace_1404606
  have hstable : (prefixWord ++ tailWord_1404606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404606).length < 2 ^ (prefixWord ++ tailWord_1404606).sum := by decide
  have hdescent : baseEnd_1404606 < baseStart_1404606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404612 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1404612 : Nat := 118140960795 + 1404612 * 2 ^ 59
def prefixEnd_1404612 : Nat := 4983230072969 + 3 ^ 40 * 1404612 * 2
def baseEnd_1404612 : Nat := 240413696357721227596771

theorem tailTrace_1404612 : CollatzResearch.WordTrace tailWord_1404612 prefixEnd_1404612 240413696357721227596771 := by
  unfold tailWord_1404612
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615204193669043738100045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34153605591558724984133393 25615204193669043738100045)
  ·
    refine ⟨9605701572625891401787517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25615204193669043738100045 9605701572625891401787517)
    ·
      refine ⟨3602138089734709275670319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9605701572625891401787517 3602138089734709275670319)
      ·
        refine ⟨5403207134602063913505479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3602138089734709275670319 5403207134602063913505479)
        ·
          refine ⟨8104810701903095870258219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403207134602063913505479 8104810701903095870258219)
          ·
            refine ⟨12157216052854643805387329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8104810701903095870258219 12157216052854643805387329)
            ·
              refine ⟨9117912039640982854040497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12157216052854643805387329 9117912039640982854040497)
              ·
                refine ⟨6838434029730737140530373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9117912039640982854040497 6838434029730737140530373)
                ·
                  refine ⟨1282206380574513213849445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6838434029730737140530373 1282206380574513213849445)
                  ·
                    refine ⟨240413696357721227596771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282206380574513213849445 240413696357721227596771)
                    ·
                      rfl

theorem cell23_1404612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1404612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404612 prefixEnd_1404612 := by exact prefixLift 1404612
  have htrace : WordTrace (prefixWord ++ tailWord_1404612) baseStart_1404612 baseEnd_1404612 := by
    simpa [prefixWord, tailWord_1404612, baseEnd_1404612] using wordTrace_append hprefix tailTrace_1404612
  have hstable : (prefixWord ++ tailWord_1404612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404612).length < 2 ^ (prefixWord ++ tailWord_1404612).sum := by decide
  have hdescent : baseEnd_1404612 < baseStart_1404612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404615 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1404615 : Nat := 118140960795 + 1404615 * 2 ^ 59
def prefixEnd_1404615 : Nat := 4983230072969 + 3 ^ 40 * 1404615 * 2
def baseEnd_1404615 : Nat := 721242629515127171052799

theorem tailTrace_1404615 : CollatzResearch.WordTrace tailWord_1404615 prefixEnd_1404615 721242629515127171052799 := by
  unfold tailWord_1404615
  simp only [CollatzResearch.WordTrace]
  refine ⟨51230517806327218988559299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34153678537551479325706199 51230517806327218988559299)
  ·
    refine ⟨76845776709490828482838949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51230517806327218988559299 76845776709490828482838949)
    ·
      refine ⟨14408583133029530340532303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76845776709490828482838949 14408583133029530340532303)
      ·
        refine ⟨21612874699544295510798455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14408583133029530340532303 21612874699544295510798455)
        ·
          refine ⟨32419312049316443266197683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21612874699544295510798455 32419312049316443266197683)
          ·
            refine ⟨48628968073974664899296525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32419312049316443266197683 48628968073974664899296525)
            ·
              refine ⟨18235863027740499337236197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48628968073974664899296525 18235863027740499337236197)
              ·
                refine ⟨3419224317701343625731787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18235863027740499337236197 3419224317701343625731787)
                ·
                  refine ⟨5128836476552015438597681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419224317701343625731787 5128836476552015438597681)
                  ·
                    refine ⟨3846627357414011578948261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5128836476552015438597681 3846627357414011578948261)
                    ·
                      refine ⟨721242629515127171052799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3846627357414011578948261 721242629515127171052799)
                      ·
                        rfl

theorem cell23_1404615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1404615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404615 prefixEnd_1404615 := by exact prefixLift 1404615
  have htrace : WordTrace (prefixWord ++ tailWord_1404615) baseStart_1404615 baseEnd_1404615 := by
    simpa [prefixWord, tailWord_1404615, baseEnd_1404615] using wordTrace_append hprefix tailTrace_1404615
  have hstable : (prefixWord ++ tailWord_1404615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404615).length < 2 ^ (prefixWord ++ tailWord_1404615).sum := by decide
  have hdescent : baseEnd_1404615 < baseStart_1404615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404652 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 3]
def baseStart_1404652 : Nat := 118140960795 + 1404652 * 2 ^ 59
def prefixEnd_1404652 : Nat := 4983230072969 + 3 ^ 40 * 1404652 * 2
def baseEnd_1404652 : Nat := 721261628299343526290129

theorem tailTrace_1404652 : CollatzResearch.WordTrace tailWord_1404652 prefixEnd_1404652 721261628299343526290129 := by
  unfold tailWord_1404652
  simp only [CollatzResearch.WordTrace]
  refine ⟨25615933653596587153828105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34154578204795449538437473 25615933653596587153828105)
  ·
    refine ⟨19211950240197440365371079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25615933653596587153828105 19211950240197440365371079)
    ·
      refine ⟨28817925360296160548056619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19211950240197440365371079 28817925360296160548056619)
      ·
        refine ⟨43226888040444240822084929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28817925360296160548056619 43226888040444240822084929)
        ·
          refine ⟨32420166030333180616563697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43226888040444240822084929 32420166030333180616563697)
          ·
            refine ⟨24315124522749885462422773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32420166030333180616563697 24315124522749885462422773)
            ·
              refine ⟨2279542924007801762102135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24315124522749885462422773 2279542924007801762102135)
              ·
                refine ⟨3419314386011702643153203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279542924007801762102135 3419314386011702643153203)
                ·
                  refine ⟨5128971579017553964729805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419314386011702643153203 5128971579017553964729805)
                  ·
                    refine ⟨1923364342131582736773677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5128971579017553964729805 1923364342131582736773677)
                    ·
                      refine ⟨721261628299343526290129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1923364342131582736773677 721261628299343526290129)
                      ·
                        rfl

theorem cell23_1404652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_1404652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404652 prefixEnd_1404652 := by exact prefixLift 1404652
  have htrace : WordTrace (prefixWord ++ tailWord_1404652) baseStart_1404652 baseEnd_1404652 := by
    simpa [prefixWord, tailWord_1404652, baseEnd_1404652] using wordTrace_append hprefix tailTrace_1404652
  have hstable : (prefixWord ++ tailWord_1404652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404652).length < 2 ^ (prefixWord ++ tailWord_1404652).sum := by decide
  have hdescent : baseEnd_1404652 < baseStart_1404652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404712 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1404712 : Nat := 118140960795 + 1404712 * 2 ^ 59
def prefixEnd_1404712 : Nat := 4983230072969 + 3 ^ 40 * 1404712 * 2
def baseEnd_1404712 : Nat := 721292437138613291539853

theorem tailTrace_1404712 : CollatzResearch.WordTrace tailWord_1404712 prefixEnd_1404712 721292437138613291539853 := by
  unfold tailWord_1404712
  simp only [CollatzResearch.WordTrace]
  refine ⟨25617027843487902277420195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34156037124650536369893593 25617027843487902277420195)
  ·
    refine ⟨38425541765231853416130293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25617027843487902277420195 38425541765231853416130293)
    ·
      refine ⟨3602394540490486257762215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38425541765231853416130293 3602394540490486257762215)
      ·
        refine ⟨5403591810735729386643323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3602394540490486257762215 5403591810735729386643323)
        ·
          refine ⟨8105387716103594079964985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5403591810735729386643323 8105387716103594079964985)
          ·
            refine ⟨6079040787077695559973739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8105387716103594079964985 6079040787077695559973739)
            ·
              refine ⟨9118561180616543339960609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6079040787077695559973739 9118561180616543339960609)
              ·
                refine ⟨6838920885462407504970457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9118561180616543339960609 6838920885462407504970457)
                ·
                  refine ⟨5129190664096805628727843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6838920885462407504970457 5129190664096805628727843)
                  ·
                    refine ⟨7693785996145208443091765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5129190664096805628727843 7693785996145208443091765)
                    ·
                      refine ⟨721292437138613291539853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7693785996145208443091765 721292437138613291539853)
                      ·
                        rfl

theorem cell23_1404712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1404712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404712 prefixEnd_1404712 := by exact prefixLift 1404712
  have htrace : WordTrace (prefixWord ++ tailWord_1404712) baseStart_1404712 baseEnd_1404712 := by
    simpa [prefixWord, tailWord_1404712, baseEnd_1404712] using wordTrace_append hprefix tailTrace_1404712
  have hstable : (prefixWord ++ tailWord_1404712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404712).length < 2 ^ (prefixWord ++ tailWord_1404712).sum := by decide
  have hdescent : baseEnd_1404712 < baseStart_1404712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404726 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1404726 : Nat := 118140960795 + 1404726 * 2 ^ 59
def prefixEnd_1404726 : Nat := 4983230072969 + 3 ^ 40 * 1404726 * 2
def baseEnd_1404726 : Nat := 721299625867776236764789

theorem tailTrace_1404726 : CollatzResearch.WordTrace tailWord_1404726 prefixEnd_1404726 721299625867776236764789 := by
  unfold tailWord_1404726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3202160394307817809115627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34156377539283389963900021 3202160394307817809115627)
  ·
    refine ⟨4803240591461726713673441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3202160394307817809115627 4803240591461726713673441)
    ·
      refine ⟨3602430443596295035255081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4803240591461726713673441 3602430443596295035255081)
      ·
        refine ⟨2701822832697221276441311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3602430443596295035255081 2701822832697221276441311)
        ·
          refine ⟨4052734249045831914661967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701822832697221276441311 4052734249045831914661967)
          ·
            refine ⟨6079101373568747871992951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4052734249045831914661967 6079101373568747871992951)
            ·
              refine ⟨9118652060353121807989427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6079101373568747871992951 9118652060353121807989427)
              ·
                refine ⟨13677978090529682711984141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9118652060353121807989427 13677978090529682711984141)
                ·
                  refine ⟨5129241783948631016994053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13677978090529682711984141 5129241783948631016994053)
                  ·
                    refine ⟨961732834490368315686385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5129241783948631016994053 961732834490368315686385)
                    ·
                      refine ⟨721299625867776236764789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 961732834490368315686385 721299625867776236764789)
                      ·
                        rfl

theorem cell23_1404726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1404726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404726 prefixEnd_1404726 := by exact prefixLift 1404726
  have htrace : WordTrace (prefixWord ++ tailWord_1404726) baseStart_1404726 baseEnd_1404726 := by
    simpa [prefixWord, tailWord_1404726, baseEnd_1404726] using wordTrace_append hprefix tailTrace_1404726
  have hstable : (prefixWord ++ tailWord_1404726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404726).length < 2 ^ (prefixWord ++ tailWord_1404726).sum := by decide
  have hdescent : baseEnd_1404726 < baseStart_1404726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404759 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_1404759 : Nat := 118140960795 + 1404759 * 2 ^ 59
def prefixEnd_1404759 : Nat := 4983230072969 + 3 ^ 40 * 1404759 * 2
def baseEnd_1404759 : Nat := 721316570729374607652137

theorem tailTrace_1404759 : CollatzResearch.WordTrace tailWord_1404759 prefixEnd_1404759 721316570729374607652137 := by
  unfold tailWord_1404759
  simp only [CollatzResearch.WordTrace]
  refine ⟨51235769917805531581801331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34157179945203687721200887 51235769917805531581801331)
  ·
    refine ⟨76853654876708297372701997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51235769917805531581801331 76853654876708297372701997)
    ·
      refine ⟨28820120578765611514763249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76853654876708297372701997 28820120578765611514763249)
      ·
        refine ⟨21615090434074208636072437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28820120578765611514763249 21615090434074208636072437)
        ·
          refine ⟨2026414728194457059631791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21615090434074208636072437 2026414728194457059631791)
          ·
            refine ⟨3039622092291685589447687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026414728194457059631791 3039622092291685589447687)
            ·
              refine ⟨4559433138437528384171531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3039622092291685589447687 4559433138437528384171531)
              ·
                refine ⟨6839149707656292576257297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4559433138437528384171531 6839149707656292576257297)
                ·
                  refine ⟨5129362280742219432192973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6839149707656292576257297 5129362280742219432192973)
                  ·
                    refine ⟨1923510855278332287072365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5129362280742219432192973 1923510855278332287072365)
                    ·
                      refine ⟨721316570729374607652137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1923510855278332287072365 721316570729374607652137)
                      ·
                        rfl

theorem cell23_1404759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_1404759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404759 prefixEnd_1404759 := by exact prefixLift 1404759
  have htrace : WordTrace (prefixWord ++ tailWord_1404759) baseStart_1404759 baseEnd_1404759 := by
    simpa [prefixWord, tailWord_1404759, baseEnd_1404759] using wordTrace_append hprefix tailTrace_1404759
  have hstable : (prefixWord ++ tailWord_1404759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404759).length < 2 ^ (prefixWord ++ tailWord_1404759).sum := by decide
  have hdescent : baseEnd_1404759 < baseStart_1404759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404809 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 3, 4]
def baseStart_1404809 : Nat := 118140960795 + 1404809 * 2 ^ 59
def prefixEnd_1404809 : Nat := 4983230072969 + 3 ^ 40 * 1404809 * 2
def baseEnd_1404809 : Nat := 240447414920699804008969

theorem tailTrace_1404809 : CollatzResearch.WordTrace tailWord_1404809 prefixEnd_1404809 240447414920699804008969 := by
  unfold tailWord_1404809
  simp only [CollatzResearch.WordTrace]
  refine ⟨51237593567624390121121481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34158395711749593414080987 51237593567624390121121481)
  ·
    refine ⟨38428195175718292590841111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51237593567624390121121481 38428195175718292590841111)
    ·
      refine ⟨57642292763577438886261667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38428195175718292590841111 57642292763577438886261667)
      ·
        refine ⟨86463439145366158329392501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57642292763577438886261667 86463439145366158329392501)
        ·
          refine ⟨8105947419878077343380547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86463439145366158329392501 8105947419878077343380547)
          ·
            refine ⟨12158921129817116015070821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8105947419878077343380547 12158921129817116015070821)
            ·
              refine ⟨2279797711840709252825779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12158921129817116015070821 2279797711840709252825779)
              ·
                refine ⟨3419696567761063879238669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279797711840709252825779 3419696567761063879238669)
                ·
                  refine ⟨1282386212910398954714501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3419696567761063879238669 1282386212910398954714501)
                  ·
                    refine ⟨240447414920699804008969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282386212910398954714501 240447414920699804008969)
                    ·
                      rfl

theorem cell23_1404809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 4].length) (baseStart_1404809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404809 prefixEnd_1404809 := by exact prefixLift 1404809
  have htrace : WordTrace (prefixWord ++ tailWord_1404809) baseStart_1404809 baseEnd_1404809 := by
    simpa [prefixWord, tailWord_1404809, baseEnd_1404809] using wordTrace_append hprefix tailTrace_1404809
  have hstable : (prefixWord ++ tailWord_1404809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404809).length < 2 ^ (prefixWord ++ tailWord_1404809).sum := by decide
  have hdescent : baseEnd_1404809 < baseStart_1404809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404815 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 9]
def baseStart_1404815 : Nat := 118140960795 + 1404815 * 2 ^ 59
def prefixEnd_1404815 : Nat := 4983230072969 + 3 ^ 40 * 1404815 * 2
def baseEnd_1404815 : Nat := 721345325646026388551879

theorem tailTrace_1404815 : CollatzResearch.WordTrace tailWord_1404815 prefixEnd_1404815 721345325646026388551879 := by
  unfold tailWord_1404815
  simp only [CollatzResearch.WordTrace]
  refine ⟨51237812405602653145839899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34158541603735102097226599 51237812405602653145839899)
  ·
    refine ⟨76856718608403979718759849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51237812405602653145839899 76856718608403979718759849)
    ·
      refine ⟨57642538956302984789069887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76856718608403979718759849 57642538956302984789069887)
      ·
        refine ⟨86463808434454477183604831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57642538956302984789069887 86463808434454477183604831)
        ·
          refine ⟨129695712651681715775407247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86463808434454477183604831 129695712651681715775407247)
          ·
            refine ⟨194543568977522573663110871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129695712651681715775407247 194543568977522573663110871)
            ·
              refine ⟨291815353466283860494666307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194543568977522573663110871 291815353466283860494666307)
              ·
                refine ⟨437723030199425790741999461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291815353466283860494666307 437723030199425790741999461)
                ·
                  refine ⟨82073068162392335764124899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437723030199425790741999461 82073068162392335764124899)
                  ·
                    refine ⟨123109602243588503646187349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82073068162392335764124899 123109602243588503646187349)
                    ·
                      refine ⟨721345325646026388551879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 123109602243588503646187349 721345325646026388551879)
                      ·
                        rfl

theorem cell23_1404815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_1404815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404815 prefixEnd_1404815 := by exact prefixLift 1404815
  have htrace : WordTrace (prefixWord ++ tailWord_1404815) baseStart_1404815 baseEnd_1404815 := by
    simpa [prefixWord, tailWord_1404815, baseEnd_1404815] using wordTrace_append hprefix tailTrace_1404815
  have hstable : (prefixWord ++ tailWord_1404815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404815).length < 2 ^ (prefixWord ++ tailWord_1404815).sum := by decide
  have hdescent : baseEnd_1404815 < baseStart_1404815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404832 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1404832 : Nat := 118140960795 + 1404832 * 2 ^ 59
def prefixEnd_1404832 : Nat := 4983230072969 + 3 ^ 40 * 1404832 * 2
def baseEnd_1404832 : Nat := 721354054817152822039301

theorem tailTrace_1404832 : CollatzResearch.WordTrace tailWord_1404832 prefixEnd_1404832 721354054817152822039301 := by
  unfold tailWord_1404832
  simp only [CollatzResearch.WordTrace]
  refine ⟨25619216223270532524604375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34158954964360710032805833 25619216223270532524604375)
  ·
    refine ⟨38428824334905798786906563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25619216223270532524604375 38428824334905798786906563)
    ·
      refine ⟨57643236502358698180359845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38428824334905798786906563 57643236502358698180359845)
      ·
        refine ⟨10808106844192255908817471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57643236502358698180359845 10808106844192255908817471)
        ·
          refine ⟨16212160266288383863226207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10808106844192255908817471 16212160266288383863226207)
          ·
            refine ⟨24318240399432575794839311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16212160266288383863226207 24318240399432575794839311)
            ·
              refine ⟨36477360599148863692258967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24318240399432575794839311 36477360599148863692258967)
              ·
                refine ⟨54716040898723295538388451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36477360599148863692258967 54716040898723295538388451)
                ·
                  refine ⟨82074061348084943307582677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54716040898723295538388451 82074061348084943307582677)
                  ·
                    refine ⟨1923610812845740858771469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 82074061348084943307582677 1923610812845740858771469)
                    ·
                      refine ⟨721354054817152822039301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1923610812845740858771469 721354054817152822039301)
                      ·
                        rfl

theorem cell23_1404832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1404832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404832 prefixEnd_1404832 := by exact prefixLift 1404832
  have htrace : WordTrace (prefixWord ++ tailWord_1404832) baseStart_1404832 baseEnd_1404832 := by
    simpa [prefixWord, tailWord_1404832, baseEnd_1404832] using wordTrace_append hprefix tailTrace_1404832
  have hstable : (prefixWord ++ tailWord_1404832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404832).length < 2 ^ (prefixWord ++ tailWord_1404832).sum := by decide
  have hdescent : baseEnd_1404832 < baseStart_1404832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404859 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 4, 3, 2]
def baseStart_1404859 : Nat := 118140960795 + 1404859 * 2 ^ 59
def prefixEnd_1404859 : Nat := 4983230072969 + 3 ^ 40 * 1404859 * 2
def baseEnd_1404859 : Nat := 721367918794824216401677

theorem tailTrace_1404859 : CollatzResearch.WordTrace tailWord_1404859 prefixEnd_1404859 721367918794824216401677 := by
  unfold tailWord_1404859
  simp only [CollatzResearch.WordTrace]
  refine ⟨51239417217443248660441631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34159611478295499106961087 51239417217443248660441631)
  ·
    refine ⟨76859125826164872990662447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51239417217443248660441631 76859125826164872990662447)
    ·
      refine ⟨115288688739247309485993671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76859125826164872990662447 115288688739247309485993671)
      ·
        refine ⟨172933033108870964228990507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115288688739247309485993671 172933033108870964228990507)
        ·
          refine ⟨259399549663306446343485761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172933033108870964228990507 259399549663306446343485761)
          ·
            refine ⟨194549662247479834757614321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259399549663306446343485761 194549662247479834757614321)
            ·
              refine ⟨145912246685609876068210741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194549662247479834757614321 145912246685609876068210741)
              ·
                refine ⟨13679273126775925881394757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145912246685609876068210741 13679273126775925881394757)
                ·
                  refine ⟨2564863711270486102761517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13679273126775925881394757 2564863711270486102761517)
                  ·
                    refine ⟨961823891726432288535569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2564863711270486102761517 961823891726432288535569)
                    ·
                      refine ⟨721367918794824216401677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 961823891726432288535569 721367918794824216401677)
                      ·
                        rfl

theorem cell23_1404859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 3, 2].length) (baseStart_1404859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404859 prefixEnd_1404859 := by exact prefixLift 1404859
  have htrace : WordTrace (prefixWord ++ tailWord_1404859) baseStart_1404859 baseEnd_1404859 := by
    simpa [prefixWord, tailWord_1404859, baseEnd_1404859] using wordTrace_append hprefix tailTrace_1404859
  have hstable : (prefixWord ++ tailWord_1404859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404859).length < 2 ^ (prefixWord ++ tailWord_1404859).sum := by decide
  have hdescent : baseEnd_1404859 < baseStart_1404859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404860 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_1404860 : Nat := 118140960795 + 1404860 * 2 ^ 59
def prefixEnd_1404860 : Nat := 4983230072969 + 3 ^ 40 * 1404860 * 2
def baseEnd_1404860 : Nat := 240456144091826237496391

theorem tailTrace_1404860 : CollatzResearch.WordTrace tailWord_1404860 prefixEnd_1404860 240456144091826237496391 := by
  unfold tailWord_1404860
  simp only [CollatzResearch.WordTrace]
  refine ⟨25619726845219812915614017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34159635793626417220818689 25619726845219812915614017)
  ·
    refine ⟨19214795133914859686710513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25619726845219812915614017 19214795133914859686710513)
    ·
      refine ⟨14411096350436144765032885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19214795133914859686710513 14411096350436144765032885)
      ·
        refine ⟨1351040282853388571721833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14411096350436144765032885 1351040282853388571721833)
        ·
          refine ⟨1013280212140041428791375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1351040282853388571721833 1013280212140041428791375)
          ·
            refine ⟨1519920318210062143187063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013280212140041428791375 1519920318210062143187063)
            ·
              refine ⟨2279880477315093214780595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1519920318210062143187063 2279880477315093214780595)
              ·
                refine ⟨3419820715972639822170893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279880477315093214780595 3419820715972639822170893)
                ·
                  refine ⟨1282432768489739933314085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3419820715972639822170893 1282432768489739933314085)
                  ·
                    refine ⟨240456144091826237496391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282432768489739933314085 240456144091826237496391)
                    ·
                      rfl

theorem cell23_1404860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_1404860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404860 prefixEnd_1404860 := by exact prefixLift 1404860
  have htrace : WordTrace (prefixWord ++ tailWord_1404860) baseStart_1404860 baseEnd_1404860 := by
    simpa [prefixWord, tailWord_1404860, baseEnd_1404860] using wordTrace_append hprefix tailTrace_1404860
  have hstable : (prefixWord ++ tailWord_1404860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404860).length < 2 ^ (prefixWord ++ tailWord_1404860).sum := by decide
  have hdescent : baseEnd_1404860 < baseStart_1404860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404899 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 1, 6]
def baseStart_1404899 : Nat := 118140960795 + 1404899 * 2 ^ 59
def prefixEnd_1404899 : Nat := 4983230072969 + 3 ^ 40 * 1404899 * 2
def baseEnd_1404899 : Nat := 240462819340334686633831

theorem tailTrace_1404899 : CollatzResearch.WordTrace tailWord_1404899 prefixEnd_1404899 240462819340334686633831 := by
  unfold tailWord_1404899
  simp only [CollatzResearch.WordTrace]
  refine ⟨51240876137298335491897751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34160584091532223661265167 51240876137298335491897751)
  ·
    refine ⟨76861314205947503237846627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51240876137298335491897751 76861314205947503237846627)
    ·
      refine ⟨115291971308921254856769941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76861314205947503237846627 115291971308921254856769941)
      ·
        refine ⟨5404311155105683821411091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115291971308921254856769941 5404311155105683821411091)
        ·
          refine ⟨8106466732658525732116637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404311155105683821411091 8106466732658525732116637)
          ·
            refine ⟨3039925024746947149543739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8106466732658525732116637 3039925024746947149543739)
            ·
              refine ⟨4559887537120420724315609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3039925024746947149543739 4559887537120420724315609)
              ·
                refine ⟨3419915652840315543236707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4559887537120420724315609 3419915652840315543236707)
                ·
                  refine ⟨5129873479260473314855061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3419915652840315543236707 5129873479260473314855061)
                  ·
                    refine ⟨240462819340334686633831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5129873479260473314855061 240462819340334686633831)
                    ·
                      rfl

theorem cell23_1404899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 6].length) (baseStart_1404899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404899 prefixEnd_1404899 := by exact prefixLift 1404899
  have htrace : WordTrace (prefixWord ++ tailWord_1404899) baseStart_1404899 baseEnd_1404899 := by
    simpa [prefixWord, tailWord_1404899, baseEnd_1404899] using wordTrace_append hprefix tailTrace_1404899
  have hstable : (prefixWord ++ tailWord_1404899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404899).length < 2 ^ (prefixWord ++ tailWord_1404899).sum := by decide
  have hdescent : baseEnd_1404899 < baseStart_1404899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404903 : List Nat := [1, 1, 5, 2, 3, 1, 3, 1, 1, 5]
def baseStart_1404903 : Nat := 118140960795 + 1404903 * 2 ^ 59
def prefixEnd_1404903 : Nat := 4983230072969 + 3 ^ 40 * 1404903 * 2
def baseEnd_1404903 : Nat := 240463503981207348083825

theorem tailTrace_1404903 : CollatzResearch.WordTrace tailWord_1404903 prefixEnd_1404903 240463503981207348083825 := by
  unfold tailWord_1404903
  simp only [CollatzResearch.WordTrace]
  refine ⟨51241022029283844175043363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34160681352855896116695575 51241022029283844175043363)
  ·
    refine ⟨76861533043925766262565045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51241022029283844175043363 76861533043925766262565045)
    ·
      refine ⟨7205768722868040587115473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76861533043925766262565045 7205768722868040587115473)
      ·
        refine ⟨5404326542151030440336605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7205768722868040587115473 5404326542151030440336605)
        ·
          refine ⟨2026622453306636415126227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5404326542151030440336605 2026622453306636415126227)
          ·
            refine ⟨3039933679959954622689341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026622453306636415126227 3039933679959954622689341)
            ·
              refine ⟨1139975129984982983508503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3039933679959954622689341 1139975129984982983508503)
              ·
                refine ⟨1709962694977474475262755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1139975129984982983508503 1709962694977474475262755)
                ·
                  refine ⟨2564944042466211712894133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1709962694977474475262755 2564944042466211712894133)
                  ·
                    refine ⟨240463503981207348083825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2564944042466211712894133 240463503981207348083825)
                    ·
                      rfl

theorem cell23_1404903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_1404903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404903 prefixEnd_1404903 := by exact prefixLift 1404903
  have htrace : WordTrace (prefixWord ++ tailWord_1404903) baseStart_1404903 baseEnd_1404903 := by
    simpa [prefixWord, tailWord_1404903, baseEnd_1404903] using wordTrace_append hprefix tailTrace_1404903
  have hstable : (prefixWord ++ tailWord_1404903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404903).length < 2 ^ (prefixWord ++ tailWord_1404903).sum := by decide
  have hdescent : baseEnd_1404903 < baseStart_1404903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404934 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1404934 : Nat := 118140960795 + 1404934 * 2 ^ 59
def prefixEnd_1404934 : Nat := 4983230072969 + 3 ^ 40 * 1404934 * 2
def baseEnd_1404934 : Nat := 721406429843911422963833

theorem tailTrace_1404934 : CollatzResearch.WordTrace tailWord_1404934 prefixEnd_1404934 721406429843911422963833 := by
  unfold tailWord_1404934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601317271630360514669433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34161435128114357646281237 1601317271630360514669433)
  ·
    refine ⟨1200987953722770386002075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1601317271630360514669433 1200987953722770386002075)
    ·
      refine ⟨1801481930584155579003113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200987953722770386002075 1801481930584155579003113)
      ·
        refine ⟨1351111447938116684252335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1801481930584155579003113 1351111447938116684252335)
        ·
          refine ⟨2026667171907175026378503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351111447938116684252335 2026667171907175026378503)
          ·
            refine ⟨3040000757860762539567755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2026667171907175026378503 3040000757860762539567755)
            ·
              refine ⟨4560001136791143809351633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040000757860762539567755 4560001136791143809351633)
              ·
                refine ⟨3420000852593357857013725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4560001136791143809351633 3420000852593357857013725)
                ·
                  refine ⟨1282500319722509196380147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3420000852593357857013725 1282500319722509196380147)
                  ·
                    refine ⟨1923750479583763794570221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1282500319722509196380147 1923750479583763794570221)
                    ·
                      refine ⟨721406429843911422963833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1923750479583763794570221 721406429843911422963833)
                      ·
                        rfl

theorem cell23_1404934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1404934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404934 prefixEnd_1404934 := by exact prefixLift 1404934
  have htrace : WordTrace (prefixWord ++ tailWord_1404934) baseStart_1404934 baseEnd_1404934 := by
    simpa [prefixWord, tailWord_1404934, baseEnd_1404934] using wordTrace_append hprefix tailTrace_1404934
  have hstable : (prefixWord ++ tailWord_1404934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404934).length < 2 ^ (prefixWord ++ tailWord_1404934).sum := by decide
  have hdescent : baseEnd_1404934 < baseStart_1404934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404956 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1404956 : Nat := 118140960795 + 1404956 * 2 ^ 59
def prefixEnd_1404956 : Nat := 4983230072969 + 3 ^ 40 * 1404956 * 2
def baseEnd_1404956 : Nat := 721417726418310336888731

theorem tailTrace_1404956 : CollatzResearch.WordTrace tailWord_1404956 prefixEnd_1404956 721417726418310336888731 := by
  unfold tailWord_1404956
  simp only [CollatzResearch.WordTrace]
  refine ⟨25621477549045917113361361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34161970065394556151148481 25621477549045917113361361)
  ·
    refine ⟨19216108161784437835021021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25621477549045917113361361 19216108161784437835021021)
    ·
      refine ⟨7206040560669164188132883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19216108161784437835021021 7206040560669164188132883)
      ·
        refine ⟨10809060841003746282199325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7206040560669164188132883 10809060841003746282199325)
        ·
          refine ⟨4053397815376404855824747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10809060841003746282199325 4053397815376404855824747)
          ·
            refine ⟨6080096723064607283737121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053397815376404855824747 6080096723064607283737121)
            ·
              refine ⟨4560072542298455462802841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6080096723064607283737121 4560072542298455462802841)
              ·
                refine ⟨3420054406723841597102131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4560072542298455462802841 3420054406723841597102131)
                ·
                  refine ⟨5130081610085762395653197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3420054406723841597102131 5130081610085762395653197)
                  ·
                    refine ⟨1923780603782160898369949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5130081610085762395653197 1923780603782160898369949)
                    ·
                      refine ⟨721417726418310336888731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1923780603782160898369949 721417726418310336888731)
                      ·
                        rfl

theorem cell23_1404956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1404956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404956 prefixEnd_1404956 := by exact prefixLift 1404956
  have htrace : WordTrace (prefixWord ++ tailWord_1404956) baseStart_1404956 baseEnd_1404956 := by
    simpa [prefixWord, tailWord_1404956, baseEnd_1404956] using wordTrace_append hprefix tailTrace_1404956
  have hstable : (prefixWord ++ tailWord_1404956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404956).length < 2 ^ (prefixWord ++ tailWord_1404956).sum := by decide
  have hdescent : baseEnd_1404956 < baseStart_1404956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404957 : List Nat := [1, 4, 2, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_1404957 : Nat := 118140960795 + 1404957 * 2 ^ 59
def prefixEnd_1404957 : Nat := 4983230072969 + 3 ^ 40 * 1404957 * 2
def baseEnd_1404957 : Nat := 721418239898964832976227

theorem tailTrace_1404957 : CollatzResearch.WordTrace tailWord_1404957 prefixEnd_1404957 721418239898964832976227 := by
  unfold tailWord_1404957
  simp only [CollatzResearch.WordTrace]
  refine ⟨51242991571088211397509125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34161994380725474265006083 51242991571088211397509125)
  ·
    refine ⟨9608060919579039637032961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51242991571088211397509125 9608060919579039637032961)
    ·
      refine ⟨7206045689684279727774721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9608060919579039637032961 7206045689684279727774721)
      ·
        refine ⟨5404534267263209795831041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7206045689684279727774721 5404534267263209795831041)
        ·
          refine ⟨4053400700447407346873281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5404534267263209795831041 4053400700447407346873281)
          ·
            refine ⟨3040050525335555510154961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4053400700447407346873281 3040050525335555510154961)
            ·
              refine ⟨2280037894001666632616221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040050525335555510154961 2280037894001666632616221)
              ·
                refine ⟨855014210250624987231083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2280037894001666632616221 855014210250624987231083)
                ·
                  refine ⟨1282521315375937480846625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855014210250624987231083 1282521315375937480846625)
                  ·
                    refine ⟨961890986531953110634969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1282521315375937480846625 961890986531953110634969)
                    ·
                      refine ⟨721418239898964832976227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 961890986531953110634969 721418239898964832976227)
                      ·
                        rfl

theorem cell23_1404957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_1404957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404957 prefixEnd_1404957 := by exact prefixLift 1404957
  have htrace : WordTrace (prefixWord ++ tailWord_1404957) baseStart_1404957 baseEnd_1404957 := by
    simpa [prefixWord, tailWord_1404957, baseEnd_1404957] using wordTrace_append hprefix tailTrace_1404957
  have hstable : (prefixWord ++ tailWord_1404957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404957).length < 2 ^ (prefixWord ++ tailWord_1404957).sum := by decide
  have hdescent : baseEnd_1404957 < baseStart_1404957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404967 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1404967 : Nat := 118140960795 + 1404967 * 2 ^ 59
def prefixEnd_1404967 : Nat := 4983230072969 + 3 ^ 40 * 1404967 * 2
def baseEnd_1404967 : Nat := 240474458235169931283727

theorem tailTrace_1404967 : CollatzResearch.WordTrace tailWord_1404967 prefixEnd_1404967 240474458235169931283727 := by
  unfold tailWord_1404967
  simp only [CollatzResearch.WordTrace]
  refine ⟨51243356301051983105373155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34162237534034655403582103 51243356301051983105373155)
  ·
    refine ⟨76865034451577974658059733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51243356301051983105373155 76865034451577974658059733)
    ·
      refine ⟨1801524244958858781048275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 76865034451577974658059733 1801524244958858781048275)
      ·
        refine ⟨2702286367438288171572413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801524244958858781048275 2702286367438288171572413)
        ·
          refine ⟨1013357387789358064339655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2702286367438288171572413 1013357387789358064339655)
          ·
            refine ⟨1520036081684037096509483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013357387789358064339655 1520036081684037096509483)
            ·
              refine ⟨2280054122526055644764225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520036081684037096509483 2280054122526055644764225)
              ·
                refine ⟨1710040591894541733573169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280054122526055644764225 1710040591894541733573169)
                ·
                  refine ⟨1282530443920906300179877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710040591894541733573169 1282530443920906300179877)
                  ·
                    refine ⟨240474458235169931283727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282530443920906300179877 240474458235169931283727)
                    ·
                      rfl

theorem cell23_1404967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1404967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404967 prefixEnd_1404967 := by exact prefixLift 1404967
  have htrace : WordTrace (prefixWord ++ tailWord_1404967) baseStart_1404967 baseEnd_1404967 := by
    simpa [prefixWord, tailWord_1404967, baseEnd_1404967] using wordTrace_append hprefix tailTrace_1404967
  have hstable : (prefixWord ++ tailWord_1404967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404967).length < 2 ^ (prefixWord ++ tailWord_1404967).sum := by decide
  have hdescent : baseEnd_1404967 < baseStart_1404967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404989 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_1404989 : Nat := 118140960795 + 1404989 * 2 ^ 59
def prefixEnd_1404989 : Nat := 4983230072969 + 3 ^ 40 * 1404989 * 2
def baseEnd_1404989 : Nat := 240478223759969569258693

theorem tailTrace_1404989 : CollatzResearch.WordTrace tailWord_1404989 prefixEnd_1404989 240478223759969569258693 := by
  unfold tailWord_1404989
  simp only [CollatzResearch.WordTrace]
  refine ⟨51244158706972280862674021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34162772471314853908449347 51244158706972280862674021)
  ·
    refine ⟨9608279757557302661751379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51244158706972280862674021 9608279757557302661751379)
    ·
      refine ⟨14412419636335953992627069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9608279757557302661751379 14412419636335953992627069)
      ·
        refine ⟨5404657363625982747235151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14412419636335953992627069 5404657363625982747235151)
        ·
          refine ⟨8106986045438974120852727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404657363625982747235151 8106986045438974120852727)
          ·
            refine ⟨12160479068158461181279091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8106986045438974120852727 12160479068158461181279091)
            ·
              refine ⟨18240718602237691771918637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12160479068158461181279091 18240718602237691771918637)
              ·
                refine ⟨6840269475839134414469489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18240718602237691771918637 6840269475839134414469489)
                ·
                  refine ⟨5130202106879350810852117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6840269475839134414469489 5130202106879350810852117)
                  ·
                    refine ⟨240478223759969569258693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5130202106879350810852117 240478223759969569258693)
                    ·
                      rfl

theorem cell23_1404989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_1404989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404989 prefixEnd_1404989 := by exact prefixLift 1404989
  have htrace : WordTrace (prefixWord ++ tailWord_1404989) baseStart_1404989 baseEnd_1404989 := by
    simpa [prefixWord, tailWord_1404989, baseEnd_1404989] using wordTrace_append hprefix tailTrace_1404989
  have hstable : (prefixWord ++ tailWord_1404989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404989).length < 2 ^ (prefixWord ++ tailWord_1404989).sum := by decide
  have hdescent : baseEnd_1404989 < baseStart_1404989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404990 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1404990 : Nat := 118140960795 + 1404990 * 2 ^ 59
def prefixEnd_1404990 : Nat := 4983230072969 + 3 ^ 40 * 1404990 * 2
def baseEnd_1404990 : Nat := 721435184760563203863575

theorem tailTrace_1404990 : CollatzResearch.WordTrace tailWord_1404990 prefixEnd_1404990 721435184760563203863575 := by
  unfold tailWord_1404990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6405524397496082254182553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34162796786645772022306949 6405524397496082254182553)
  ·
    refine ⟨4804143298122061690636915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6405524397496082254182553 4804143298122061690636915)
    ·
      refine ⟨7206214947183092535955373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4804143298122061690636915 7206214947183092535955373)
      ·
        refine ⟨2702330605193659700983265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7206214947183092535955373 2702330605193659700983265)
        ·
          refine ⟨2026747953895244775737449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2702330605193659700983265 2026747953895244775737449)
          ·
            refine ⟨1520060965421433581803087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2026747953895244775737449 1520060965421433581803087)
            ·
              refine ⟨2280091448132150372704631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520060965421433581803087 2280091448132150372704631)
              ·
                refine ⟨3420137172198225559056947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280091448132150372704631 3420137172198225559056947)
                ·
                  refine ⟨5130205758297338338585421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3420137172198225559056947 5130205758297338338585421)
                  ·
                    refine ⟨1923827159361501876969533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5130205758297338338585421 1923827159361501876969533)
                    ·
                      refine ⟨721435184760563203863575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1923827159361501876969533 721435184760563203863575)
                      ·
                        rfl

theorem cell23_1404990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1404990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404990 prefixEnd_1404990 := by exact prefixLift 1404990
  have htrace : WordTrace (prefixWord ++ tailWord_1404990) baseStart_1404990 baseEnd_1404990 := by
    simpa [prefixWord, tailWord_1404990, baseEnd_1404990] using wordTrace_append hprefix tailTrace_1404990
  have hstable : (prefixWord ++ tailWord_1404990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404990).length < 2 ^ (prefixWord ++ tailWord_1404990).sum := by decide
  have hdescent : baseEnd_1404990 < baseStart_1404990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1404999 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1404999 : Nat := 118140960795 + 1404999 * 2 ^ 59
def prefixEnd_1404999 : Nat := 4983230072969 + 3 ^ 40 * 1404999 * 2
def baseEnd_1404999 : Nat := 721439806086453668651033

theorem tailTrace_1404999 : CollatzResearch.WordTrace tailWord_1404999 prefixEnd_1404999 721439806086453668651033 := by
  unfold tailWord_1404999
  simp only [CollatzResearch.WordTrace]
  refine ⟨51244523436936052570538051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34163015624624035047025367 51244523436936052570538051)
  ·
    refine ⟨76866785155404078855807077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51244523436936052570538051 76866785155404078855807077)
    ·
      refine ⟨14412522216638264785463827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76866785155404078855807077 14412522216638264785463827)
      ·
        refine ⟨21618783324957397178195741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14412522216638264785463827 21618783324957397178195741)
        ·
          refine ⟨8107043746859023941823403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21618783324957397178195741 8107043746859023941823403)
          ·
            refine ⟨12160565620288535912735105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107043746859023941823403 12160565620288535912735105)
            ·
              refine ⟨9120424215216401934551329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12160565620288535912735105 9120424215216401934551329)
              ·
                refine ⟨6840318161412301450913497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9120424215216401934551329 6840318161412301450913497)
                ·
                  refine ⟨5130238621059226088185123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6840318161412301450913497 5130238621059226088185123)
                  ·
                    refine ⟨7695357931588839132277685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5130238621059226088185123 7695357931588839132277685)
                    ·
                      refine ⟨721439806086453668651033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7695357931588839132277685 721439806086453668651033)
                      ·
                        rfl

theorem cell23_1404999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1404999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1404999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1404999 prefixEnd_1404999 := by exact prefixLift 1404999
  have htrace : WordTrace (prefixWord ++ tailWord_1404999) baseStart_1404999 baseEnd_1404999 := by
    simpa [prefixWord, tailWord_1404999, baseEnd_1404999] using wordTrace_append hprefix tailTrace_1404999
  have hstable : (prefixWord ++ tailWord_1404999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1404999).length < 2 ^ (prefixWord ++ tailWord_1404999).sum := by decide
  have hdescent : baseEnd_1404999 < baseStart_1404999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1404999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405013 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_1405013 : Nat := 118140960795 + 1405013 * 2 ^ 59
def prefixEnd_1405013 : Nat := 4983230072969 + 3 ^ 40 * 1405013 * 2
def baseEnd_1405013 : Nat := 721446994815616613875969

theorem tailTrace_1405013 : CollatzResearch.WordTrace tailWord_1405013 prefixEnd_1405013 721446994815616613875969 := by
  unfold tailWord_1405013
  simp only [CollatzResearch.WordTrace]
  refine ⟨51245034058885332961547693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34163356039256888641031795 51245034058885332961547693)
  ·
    refine ⟨19216887772081999860580385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51245034058885332961547693 19216887772081999860580385)
    ·
      refine ⟨14412665829061499895435289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19216887772081999860580385 14412665829061499895435289)
      ·
        refine ⟨10809499371796124921576467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14412665829061499895435289 10809499371796124921576467)
        ·
          refine ⟨16214249057694187382364701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10809499371796124921576467 16214249057694187382364701)
          ·
            refine ⟨6080343396635320268386763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16214249057694187382364701 6080343396635320268386763)
            ·
              refine ⟨9120515094952980402580145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080343396635320268386763 9120515094952980402580145)
              ·
                refine ⟨6840386321214735301935109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9120515094952980402580145 6840386321214735301935109)
                ·
                  refine ⟨1282572435227762869112833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6840386321214735301935109 1282572435227762869112833)
                  ·
                    refine ⟨961929326420822151834625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1282572435227762869112833 961929326420822151834625)
                    ·
                      refine ⟨721446994815616613875969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 961929326420822151834625 721446994815616613875969)
                      ·
                        rfl

theorem cell23_1405013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_1405013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405013 prefixEnd_1405013 := by exact prefixLift 1405013
  have htrace : WordTrace (prefixWord ++ tailWord_1405013) baseStart_1405013 baseEnd_1405013 := by
    simpa [prefixWord, tailWord_1405013, baseEnd_1405013] using wordTrace_append hprefix tailTrace_1405013
  have hstable : (prefixWord ++ tailWord_1405013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405013).length < 2 ^ (prefixWord ++ tailWord_1405013).sum := by decide
  have hdescent : baseEnd_1405013 < baseStart_1405013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405036 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 7]
def baseStart_1405036 : Nat := 118140960795 + 1405036 * 2 ^ 59
def prefixEnd_1405036 : Nat := 4983230072969 + 3 ^ 40 * 1405036 * 2
def baseEnd_1405036 : Nat := 80162089430074447098707

theorem tailTrace_1405036 : CollatzResearch.WordTrace tailWord_1405036 prefixEnd_1405036 80162089430074447098707 := by
  unfold tailWord_1405036
  simp only [CollatzResearch.WordTrace]
  refine ⟨25622936468901003944817481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34163915291868005259756641 25622936468901003944817481)
  ·
    refine ⟨19217202351675752958613111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25622936468901003944817481 19217202351675752958613111)
    ·
      refine ⟨28825803527513629437919667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19217202351675752958613111 28825803527513629437919667)
      ·
        refine ⟨43238705291270444156879501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28825803527513629437919667 43238705291270444156879501)
        ·
          refine ⟨16214514484226416558829813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43238705291270444156879501 16214514484226416558829813)
          ·
            refine ⟨1520110732896226552390295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16214514484226416558829813 1520110732896226552390295)
            ·
              refine ⟨2280166099344339828585443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520110732896226552390295 2280166099344339828585443)
              ·
                refine ⟨3420249149016509742878165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280166099344339828585443 3420249149016509742878165)
                ·
                  refine ⟨80162089430074447098707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3420249149016509742878165 80162089430074447098707)
                  ·
                    rfl

theorem cell23_1405036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_1405036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405036 prefixEnd_1405036 := by exact prefixLift 1405036
  have htrace : WordTrace (prefixWord ++ tailWord_1405036) baseStart_1405036 baseEnd_1405036 := by
    simpa [prefixWord, tailWord_1405036, baseEnd_1405036] using wordTrace_append hprefix tailTrace_1405036
  have hstable : (prefixWord ++ tailWord_1405036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405036).length < 2 ^ (prefixWord ++ tailWord_1405036).sum := by decide
  have hdescent : baseEnd_1405036 < baseStart_1405036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405047 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 2, 2, 2]
def baseStart_1405047 : Nat := 118140960795 + 1405047 * 2 ^ 59
def prefixEnd_1405047 : Nat := 4983230072969 + 3 ^ 40 * 1405047 * 2
def baseEnd_1405047 : Nat := 721464453157869480850813

theorem tailTrace_1405047 : CollatzResearch.WordTrace tailWord_1405047 prefixEnd_1405047 721464453157869480850813 := by
  unfold tailWord_1405047
  simp only [CollatzResearch.WordTrace]
  refine ⟨51246274140762156768285395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34164182760508104512190263 51246274140762156768285395)
  ·
    refine ⟨76869411211143235152428093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51246274140762156768285395 76869411211143235152428093)
    ·
      refine ⟨28826029204178713182160535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76869411211143235152428093 28826029204178713182160535)
      ·
        refine ⟨43239043806268069773240803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28826029204178713182160535 43239043806268069773240803)
        ·
          refine ⟨64858565709402104659861205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43239043806268069773240803 64858565709402104659861205)
          ·
            refine ⟨1520122633814111827965497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 64858565709402104659861205 1520122633814111827965497)
            ·
              refine ⟨1140091975360583870974123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520122633814111827965497 1140091975360583870974123)
              ·
                refine ⟨1710137963040875806461185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140091975360583870974123 1710137963040875806461185)
                ·
                  refine ⟨1282603472280656854845889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710137963040875806461185 1282603472280656854845889)
                  ·
                    refine ⟨961952604210492641134417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1282603472280656854845889 961952604210492641134417)
                    ·
                      refine ⟨721464453157869480850813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 961952604210492641134417 721464453157869480850813)
                      ·
                        rfl

theorem cell23_1405047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_1405047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405047 prefixEnd_1405047 := by exact prefixLift 1405047
  have htrace : WordTrace (prefixWord ++ tailWord_1405047) baseStart_1405047 baseEnd_1405047 := by
    simpa [prefixWord, tailWord_1405047, baseEnd_1405047] using wordTrace_append hprefix tailTrace_1405047
  have hstable : (prefixWord ++ tailWord_1405047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405047).length < 2 ^ (prefixWord ++ tailWord_1405047).sum := by decide
  have hdescent : baseEnd_1405047 < baseStart_1405047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405066 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 2, 5]
def baseStart_1405066 : Nat := 118140960795 + 1405066 * 2 ^ 59
def prefixEnd_1405066 : Nat := 4983230072969 + 3 ^ 40 * 1405066 * 2
def baseEnd_1405066 : Nat := 240491403096768302171075

theorem tailTrace_1405066 : CollatzResearch.WordTrace tailWord_1405066 prefixEnd_1405066 240491403096768302171075 := by
  unfold tailWord_1405066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12811741781923330753306763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34164644751795548675484701 12811741781923330753306763)
  ·
    refine ⟨19217612672884996129960145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12811741781923330753306763 19217612672884996129960145)
    ·
      refine ⟨14413209504663747097470109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19217612672884996129960145 14413209504663747097470109)
      ·
        refine ⟨5404953564248905161551291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14413209504663747097470109 5404953564248905161551291)
        ·
          refine ⟨8107430346373357742326937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5404953564248905161551291 8107430346373357742326937)
          ·
            refine ⟨6080572759780018306745203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8107430346373357742326937 6080572759780018306745203)
            ·
              refine ⟨9120859139670027460117805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6080572759780018306745203 9120859139670027460117805)
              ·
                refine ⟨3420322177376260297544177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9120859139670027460117805 3420322177376260297544177)
                ·
                  refine ⟨2565241633032195223158133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3420322177376260297544177 2565241633032195223158133)
                  ·
                    refine ⟨240491403096768302171075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2565241633032195223158133 240491403096768302171075)
                    ·
                      rfl

theorem cell23_1405066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_1405066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405066 prefixEnd_1405066 := by exact prefixLift 1405066
  have htrace : WordTrace (prefixWord ++ tailWord_1405066) baseStart_1405066 baseEnd_1405066 := by
    simpa [prefixWord, tailWord_1405066, baseEnd_1405066] using wordTrace_append hprefix tailTrace_1405066
  have hstable : (prefixWord ++ tailWord_1405066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405066).length < 2 ^ (prefixWord ++ tailWord_1405066).sum := by decide
  have hdescent : baseEnd_1405066 < baseStart_1405066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405106 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_1405106 : Nat := 118140960795 + 1405106 * 2 ^ 59
def prefixEnd_1405106 : Nat := 4983230072969 + 3 ^ 40 * 1405106 * 2
def baseEnd_1405106 : Nat := 721494748516484750013041

theorem tailTrace_1405106 : CollatzResearch.WordTrace tailWord_1405106 prefixEnd_1405106 721494748516484750013041 := by
  unfold tailWord_1405106
  simp only [CollatzResearch.WordTrace]
  refine ⟨12812106511887102461170793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34165617365032273229788781 12812106511887102461170793)
  ·
    refine ⟨9609079883915326845878095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12812106511887102461170793 9609079883915326845878095)
    ·
      refine ⟨14413619825872990268817143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9609079883915326845878095 14413619825872990268817143)
      ·
        refine ⟨21620429738809485403225715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14413619825872990268817143 21620429738809485403225715)
        ·
          refine ⟨32430644608214228104838573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21620429738809485403225715 32430644608214228104838573)
          ·
            refine ⟨12161491728080335539314465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32430644608214228104838573 12161491728080335539314465)
            ·
              refine ⟨9121118796060251654485849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12161491728080335539314465 9121118796060251654485849)
              ·
                refine ⟨6840839097045188740864387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9121118796060251654485849 6840839097045188740864387)
                ·
                  refine ⟨10261258645567783111296581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6840839097045188740864387 10261258645567783111296581)
                  ·
                    refine ⟨1923985996043959333368109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10261258645567783111296581 1923985996043959333368109)
                    ·
                      refine ⟨721494748516484750013041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1923985996043959333368109 721494748516484750013041)
                      ·
                        rfl

theorem cell23_1405106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_1405106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405106 prefixEnd_1405106 := by exact prefixLift 1405106
  have htrace : WordTrace (prefixWord ++ tailWord_1405106) baseStart_1405106 baseEnd_1405106 := by
    simpa [prefixWord, tailWord_1405106, baseEnd_1405106] using wordTrace_append hprefix tailTrace_1405106
  have hstable : (prefixWord ++ tailWord_1405106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405106).length < 2 ^ (prefixWord ++ tailWord_1405106).sum := by decide
  have hdescent : baseEnd_1405106 < baseStart_1405106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405130 : List Nat := [3, 1, 2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_1405130 : Nat := 118140960795 + 1405130 * 2 ^ 59
def prefixEnd_1405130 : Nat := 4983230072969 + 3 ^ 40 * 1405130 * 2
def baseEnd_1405130 : Nat := 240502357350730885370977

theorem tailTrace_1405130 : CollatzResearch.WordTrace tailWord_1405130 prefixEnd_1405130 240502357350730885370977 := by
  unfold tailWord_1405130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12812325349865365485889211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34166200932974307962371229 12812325349865365485889211)
  ·
    refine ⟨19218488024798048228833817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12812325349865365485889211 19218488024798048228833817)
    ·
      refine ⟨14413866018598536171625363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19218488024798048228833817 14413866018598536171625363)
      ·
        refine ⟨21620799027897804257438045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14413866018598536171625363 21620799027897804257438045)
        ·
          refine ⟨8107799635461676596539267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21620799027897804257438045 8107799635461676596539267)
          ·
            refine ⟨12161699453192514894808901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8107799635461676596539267 12161699453192514894808901)
            ·
              refine ⟨2280318647473596542776669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12161699453192514894808901 2280318647473596542776669)
              ·
                refine ⟨855119492802598703541251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2280318647473596542776669 855119492802598703541251)
                ·
                  refine ⟨1282679239203898055311877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855119492802598703541251 1282679239203898055311877)
                  ·
                    refine ⟨240502357350730885370977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282679239203898055311877 240502357350730885370977)
                    ·
                      rfl

theorem cell23_1405130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_1405130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405130 prefixEnd_1405130 := by exact prefixLift 1405130
  have htrace : WordTrace (prefixWord ++ tailWord_1405130) baseStart_1405130 baseEnd_1405130 := by
    simpa [prefixWord, tailWord_1405130, baseEnd_1405130] using wordTrace_append hprefix tailTrace_1405130
  have hstable : (prefixWord ++ tailWord_1405130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405130).length < 2 ^ (prefixWord ++ tailWord_1405130).sum := by decide
  have hdescent : baseEnd_1405130 < baseStart_1405130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405170 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_1405170 : Nat := 118140960795 + 1405170 * 2 ^ 59
def prefixEnd_1405170 : Nat := 4983230072969 + 3 ^ 40 * 1405170 * 2
def baseEnd_1405170 : Nat := 721527611278372499612747

theorem tailTrace_1405170 : CollatzResearch.WordTrace tailWord_1405170 prefixEnd_1405170 721527611278372499612747 := by
  unfold tailWord_1405170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12812690079829137193753241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34167173546211032516675309 12812690079829137193753241)
  ·
    refine ⟨9609517559871852895314931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12812690079829137193753241 9609517559871852895314931)
    ·
      refine ⟨14414276339807779342972397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9609517559871852895314931 14414276339807779342972397)
      ·
        refine ⟨5405353627427917253614649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14414276339807779342972397 5405353627427917253614649)
        ·
          refine ⟨4054015220570937940210987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5405353627427917253614649 4054015220570937940210987)
          ·
            refine ⟨6081022830856406910316481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054015220570937940210987 6081022830856406910316481)
            ·
              refine ⟨4560767123142305182737361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6081022830856406910316481 4560767123142305182737361)
              ·
                refine ⟨3420575342356728887053021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4560767123142305182737361 3420575342356728887053021)
                ·
                  refine ⟨1282715753383773332644883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3420575342356728887053021 1282715753383773332644883)
                  ·
                    refine ⟨1924073630075659998967325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1282715753383773332644883 1924073630075659998967325)
                    ·
                      refine ⟨721527611278372499612747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1924073630075659998967325 721527611278372499612747)
                      ·
                        rfl

theorem cell23_1405170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_1405170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405170 prefixEnd_1405170 := by exact prefixLift 1405170
  have htrace : WordTrace (prefixWord ++ tailWord_1405170) baseStart_1405170 baseEnd_1405170 := by
    simpa [prefixWord, tailWord_1405170, baseEnd_1405170] using wordTrace_append hprefix tailTrace_1405170
  have hstable : (prefixWord ++ tailWord_1405170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405170).length < 2 ^ (prefixWord ++ tailWord_1405170).sum := by decide
  have hdescent : baseEnd_1405170 < baseStart_1405170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405176 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_1405176 : Nat := 118140960795 + 1405176 * 2 ^ 59
def prefixEnd_1405176 : Nat := 4983230072969 + 3 ^ 40 * 1405176 * 2
def baseEnd_1405176 : Nat := 721530692162299476137719

theorem tailTrace_1405176 : CollatzResearch.WordTrace tailWord_1405176 prefixEnd_1405176 721530692162299476137719 := by
  unfold tailWord_1405176
  simp only [CollatzResearch.WordTrace]
  refine ⟨25625489578647405899865691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34167319438196541199820921 25625489578647405899865691)
  ·
    refine ⟨38438234367971108849798537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25625489578647405899865691 38438234367971108849798537)
    ·
      refine ⟨28828675775978331637348903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38438234367971108849798537 28828675775978331637348903)
      ·
        refine ⟨43243013663967497456023355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28828675775978331637348903 43243013663967497456023355)
        ·
          refine ⟨64864520495951246184035033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43243013663967497456023355 64864520495951246184035033)
          ·
            refine ⟨48648390371963434638026275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64864520495951246184035033 48648390371963434638026275)
            ·
              refine ⟨72972585557945151957039413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48648390371963434638026275 72972585557945151957039413)
              ·
                refine ⟨6841179896057357995972445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72972585557945151957039413 6841179896057357995972445)
                ·
                  refine ⟨2565442461021509248489667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6841179896057357995972445 2565442461021509248489667)
                  ·
                    refine ⟨3848163691532263872734501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2565442461021509248489667 3848163691532263872734501)
                    ·
                      refine ⟨721530692162299476137719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3848163691532263872734501 721530692162299476137719)
                      ·
                        rfl

theorem cell23_1405176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_1405176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405176 prefixEnd_1405176 := by exact prefixLift 1405176
  have htrace : WordTrace (prefixWord ++ tailWord_1405176) baseStart_1405176 baseEnd_1405176 := by
    simpa [prefixWord, tailWord_1405176, baseEnd_1405176] using wordTrace_append hprefix tailTrace_1405176
  have hstable : (prefixWord ++ tailWord_1405176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405176).length < 2 ^ (prefixWord ++ tailWord_1405176).sum := by decide
  have hdescent : baseEnd_1405176 < baseStart_1405176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405193 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 4]
def baseStart_1405193 : Nat := 118140960795 + 1405193 * 2 ^ 59
def prefixEnd_1405193 : Nat := 4983230072969 + 3 ^ 40 * 1405193 * 2
def baseEnd_1405193 : Nat := 721539421333425909625141

theorem tailTrace_1405193 : CollatzResearch.WordTrace tailWord_1405193 prefixEnd_1405193 721539421333425909625141 := by
  unfold tailWord_1405193
  simp only [CollatzResearch.WordTrace]
  refine ⟨51251599198233223703100233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34167732798822149135400155 51251599198233223703100233)
  ·
    refine ⟨38438699398674917777325175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51251599198233223703100233 38438699398674917777325175)
    ·
      refine ⟨57658049098012376665987763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38438699398674917777325175 57658049098012376665987763)
      ·
        refine ⟨86487073647018564998981645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57658049098012376665987763 86487073647018564998981645)
        ·
          refine ⟨32432652617631961874618117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86487073647018564998981645 32432652617631961874618117)
          ·
            refine ⟨6081122365805992851490897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32432652617631961874618117 6081122365805992851490897)
            ·
              refine ⟨4560841774354494638618173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6081122365805992851490897 4560841774354494638618173)
              ·
                refine ⟨1710315665382935489481815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4560841774354494638618173 1710315665382935489481815)
                ·
                  refine ⟨2565473498074403234222723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710315665382935489481815 2565473498074403234222723)
                  ·
                    refine ⟨3848210247111604851334085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2565473498074403234222723 3848210247111604851334085)
                    ·
                      refine ⟨721539421333425909625141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3848210247111604851334085 721539421333425909625141)
                      ·
                        rfl

theorem cell23_1405193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 4].length) (baseStart_1405193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405193 prefixEnd_1405193 := by exact prefixLift 1405193
  have htrace : WordTrace (prefixWord ++ tailWord_1405193) baseStart_1405193 baseEnd_1405193 := by
    simpa [prefixWord, tailWord_1405193, baseEnd_1405193] using wordTrace_append hprefix tailTrace_1405193
  have hstable : (prefixWord ++ tailWord_1405193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405193).length < 2 ^ (prefixWord ++ tailWord_1405193).sum := by decide
  have hdescent : baseEnd_1405193 < baseStart_1405193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405216 : List Nat := [2, 1, 1, 5, 2, 1, 1, 10]
def baseStart_1405216 : Nat := 118140960795 + 1405216 * 2 ^ 59
def prefixEnd_1405216 : Nat := 4983230072969 + 3 ^ 40 * 1405216 * 2
def baseEnd_1405216 : Nat := 26724119681054789616205

theorem tailTrace_1405216 : CollatzResearch.WordTrace tailWord_1405216 prefixEnd_1405216 26724119681054789616205 := by
  unfold tailWord_1405216
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626219038574949315593751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34168292051433265754125001 25626219038574949315593751)
  ·
    refine ⟨38439328557862423973390627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25626219038574949315593751 38439328557862423973390627)
    ·
      refine ⟨57658992836793635960085941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38439328557862423973390627 57658992836793635960085941)
      ·
        refine ⟨5405530578449403371258057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57658992836793635960085941 5405530578449403371258057)
        ·
          refine ⟨4054147933837052528443543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5405530578449403371258057 4054147933837052528443543)
          ·
            refine ⟨6081221900755578792665315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054147933837052528443543 6081221900755578792665315)
            ·
              refine ⟨9121832851133368188997973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6081221900755578792665315 9121832851133368188997973)
              ·
                refine ⟨26724119681054789616205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9121832851133368188997973 26724119681054789616205)
                ·
                  rfl

theorem cell23_1405216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 10].length) (baseStart_1405216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405216 prefixEnd_1405216 := by exact prefixLift 1405216
  have htrace : WordTrace (prefixWord ++ tailWord_1405216) baseStart_1405216 baseEnd_1405216 := by
    simpa [prefixWord, tailWord_1405216, baseEnd_1405216] using wordTrace_append hprefix tailTrace_1405216
  have hstable : (prefixWord ++ tailWord_1405216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405216).length < 2 ^ (prefixWord ++ tailWord_1405216).sum := by decide
  have hdescent : baseEnd_1405216 < baseStart_1405216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405220 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_1405220 : Nat := 118140960795 + 1405220 * 2 ^ 59
def prefixEnd_1405220 : Nat := 4983230072969 + 3 ^ 40 * 1405220 * 2
def baseEnd_1405220 : Nat := 240517761770365767995839

theorem tailTrace_1405220 : CollatzResearch.WordTrace tailWord_1405220 prefixEnd_1405220 240517761770365767995839 := by
  unfold tailWord_1405220
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626291984567703657166557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34168389312756938209555409 25626291984567703657166557)
  ·
    refine ⟨9609859494212888871437459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25626291984567703657166557 9609859494212888871437459)
    ·
      refine ⟨14414789241319333307156189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9609859494212888871437459 14414789241319333307156189)
      ·
        refine ⟨5405545965494749990183571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14414789241319333307156189 5405545965494749990183571)
        ·
          refine ⟨8108318948242124985275357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5405545965494749990183571 8108318948242124985275357)
          ·
            refine ⟨3040619605590796869478259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8108318948242124985275357 3040619605590796869478259)
            ·
              refine ⟨4560929408386195304217389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040619605590796869478259 4560929408386195304217389)
              ·
                refine ⟨1710348528144823239081521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4560929408386195304217389 1710348528144823239081521)
                ·
                  refine ⟨1282761396108617429311141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710348528144823239081521 1282761396108617429311141)
                  ·
                    refine ⟨240517761770365767995839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1282761396108617429311141 240517761770365767995839)
                    ·
                      rfl

theorem cell23_1405220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_1405220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405220 prefixEnd_1405220 := by exact prefixLift 1405220
  have htrace : WordTrace (prefixWord ++ tailWord_1405220) baseStart_1405220 baseEnd_1405220 := by
    simpa [prefixWord, tailWord_1405220, baseEnd_1405220] using wordTrace_append hprefix tailTrace_1405220
  have hstable : (prefixWord ++ tailWord_1405220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405220).length < 2 ^ (prefixWord ++ tailWord_1405220).sum := by decide
  have hdescent : baseEnd_1405220 < baseStart_1405220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405256 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_1405256 : Nat := 118140960795 + 1405256 * 2 ^ 59
def prefixEnd_1405256 : Nat := 4983230072969 + 3 ^ 40 * 1405256 * 2
def baseEnd_1405256 : Nat := 721571770614659163137351

theorem tailTrace_1405256 : CollatzResearch.WordTrace tailWord_1405256 prefixEnd_1405256 721571770614659163137351 := by
  unfold tailWord_1405256
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626948498502492731321811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34169264664669990308429081 25626948498502492731321811)
  ·
    refine ⟨38440422747753739096982717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25626948498502492731321811 38440422747753739096982717)
    ·
      refine ⟨14415158530407652161368519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38440422747753739096982717 14415158530407652161368519)
      ·
        refine ⟨21622737795611478242052779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14415158530407652161368519 21622737795611478242052779)
        ·
          refine ⟨32434106693417217363079169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21622737795611478242052779 32434106693417217363079169)
          ·
            refine ⟨24325580020062913022309377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32434106693417217363079169 24325580020062913022309377)
            ·
              refine ⟨18244185015047184766732033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24325580020062913022309377 18244185015047184766732033)
              ·
                refine ⟨13683138761285388575049025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18244185015047184766732033 13683138761285388575049025)
                ·
                  refine ⟨10262354070964041431286769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13683138761285388575049025 10262354070964041431286769)
                  ·
                    refine ⟨7696765553223031073465077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10262354070964041431286769 7696765553223031073465077)
                    ·
                      refine ⟨721571770614659163137351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7696765553223031073465077 721571770614659163137351)
                      ·
                        rfl

theorem cell23_1405256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_1405256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405256 prefixEnd_1405256 := by exact prefixLift 1405256
  have htrace : WordTrace (prefixWord ++ tailWord_1405256) baseStart_1405256 baseEnd_1405256 := by
    simpa [prefixWord, tailWord_1405256, baseEnd_1405256] using wordTrace_append hprefix tailTrace_1405256
  have hstable : (prefixWord ++ tailWord_1405256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405256).length < 2 ^ (prefixWord ++ tailWord_1405256).sum := by decide
  have hdescent : baseEnd_1405256 < baseStart_1405256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405323 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 7]
def baseStart_1405323 : Nat := 118140960795 + 1405323 * 2 ^ 59
def prefixEnd_1405323 : Nat := 4983230072969 + 3 ^ 40 * 1405323 * 2
def baseEnd_1405323 : Nat := 80178463757612266777727

theorem tailTrace_1405323 : CollatzResearch.WordTrace tailWord_1405323 prefixEnd_1405323 80178463757612266777727 := by
  unfold tailWord_1405323
  simp only [CollatzResearch.WordTrace]
  refine ⟨51256340687762255905332623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34170893791841503936888415 51256340687762255905332623)
  ·
    refine ⟨76884511031643383857998935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51256340687762255905332623 76884511031643383857998935)
    ·
      refine ⟨115326766547465075786998403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76884511031643383857998935 115326766547465075786998403)
      ·
        refine ⟨172990149821197613680497605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115326766547465075786998403 172990149821197613680497605)
        ·
          refine ⟨32435653091474552565093301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172990149821197613680497605 32435653091474552565093301)
          ·
            refine ⟨3040842477325739302977497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32435653091474552565093301 3040842477325739302977497)
            ·
              refine ⟨2280631857994304477233123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040842477325739302977497 2280631857994304477233123)
              ·
                refine ⟨3420947786991456715849685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280631857994304477233123 3420947786991456715849685)
                ·
                  refine ⟨80178463757612266777727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3420947786991456715849685 80178463757612266777727)
                  ·
                    rfl

theorem cell23_1405323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 7].length) (baseStart_1405323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405323 prefixEnd_1405323 := by exact prefixLift 1405323
  have htrace : WordTrace (prefixWord ++ tailWord_1405323) baseStart_1405323 baseEnd_1405323 := by
    simpa [prefixWord, tailWord_1405323, baseEnd_1405323] using wordTrace_append hprefix tailTrace_1405323
  have hstable : (prefixWord ++ tailWord_1405323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405323).length < 2 ^ (prefixWord ++ tailWord_1405323).sum := by decide
  have hdescent : baseEnd_1405323 < baseStart_1405323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405354 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1405354 : Nat := 118140960795 + 1405354 * 2 ^ 59
def prefixEnd_1405354 : Nat := 4983230072969 + 3 ^ 40 * 1405354 * 2
def baseEnd_1405354 : Nat := 721622091718799779711901

theorem tailTrace_1405354 : CollatzResearch.WordTrace tailWord_1405354 prefixEnd_1405354 721622091718799779711901 := by
  unfold tailWord_1405354
  simp only [CollatzResearch.WordTrace]
  refine ⟨12814367837662487049927779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34171647567099965466474077 12814367837662487049927779)
  ·
    refine ⟨19221551756493730574891669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12814367837662487049927779 19221551756493730574891669)
    ·
      refine ⟨901010238585643620698047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19221551756493730574891669 901010238585643620698047)
      ·
        refine ⟨1351515357878465431047071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901010238585643620698047 1351515357878465431047071)
        ·
          refine ⟨2027273036817698146570607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351515357878465431047071 2027273036817698146570607)
          ·
            refine ⟨3040909555226547219855911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027273036817698146570607 3040909555226547219855911)
            ·
              refine ⟨4561364332839820829783867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3040909555226547219855911 4561364332839820829783867)
              ·
                refine ⟨6842046499259731244675801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561364332839820829783867 6842046499259731244675801)
                ·
                  refine ⟨5131534874444798433506851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6842046499259731244675801 5131534874444798433506851)
                  ·
                    refine ⟨7697302311667197650260277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5131534874444798433506851 7697302311667197650260277)
                    ·
                      refine ⟨721622091718799779711901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7697302311667197650260277 721622091718799779711901)
                      ·
                        rfl

theorem cell23_1405354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1405354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405354 prefixEnd_1405354 := by exact prefixLift 1405354
  have htrace : WordTrace (prefixWord ++ tailWord_1405354) baseStart_1405354 baseEnd_1405354 := by
    simpa [prefixWord, tailWord_1405354, baseEnd_1405354] using wordTrace_append hprefix tailTrace_1405354
  have hstable : (prefixWord ++ tailWord_1405354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405354).length < 2 ^ (prefixWord ++ tailWord_1405354).sum := by decide
  have hdescent : baseEnd_1405354 < baseStart_1405354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405390 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_1405390 : Nat := 118140960795 + 1405390 * 2 ^ 59
def prefixEnd_1405390 : Nat := 4983230072969 + 3 ^ 40 * 1405390 * 2
def baseEnd_1405390 : Nat := 721640577022361638861735

theorem tailTrace_1405390 : CollatzResearch.WordTrace tailWord_1405390 prefixEnd_1405390 721640577022361638861735 := by
  unfold tailWord_1405390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6407348047314940793502703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34172522919013017565347749 6407348047314940793502703)
  ·
    refine ⟨9611022070972411190254055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6407348047314940793502703 9611022070972411190254055)
    ·
      refine ⟨14416533106458616785381083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9611022070972411190254055 14416533106458616785381083)
      ·
        refine ⟨21624799659687925178071625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14416533106458616785381083 21624799659687925178071625)
        ·
          refine ⟨16218599744765943883553719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21624799659687925178071625 16218599744765943883553719)
          ·
            refine ⟨24327899617148915825330579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16218599744765943883553719 24327899617148915825330579)
            ·
              refine ⟨36491849425723373737995869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24327899617148915825330579 36491849425723373737995869)
              ·
                refine ⟨13684443534646265151748451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36491849425723373737995869 13684443534646265151748451)
                ·
                  refine ⟨20526665301969397727622677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13684443534646265151748451 20526665301969397727622677)
                  ·
                    refine ⟨962187436029815518482313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20526665301969397727622677 962187436029815518482313)
                    ·
                      refine ⟨721640577022361638861735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962187436029815518482313 721640577022361638861735)
                      ·
                        rfl

theorem cell23_1405390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_1405390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405390 prefixEnd_1405390 := by exact prefixLift 1405390
  have htrace : WordTrace (prefixWord ++ tailWord_1405390) baseStart_1405390 baseEnd_1405390 := by
    simpa [prefixWord, tailWord_1405390, baseEnd_1405390] using wordTrace_append hprefix tailTrace_1405390
  have hstable : (prefixWord ++ tailWord_1405390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405390).length < 2 ^ (prefixWord ++ tailWord_1405390).sum := by decide
  have hdescent : baseEnd_1405390 < baseStart_1405390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405393 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_1405393 : Nat := 118140960795 + 1405393 * 2 ^ 59
def prefixEnd_1405393 : Nat := 4983230072969 + 3 ^ 40 * 1405393 * 2
def baseEnd_1405393 : Nat := 721642117464325127124221

theorem tailTrace_1405393 : CollatzResearch.WordTrace tailWord_1405393 prefixEnd_1405393 721642117464325127124221 := by
  unfold tailWord_1405393
  simp only [CollatzResearch.WordTrace]
  refine ⟨51258893797508657860380833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34172595865005771906920555 51258893797508657860380833)
  ·
    refine ⟨38444170348131493395285625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51258893797508657860380833 38444170348131493395285625)
    ·
      refine ⟨28833127761098620046464219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38444170348131493395285625 28833127761098620046464219)
      ·
        refine ⟨43249691641647930069696329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28833127761098620046464219 43249691641647930069696329)
        ·
          refine ⟨32437268731235947552272247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43249691641647930069696329 32437268731235947552272247)
          ·
            refine ⟨48655903096853921328408371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32437268731235947552272247 48655903096853921328408371)
            ·
              refine ⟨72983854645280881992612557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48655903096853921328408371 72983854645280881992612557)
              ·
                refine ⟨27368945491980330747229709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72983854645280881992612557 27368945491980330747229709)
                ·
                  refine ⟨10263354559492624030211141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27368945491980330747229709 10263354559492624030211141)
                  ·
                    refine ⟨1924378979904867005664589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10263354559492624030211141 1924378979904867005664589)
                    ·
                      refine ⟨721642117464325127124221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1924378979904867005664589 721642117464325127124221)
                      ·
                        rfl

theorem cell23_1405393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_1405393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405393 prefixEnd_1405393 := by exact prefixLift 1405393
  have htrace : WordTrace (prefixWord ++ tailWord_1405393) baseStart_1405393 baseEnd_1405393 := by
    simpa [prefixWord, tailWord_1405393, baseEnd_1405393] using wordTrace_append hprefix tailTrace_1405393
  have hstable : (prefixWord ++ tailWord_1405393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405393).length < 2 ^ (prefixWord ++ tailWord_1405393).sum := by decide
  have hdescent : baseEnd_1405393 < baseStart_1405393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405440 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 9, 1, 3]
def baseStart_1405440 : Nat := 118140960795 + 1405440 * 2 ^ 59
def prefixEnd_1405440 : Nat := 4983230072969 + 3 ^ 40 * 1405440 * 2
def baseEnd_1405440 : Nat := 721666251055086443236505

theorem tailTrace_1405440 : CollatzResearch.WordTrace tailWord_1405440 prefixEnd_1405440 721666251055086443236505 := by
  unfold tailWord_1405440
  simp only [CollatzResearch.WordTrace]
  refine ⟨25630304014169192443670887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34173738685558923258227849 25630304014169192443670887)
  ·
    refine ⟨38445456021253788665506331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25630304014169192443670887 38445456021253788665506331)
    ·
      refine ⟨57668184031880682998259497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38445456021253788665506331 57668184031880682998259497)
      ·
        refine ⟨43251138023910512248694623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57668184031880682998259497 43251138023910512248694623)
        ·
          refine ⟨64876707035865768373041935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43251138023910512248694623 64876707035865768373041935)
          ·
            refine ⟨97315060553798652559562903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64876707035865768373041935 97315060553798652559562903)
            ·
              refine ⟨145972590830697978839344355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97315060553798652559562903 145972590830697978839344355)
              ·
                refine ⟨218958886246046968259016533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145972590830697978839344355 218958886246046968259016533)
                ·
                  refine ⟨1282962224097931454642675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 218958886246046968259016533 1282962224097931454642675)
                  ·
                    refine ⟨1924443336146897181964013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1282962224097931454642675 1924443336146897181964013)
                    ·
                      refine ⟨721666251055086443236505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1924443336146897181964013 721666251055086443236505)
                      ·
                        rfl

theorem cell23_1405440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_1405440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405440 prefixEnd_1405440 := by exact prefixLift 1405440
  have htrace : WordTrace (prefixWord ++ tailWord_1405440) baseStart_1405440 baseEnd_1405440 := by
    simpa [prefixWord, tailWord_1405440, baseEnd_1405440] using wordTrace_append hprefix tailTrace_1405440
  have hstable : (prefixWord ++ tailWord_1405440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405440).length < 2 ^ (prefixWord ++ tailWord_1405440).sum := by decide
  have hdescent : baseEnd_1405440 < baseStart_1405440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405443 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 5, 5]
def baseStart_1405443 : Nat := 118140960795 + 1405443 * 2 ^ 59
def prefixEnd_1405443 : Nat := 4983230072969 + 3 ^ 40 * 1405443 * 2
def baseEnd_1405443 : Nat := 240555930499016643832997

theorem tailTrace_1405443 : CollatzResearch.WordTrace tailWord_1405443 prefixEnd_1405443 240555930499016643832997 := by
  unfold tailWord_1405443
  simp only [CollatzResearch.WordTrace]
  refine ⟨51260717447327516399700983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34173811631551677599800655 51260717447327516399700983)
  ·
    refine ⟨76891076170991274599551475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51260717447327516399700983 76891076170991274599551475)
    ·
      refine ⟨115336614256486911899327213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76891076170991274599551475 115336614256486911899327213)
      ·
        refine ⟨43251230346182591962247705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115336614256486911899327213 43251230346182591962247705)
        ·
          refine ⟨32438422759636943971685779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43251230346182591962247705 32438422759636943971685779)
          ·
            refine ⟨48657634139455415957528669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32438422759636943971685779 48657634139455415957528669)
            ·
              refine ⟨18246612802295780984073251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48657634139455415957528669 18246612802295780984073251)
              ·
                refine ⟨27369919203443671476109877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18246612802295780984073251 27369919203443671476109877)
                ·
                  refine ⟨2565929925322844200885301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27369919203443671476109877 2565929925322844200885301)
                  ·
                    refine ⟨240555930499016643832997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2565929925322844200885301 240555930499016643832997)
                    ·
                      rfl

theorem cell23_1405443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 5].length) (baseStart_1405443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405443 prefixEnd_1405443 := by exact prefixLift 1405443
  have htrace : WordTrace (prefixWord ++ tailWord_1405443) baseStart_1405443 baseEnd_1405443 := by
    simpa [prefixWord, tailWord_1405443, baseEnd_1405443] using wordTrace_append hprefix tailTrace_1405443
  have hstable : (prefixWord ++ tailWord_1405443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405443).length < 2 ^ (prefixWord ++ tailWord_1405443).sum := by decide
  have hdescent : baseEnd_1405443 < baseStart_1405443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405477 : List Nat := [1, 3, 1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_1405477 : Nat := 118140960795 + 1405477 * 2 ^ 59
def prefixEnd_1405477 : Nat := 4983230072969 + 3 ^ 40 * 1405477 * 2
def baseEnd_1405477 : Nat := 240561749946434266157945

theorem tailTrace_1405477 : CollatzResearch.WordTrace tailWord_1405477 prefixEnd_1405477 240561749946434266157945 := by
  unfold tailWord_1405477
  simp only [CollatzResearch.WordTrace]
  refine ⟨51261957529204340206438685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34174638352802893470959123 51261957529204340206438685)
  ·
    refine ⟨19223234073451627577414507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51261957529204340206438685 19223234073451627577414507)
    ·
      refine ⟨28834851110177441366121761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19223234073451627577414507 28834851110177441366121761)
      ·
        refine ⟨21626138332633081024591321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28834851110177441366121761 21626138332633081024591321)
        ·
          refine ⟨16219603749474810768443491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21626138332633081024591321 16219603749474810768443491)
          ·
            refine ⟨24329405624212216152665237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16219603749474810768443491 24329405624212216152665237)
            ·
              refine ⟨1140440888634947632156183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24329405624212216152665237 1140440888634947632156183)
              ·
                refine ⟨1710661332952421448234275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140440888634947632156183 1710661332952421448234275)
                ·
                  refine ⟨2565991999428632172351413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710661332952421448234275 2565991999428632172351413)
                  ·
                    refine ⟨240561749946434266157945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2565991999428632172351413 240561749946434266157945)
                    ·
                      rfl

theorem cell23_1405477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_1405477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405477 prefixEnd_1405477 := by exact prefixLift 1405477
  have htrace : WordTrace (prefixWord ++ tailWord_1405477) baseStart_1405477 baseEnd_1405477 := by
    simpa [prefixWord, tailWord_1405477, baseEnd_1405477] using wordTrace_append hprefix tailTrace_1405477
  have hstable : (prefixWord ++ tailWord_1405477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405477).length < 2 ^ (prefixWord ++ tailWord_1405477).sum := by decide
  have hdescent : baseEnd_1405477 < baseStart_1405477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405483 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 5]
def baseStart_1405483 : Nat := 118140960795 + 1405483 * 2 ^ 59
def prefixEnd_1405483 : Nat := 4983230072969 + 3 ^ 40 * 1405483 * 2
def baseEnd_1405483 : Nat := 721688330723229774998807

theorem tailTrace_1405483 : CollatzResearch.WordTrace tailWord_1405483 prefixEnd_1405483 721688330723229774998807 := by
  unfold tailWord_1405483
  simp only [CollatzResearch.WordTrace]
  refine ⟨51262176367182603231157103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34174784244788402154104735 51262176367182603231157103)
  ·
    refine ⟨76893264550773904846735655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51262176367182603231157103 76893264550773904846735655)
    ·
      refine ⟨115339896826160857270103483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76893264550773904846735655 115339896826160857270103483)
      ·
        refine ⟨173009845239241285905155225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115339896826160857270103483 173009845239241285905155225)
        ·
          refine ⟨129757383929430964428866419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173009845239241285905155225 129757383929430964428866419)
          ·
            refine ⟨194636075894146446643299629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129757383929430964428866419 194636075894146446643299629)
            ·
              refine ⟨72988528460304917491237361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194636075894146446643299629 72988528460304917491237361)
              ·
                refine ⟨54741396345228688118428021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72988528460304917491237361 54741396345228688118428021)
                ·
                  refine ⟨5132005907365189511102627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54741396345228688118428021 5132005907365189511102627)
                  ·
                    refine ⟨7698008861047784266653941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5132005907365189511102627 7698008861047784266653941)
                    ·
                      refine ⟨721688330723229774998807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7698008861047784266653941 721688330723229774998807)
                      ·
                        rfl

theorem cell23_1405483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 5].length) (baseStart_1405483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405483 prefixEnd_1405483 := by exact prefixLift 1405483
  have htrace : WordTrace (prefixWord ++ tailWord_1405483) baseStart_1405483 baseEnd_1405483 := by
    simpa [prefixWord, tailWord_1405483, baseEnd_1405483] using wordTrace_append hprefix tailTrace_1405483
  have hstable : (prefixWord ++ tailWord_1405483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405483).length < 2 ^ (prefixWord ++ tailWord_1405483).sum := by decide
  have hdescent : baseEnd_1405483 < baseStart_1405483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405500 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_1405500 : Nat := 118140960795 + 1405500 * 2 ^ 59
def prefixEnd_1405500 : Nat := 4983230072969 + 3 ^ 40 * 1405500 * 2
def baseEnd_1405500 : Nat := 721697059894356208486229

theorem tailTrace_1405500 : CollatzResearch.WordTrace tailWord_1405500 prefixEnd_1405500 721697059894356208486229 := by
  unfold tailWord_1405500
  simp only [CollatzResearch.WordTrace]
  refine ⟨25631398204060507567262977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34175197605414010089683969 25631398204060507567262977)
  ·
    refine ⟨19223548653045380675447233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25631398204060507567262977 19223548653045380675447233)
    ·
      refine ⟨14417661489784035506585425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19223548653045380675447233 14417661489784035506585425)
      ·
        refine ⟨10813246117338026629939069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14417661489784035506585425 10813246117338026629939069)
        ·
          refine ⟨4054967294001759986227151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10813246117338026629939069 4054967294001759986227151)
          ·
            refine ⟨6082450941002639979340727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054967294001759986227151 6082450941002639979340727)
            ·
              refine ⟨9123676411503959969011091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6082450941002639979340727 9123676411503959969011091)
              ·
                refine ⟨13685514617255939953516637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9123676411503959969011091 13685514617255939953516637)
                ·
                  refine ⟨5132067981470977482568739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13685514617255939953516637 5132067981470977482568739)
                  ·
                    refine ⟨7698101972206466223853109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5132067981470977482568739 7698101972206466223853109)
                    ·
                      refine ⟨721697059894356208486229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7698101972206466223853109 721697059894356208486229)
                      ·
                        rfl

theorem cell23_1405500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_1405500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405500 prefixEnd_1405500 := by exact prefixLift 1405500
  have htrace : WordTrace (prefixWord ++ tailWord_1405500) baseStart_1405500 baseEnd_1405500 := by
    simpa [prefixWord, tailWord_1405500, baseEnd_1405500] using wordTrace_append hprefix tailTrace_1405500
  have hstable : (prefixWord ++ tailWord_1405500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405500).length < 2 ^ (prefixWord ++ tailWord_1405500).sum := by decide
  have hdescent : baseEnd_1405500 < baseStart_1405500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405503 : List Nat := [1, 1, 2, 2, 3, 2, 2, 10]
def baseStart_1405503 : Nat := 118140960795 + 1405503 * 2 ^ 59
def prefixEnd_1405503 : Nat := 4983230072969 + 3 ^ 40 * 1405503 * 2
def baseEnd_1405503 : Nat := 26729577790234062842545

theorem tailTrace_1405503 : CollatzResearch.WordTrace tailWord_1405503 prefixEnd_1405503 26729577790234062842545 := by
  unfold tailWord_1405503
  simp only [CollatzResearch.WordTrace]
  refine ⟨51262905827110146646885163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34175270551406764431256775 51262905827110146646885163)
  ·
    refine ⟨76894358740665219970327745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51262905827110146646885163 76894358740665219970327745)
    ·
      refine ⟨57670769055498914977745809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76894358740665219970327745 57670769055498914977745809)
      ·
        refine ⟨43253076791624186233309357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57670769055498914977745809 43253076791624186233309357)
        ·
          refine ⟨16219903796859069837491009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43253076791624186233309357 16219903796859069837491009)
          ·
            refine ⟨12164927847644302378118257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16219903796859069837491009 12164927847644302378118257)
            ·
              refine ⟨9123695885733226783588693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12164927847644302378118257 9123695885733226783588693)
              ·
                refine ⟨26729577790234062842545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9123695885733226783588693 26729577790234062842545)
                ·
                  rfl

theorem cell23_1405503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 10].length) (baseStart_1405503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405503 prefixEnd_1405503 := by exact prefixLift 1405503
  have htrace : WordTrace (prefixWord ++ tailWord_1405503) baseStart_1405503 baseEnd_1405503 := by
    simpa [prefixWord, tailWord_1405503, baseEnd_1405503] using wordTrace_append hprefix tailTrace_1405503
  have hstable : (prefixWord ++ tailWord_1405503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405503).length < 2 ^ (prefixWord ++ tailWord_1405503).sum := by decide
  have hdescent : baseEnd_1405503 < baseStart_1405503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405514 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_1405514 : Nat := 118140960795 + 1405514 * 2 ^ 59
def prefixEnd_1405514 : Nat := 4983230072969 + 3 ^ 40 * 1405514 * 2
def baseEnd_1405514 : Nat := 721704248623519153711165

theorem tailTrace_1405514 : CollatzResearch.WordTrace tailWord_1405514 prefixEnd_1405514 721704248623519153711165 := by
  unfold tailWord_1405514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12815826757517573881383899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34175538020046863683690397 12815826757517573881383899)
  ·
    refine ⟨19223740136276360822075849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12815826757517573881383899 19223740136276360822075849)
    ·
      refine ⟨14417805102207270616556887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19223740136276360822075849 14417805102207270616556887)
      ·
        refine ⟨21626707653310905924835331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14417805102207270616556887 21626707653310905924835331)
        ·
          refine ⟨32440061479966358887252997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21626707653310905924835331 32440061479966358887252997)
          ·
            refine ⟨6082511527493692291359937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32440061479966358887252997 6082511527493692291359937)
            ·
              refine ⟨4561883645620269218519953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6082511527493692291359937 4561883645620269218519953)
              ·
                refine ⟨3421412734215201913889965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4561883645620269218519953 3421412734215201913889965)
                ·
                  refine ⟨1283029775330700717708737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3421412734215201913889965 1283029775330700717708737)
                  ·
                    refine ⟨962272331498025538281553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1283029775330700717708737 962272331498025538281553)
                    ·
                      refine ⟨721704248623519153711165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962272331498025538281553 721704248623519153711165)
                      ·
                        rfl

theorem cell23_1405514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_1405514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405514 prefixEnd_1405514 := by exact prefixLift 1405514
  have htrace : WordTrace (prefixWord ++ tailWord_1405514) baseStart_1405514 baseEnd_1405514 := by
    simpa [prefixWord, tailWord_1405514, baseEnd_1405514] using wordTrace_append hprefix tailTrace_1405514
  have hstable : (prefixWord ++ tailWord_1405514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405514).length < 2 ^ (prefixWord ++ tailWord_1405514).sum := by decide
  have hdescent : baseEnd_1405514 < baseStart_1405514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405558 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1405558 : Nat := 118140960795 + 1405558 * 2 ^ 59
def prefixEnd_1405558 : Nat := 4983230072969 + 3 ^ 40 * 1405558 * 2
def baseEnd_1405558 : Nat := 240575613924105660520321

theorem tailTrace_1405558 : CollatzResearch.WordTrace tailWord_1405558 prefixEnd_1405558 240575613924105660520321 := by
  unfold tailWord_1405558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204056990119430690008583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34176607894607260693424885 3204056990119430690008583)
  ·
    refine ⟨4806085485179146035012875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3204056990119430690008583 4806085485179146035012875)
    ·
      refine ⟨7209128227768719052519313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4806085485179146035012875 7209128227768719052519313)
      ·
        refine ⟨5406846170826539289389485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7209128227768719052519313 5406846170826539289389485)
        ·
          refine ⟨2027567314059952233521057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5406846170826539289389485 2027567314059952233521057)
          ·
            refine ⟨1520675485544964175140793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2027567314059952233521057 1520675485544964175140793)
            ·
              refine ⟨1140506614158723131355595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520675485544964175140793 1140506614158723131355595)
              ·
                refine ⟨1710759921238084697033393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140506614158723131355595 1710759921238084697033393)
                ·
                  refine ⟨1283069940928563522775045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1710759921238084697033393 1283069940928563522775045)
                  ·
                    refine ⟨240575613924105660520321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1283069940928563522775045 240575613924105660520321)
                    ·
                      rfl

theorem cell23_1405558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1405558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405558 prefixEnd_1405558 := by exact prefixLift 1405558
  have htrace : WordTrace (prefixWord ++ tailWord_1405558) baseStart_1405558 baseEnd_1405558 := by
    simpa [prefixWord, tailWord_1405558, baseEnd_1405558] using wordTrace_append hprefix tailTrace_1405558
  have hstable : (prefixWord ++ tailWord_1405558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405558).length < 2 ^ (prefixWord ++ tailWord_1405558).sum := by decide
  have hdescent : baseEnd_1405558 < baseStart_1405558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405587 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 1, 4, 2]
def baseStart_1405587 : Nat := 118140960795 + 1405587 * 2 ^ 59
def prefixEnd_1405587 : Nat := 4983230072969 + 3 ^ 40 * 1405587 * 2
def baseEnd_1405587 : Nat := 721741732711297368098329

theorem tailTrace_1405587 : CollatzResearch.WordTrace tailWord_1405587 prefixEnd_1405587 721741732711297368098329 := by
  unfold tailWord_1405587
  simp only [CollatzResearch.WordTrace]
  refine ⟨51265969558805828992943015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34177313039203885995295343 51265969558805828992943015)
  ·
    refine ⟨76898954338208743489414523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51265969558805828992943015 76898954338208743489414523)
    ·
      refine ⟨115348431507313115234121785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76898954338208743489414523 115348431507313115234121785)
      ·
        refine ⟨86511323630484836425591339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115348431507313115234121785 86511323630484836425591339)
        ·
          refine ⟨129766985445727254638387009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86511323630484836425591339 129766985445727254638387009)
          ·
            refine ⟨97325239084295440978790257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129766985445727254638387009 97325239084295440978790257)
            ·
              refine ⟨72993929313221580734092693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97325239084295440978790257 72993929313221580734092693)
              ·
                refine ⟨3421590436557261596910595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72993929313221580734092693 3421590436557261596910595)
                ·
                  refine ⟨5132385654835892395365893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421590436557261596910595 5132385654835892395365893)
                  ·
                    refine ⟨962322310281729824131105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5132385654835892395365893 962322310281729824131105)
                    ·
                      refine ⟨721741732711297368098329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962322310281729824131105 721741732711297368098329)
                      ·
                        rfl

theorem cell23_1405587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 4, 2].length) (baseStart_1405587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405587 prefixEnd_1405587 := by exact prefixLift 1405587
  have htrace : WordTrace (prefixWord ++ tailWord_1405587) baseStart_1405587 baseEnd_1405587 := by
    simpa [prefixWord, tailWord_1405587, baseEnd_1405587] using wordTrace_append hprefix tailTrace_1405587
  have hstable : (prefixWord ++ tailWord_1405587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405587).length < 2 ^ (prefixWord ++ tailWord_1405587).sum := by decide
  have hdescent : baseEnd_1405587 < baseStart_1405587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405591 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 1, 3, 2]
def baseStart_1405591 : Nat := 118140960795 + 1405591 * 2 ^ 59
def prefixEnd_1405591 : Nat := 4983230072969 + 3 ^ 40 * 1405591 * 2
def baseEnd_1405591 : Nat := 721743786633915352448311

theorem tailTrace_1405591 : CollatzResearch.WordTrace tailWord_1405591 prefixEnd_1405591 721743786633915352448311 := by
  unfold tailWord_1405591
  simp only [CollatzResearch.WordTrace]
  refine ⟨51266115450791337676088627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34177410300527558450725751 51266115450791337676088627)
  ·
    refine ⟨76899173176187006514132941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51266115450791337676088627 76899173176187006514132941)
    ·
      refine ⟨28837189941070127442799853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76899173176187006514132941 28837189941070127442799853)
      ·
        refine ⟨10813946227901297791049945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28837189941070127442799853 10813946227901297791049945)
        ·
          refine ⟨8110459670925973343287459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10813946227901297791049945 8110459670925973343287459)
          ·
            refine ⟨12165689506388960014931189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8110459670925973343287459 12165689506388960014931189)
            ·
              refine ⟨1140533391223965001399799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12165689506388960014931189 1140533391223965001399799)
              ·
                refine ⟨1710800086835947502099699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140533391223965001399799 1710800086835947502099699)
                ·
                  refine ⟨2566200130253921253149549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710800086835947502099699 2566200130253921253149549)
                  ·
                    refine ⟨962325048845220469931081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566200130253921253149549 962325048845220469931081)
                    ·
                      refine ⟨721743786633915352448311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962325048845220469931081 721743786633915352448311)
                      ·
                        rfl

theorem cell23_1405591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_1405591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405591 prefixEnd_1405591 := by exact prefixLift 1405591
  have htrace : WordTrace (prefixWord ++ tailWord_1405591) baseStart_1405591 baseEnd_1405591 := by
    simpa [prefixWord, tailWord_1405591, baseEnd_1405591] using wordTrace_append hprefix tailTrace_1405591
  have hstable : (prefixWord ++ tailWord_1405591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405591).length < 2 ^ (prefixWord ++ tailWord_1405591).sum := by decide
  have hdescent : baseEnd_1405591 < baseStart_1405591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405614 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1405614 : Nat := 118140960795 + 1405614 * 2 ^ 59
def prefixEnd_1405614 : Nat := 4983230072969 + 3 ^ 40 * 1405614 * 2
def baseEnd_1405614 : Nat := 240585198896322920820235

theorem tailTrace_1405614 : CollatzResearch.WordTrace tailWord_1405614 prefixEnd_1405614 240585198896322920820235 := by
  unfold tailWord_1405614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6408369291213501575521987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34177969553138675069450597 6408369291213501575521987)
  ·
    refine ⟨9612553936820252363282981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6408369291213501575521987 9612553936820252363282981)
    ·
      refine ⟨1802353863153797318115559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9612553936820252363282981 1802353863153797318115559)
      ·
        refine ⟨2703530794730695977173339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802353863153797318115559 2703530794730695977173339)
        ·
          refine ⟨4055296192096043965760009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703530794730695977173339 4055296192096043965760009)
          ·
            refine ⟨3041472144072032974320007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4055296192096043965760009 3041472144072032974320007)
            ·
              refine ⟨4562208216108049461480011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041472144072032974320007 4562208216108049461480011)
              ·
                refine ⟨6843312324162074192220017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562208216108049461480011 6843312324162074192220017)
                ·
                  refine ⟨5132484243121555644165013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6843312324162074192220017 5132484243121555644165013)
                  ·
                    refine ⟨240585198896322920820235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5132484243121555644165013 240585198896322920820235)
                    ·
                      rfl

theorem cell23_1405614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1405614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405614 prefixEnd_1405614 := by exact prefixLift 1405614
  have htrace : WordTrace (prefixWord ++ tailWord_1405614) baseStart_1405614 baseEnd_1405614 := by
    simpa [prefixWord, tailWord_1405614, baseEnd_1405614] using wordTrace_append hprefix tailTrace_1405614
  have hstable : (prefixWord ++ tailWord_1405614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405614).length < 2 ^ (prefixWord ++ tailWord_1405614).sum := by decide
  have hdescent : baseEnd_1405614 < baseStart_1405614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405621 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_1405621 : Nat := 118140960795 + 1405621 * 2 ^ 59
def prefixEnd_1405621 : Nat := 4983230072969 + 3 ^ 40 * 1405621 * 2
def baseEnd_1405621 : Nat := 721759191053550235073173

theorem tailTrace_1405621 : CollatzResearch.WordTrace tailWord_1405621 prefixEnd_1405621 721759191053550235073173 := by
  unfold tailWord_1405621
  simp only [CollatzResearch.WordTrace]
  refine ⟨51267209640682652799680717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34178139760455101866453811 51267209640682652799680717)
  ·
    refine ⟨19225203615255994799880269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51267209640682652799680717 19225203615255994799880269)
    ·
      refine ⟨7209451355720998049955101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19225203615255994799880269 7209451355720998049955101)
      ·
        refine ⟨2703544258395374268733163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7209451355720998049955101 2703544258395374268733163)
        ·
          refine ⟨4055316387593061403099745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703544258395374268733163 4055316387593061403099745)
          ·
            refine ⟨3041487290694796052324809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4055316387593061403099745 3041487290694796052324809)
            ·
              refine ⟨2281115468021097039243607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3041487290694796052324809 2281115468021097039243607)
              ·
                refine ⟨3421673202031645558865411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281115468021097039243607 3421673202031645558865411)
                ·
                  refine ⟨5132509803047468338298117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421673202031645558865411 5132509803047468338298117)
                  ·
                    refine ⟨962345588071400313430897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5132509803047468338298117 962345588071400313430897)
                    ·
                      refine ⟨721759191053550235073173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962345588071400313430897 721759191053550235073173)
                      ·
                        rfl

theorem cell23_1405621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_1405621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405621 prefixEnd_1405621 := by exact prefixLift 1405621
  have htrace : WordTrace (prefixWord ++ tailWord_1405621) baseStart_1405621 baseEnd_1405621 := by
    simpa [prefixWord, tailWord_1405621, baseEnd_1405621] using wordTrace_append hprefix tailTrace_1405621
  have hstable : (prefixWord ++ tailWord_1405621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405621).length < 2 ^ (prefixWord ++ tailWord_1405621).sum := by decide
  have hdescent : baseEnd_1405621 < baseStart_1405621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405644 : List Nat := [2, 2, 1, 5, 1, 1, 1, 5, 5]
def baseStart_1405644 : Nat := 118140960795 + 1405644 * 2 ^ 59
def prefixEnd_1405644 : Nat := 4983230072969 + 3 ^ 40 * 1405644 * 2
def baseEnd_1405644 : Nat := 80196777900955960565063

theorem tailTrace_1405644 : CollatzResearch.WordTrace tailWord_1405644 prefixEnd_1405644 80196777900955960565063 := by
  unfold tailWord_1405644
  simp only [CollatzResearch.WordTrace]
  refine ⟨25634024259799663863883993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34178699013066218485178657 25634024259799663863883993)
  ·
    refine ⟨19225518194849747897912995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25634024259799663863883993 19225518194849747897912995)
    ·
      refine ⟨28838277292274621846869493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19225518194849747897912995 28838277292274621846869493)
      ·
        refine ⟨2703588496150745798144015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28838277292274621846869493 2703588496150745798144015)
        ·
          refine ⟨4055382744226118697216023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703588496150745798144015 4055382744226118697216023)
          ·
            refine ⟨6083074116339178045824035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055382744226118697216023 6083074116339178045824035)
            ·
              refine ⟨9124611174508767068736053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083074116339178045824035 9124611174508767068736053)
              ·
                refine ⟨855432297610196912694005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9124611174508767068736053 855432297610196912694005)
                ·
                  refine ⟨80196777900955960565063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 855432297610196912694005 80196777900955960565063)
                  ·
                    rfl

theorem cell23_1405644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_1405644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405644 prefixEnd_1405644 := by exact prefixLift 1405644
  have htrace : WordTrace (prefixWord ++ tailWord_1405644) baseStart_1405644 baseEnd_1405644 := by
    simpa [prefixWord, tailWord_1405644, baseEnd_1405644] using wordTrace_append hprefix tailTrace_1405644
  have hstable : (prefixWord ++ tailWord_1405644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405644).length < 2 ^ (prefixWord ++ tailWord_1405644).sum := by decide
  have hdescent : baseEnd_1405644 < baseStart_1405644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405677 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1405677 : Nat := 118140960795 + 1405677 * 2 ^ 59
def prefixEnd_1405677 : Nat := 4983230072969 + 3 ^ 40 * 1405677 * 2
def baseEnd_1405677 : Nat := 721787945970202015972915

theorem tailTrace_1405677 : CollatzResearch.WordTrace tailWord_1405677 prefixEnd_1405677 721787945970202015972915 := by
  unfold tailWord_1405677
  simp only [CollatzResearch.WordTrace]
  refine ⟨51269252128479774363719285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34179501418986516242479523 51269252128479774363719285)
  ·
    refine ⟨4806492387044978846598683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51269252128479774363719285 4806492387044978846598683)
    ·
      refine ⟨7209738580567468269898025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4806492387044978846598683 7209738580567468269898025)
      ·
        refine ⟨5407303935425601202423519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7209738580567468269898025 5407303935425601202423519)
        ·
          refine ⟨8110955903138401803635279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407303935425601202423519 8110955903138401803635279)
          ·
            refine ⟨12166433854707602705452919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8110955903138401803635279 12166433854707602705452919)
            ·
              refine ⟨18249650782061404058179379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12166433854707602705452919 18249650782061404058179379)
              ·
                refine ⟨27374476173092106087269069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18249650782061404058179379 27374476173092106087269069)
                ·
                  refine ⟨10265428564909539782725901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27374476173092106087269069 10265428564909539782725901)
                  ·
                    refine ⟨3849535711841077418522213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10265428564909539782725901 3849535711841077418522213)
                    ·
                      refine ⟨721787945970202015972915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3849535711841077418522213 721787945970202015972915)
                      ·
                        rfl

theorem cell23_1405677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1405677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405677 prefixEnd_1405677 := by exact prefixLift 1405677
  have htrace : WordTrace (prefixWord ++ tailWord_1405677) baseStart_1405677 baseEnd_1405677 := by
    simpa [prefixWord, tailWord_1405677, baseEnd_1405677] using wordTrace_append hprefix tailTrace_1405677
  have hstable : (prefixWord ++ tailWord_1405677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405677).length < 2 ^ (prefixWord ++ tailWord_1405677).sum := by decide
  have hdescent : baseEnd_1405677 < baseStart_1405677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405694 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1405694 : Nat := 118140960795 + 1405694 * 2 ^ 59
def prefixEnd_1405694 : Nat := 4983230072969 + 3 ^ 40 * 1405694 * 2
def baseEnd_1405694 : Nat := 721796675141328449460337

theorem tailTrace_1405694 : CollatzResearch.WordTrace tailWord_1405694 prefixEnd_1405694 721796675141328449460337 := by
  unfold tailWord_1405694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6408734021177273283386017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34179914779612124178058757 6408734021177273283386017)
  ·
    refine ⟨4806550515882954962539513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6408734021177273283386017 4806550515882954962539513)
    ·
      refine ⟨3604912886912216221904635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4806550515882954962539513 3604912886912216221904635)
      ·
        refine ⟨5407369330368324332856953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604912886912216221904635 5407369330368324332856953)
        ·
          refine ⟨4055526997776243249642715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5407369330368324332856953 4055526997776243249642715)
          ·
            refine ⟨6083290496664364874464073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055526997776243249642715 6083290496664364874464073)
            ·
              refine ⟨4562467872498273655848055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6083290496664364874464073 4562467872498273655848055)
              ·
                refine ⟨6843701808747410483772083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562467872498273655848055 6843701808747410483772083)
                ·
                  refine ⟨10265552713121115725658125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6843701808747410483772083 10265552713121115725658125)
                  ·
                    refine ⟨3849582267420418397121797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10265552713121115725658125 3849582267420418397121797)
                    ·
                      refine ⟨721796675141328449460337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3849582267420418397121797 721796675141328449460337)
                      ·
                        rfl

theorem cell23_1405694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1405694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405694 prefixEnd_1405694 := by exact prefixLift 1405694
  have htrace : WordTrace (prefixWord ++ tailWord_1405694) baseStart_1405694 baseEnd_1405694 := by
    simpa [prefixWord, tailWord_1405694, baseEnd_1405694] using wordTrace_append hprefix tailTrace_1405694
  have hstable : (prefixWord ++ tailWord_1405694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405694).length < 2 ^ (prefixWord ++ tailWord_1405694).sum := by decide
  have hdescent : baseEnd_1405694 < baseStart_1405694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405717 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 6]
def baseStart_1405717 : Nat := 118140960795 + 1405717 * 2 ^ 59
def prefixEnd_1405717 : Nat := 4983230072969 + 3 ^ 40 * 1405717 * 2
def baseEnd_1405717 : Nat := 80200942799597984385859

theorem tailTrace_1405717 : CollatzResearch.WordTrace tailWord_1405717 prefixEnd_1405717 80200942799597984385859 := by
  unfold tailWord_1405717
  simp only [CollatzResearch.WordTrace]
  refine ⟨51270711048334861195175405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34180474032223240796783603 51270711048334861195175405)
  ·
    refine ⟨19226516643125572948190777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51270711048334861195175405 19226516643125572948190777)
    ·
      refine ⟨14419887482344179711143083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19226516643125572948190777 14419887482344179711143083)
      ·
        refine ⟨21629831223516269566714625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14419887482344179711143083 21629831223516269566714625)
        ·
          refine ⟨16222373417637202175035969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21629831223516269566714625 16222373417637202175035969)
          ·
            refine ⟨12166780063227901631276977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16222373417637202175035969 12166780063227901631276977)
            ·
              refine ⟨9125085047420926223457733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12166780063227901631276977 9125085047420926223457733)
              ·
                refine ⟨1710953446391423666898325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9125085047420926223457733 1710953446391423666898325)
                ·
                  refine ⟨80200942799597984385859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1710953446391423666898325 80200942799597984385859)
                  ·
                    rfl

theorem cell23_1405717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_1405717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405717 prefixEnd_1405717 := by exact prefixLift 1405717
  have htrace : WordTrace (prefixWord ++ tailWord_1405717) baseStart_1405717 baseEnd_1405717 := by
    simpa [prefixWord, tailWord_1405717, baseEnd_1405717] using wordTrace_append hprefix tailTrace_1405717
  have hstable : (prefixWord ++ tailWord_1405717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405717).length < 2 ^ (prefixWord ++ tailWord_1405717).sum := by decide
  have hdescent : baseEnd_1405717 < baseStart_1405717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405744 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 3, 1, 3]
def baseStart_1405744 : Nat := 118140960795 + 1405744 * 2 ^ 59
def prefixEnd_1405744 : Nat := 4983230072969 + 3 ^ 40 * 1405744 * 2
def baseEnd_1405744 : Nat := 721822349174053253835107

theorem tailTrace_1405744 : CollatzResearch.WordTrace tailWord_1405744 prefixEnd_1405744 721822349174053253835107 := by
  unfold tailWord_1405744
  simp only [CollatzResearch.WordTrace]
  refine ⟨25635847909618522403204143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34181130546158029870938857 25635847909618522403204143)
  ·
    refine ⟨38453771864427783604806215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25635847909618522403204143 38453771864427783604806215)
    ·
      refine ⟨57680657796641675407209323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38453771864427783604806215 57680657796641675407209323)
      ·
        refine ⟨86520986694962513110813985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57680657796641675407209323 86520986694962513110813985)
        ·
          refine ⟨64890740021221884833110489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86520986694962513110813985 64890740021221884833110489)
          ·
            refine ⟨48668055015916413624832867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64890740021221884833110489 48668055015916413624832867)
            ·
              refine ⟨73002082523874620437249301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48668055015916413624832867 73002082523874620437249301)
              ·
                refine ⟨3421972618306622832996061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73002082523874620437249301 3421972618306622832996061)
                ·
                  refine ⟨1283239731864983562373523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3421972618306622832996061 1283239731864983562373523)
                  ·
                    refine ⟨1924859597797475343560285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1283239731864983562373523 1924859597797475343560285)
                    ·
                      refine ⟨721822349174053253835107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1924859597797475343560285 721822349174053253835107)
                      ·
                        rfl

theorem cell23_1405744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 1, 3].length) (baseStart_1405744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405744 prefixEnd_1405744 := by exact prefixLift 1405744
  have htrace : WordTrace (prefixWord ++ tailWord_1405744) baseStart_1405744 baseEnd_1405744 := by
    simpa [prefixWord, tailWord_1405744, baseEnd_1405744] using wordTrace_append hprefix tailTrace_1405744
  have hstable : (prefixWord ++ tailWord_1405744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405744).length < 2 ^ (prefixWord ++ tailWord_1405744).sum := by decide
  have hdescent : baseEnd_1405744 < baseStart_1405744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405748 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1405748 : Nat := 118140960795 + 1405748 * 2 ^ 59
def prefixEnd_1405748 : Nat := 4983230072969 + 3 ^ 40 * 1405748 * 2
def baseEnd_1405748 : Nat := 721824403096671238185089

theorem tailTrace_1405748 : CollatzResearch.WordTrace tailWord_1405748 prefixEnd_1405748 721824403096671238185089 := by
  unfold tailWord_1405748
  simp only [CollatzResearch.WordTrace]
  refine ⟨25635920855611276744776949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34181227807481702326369265 25635920855611276744776949)
  ·
    refine ⟨2403367580213557194822839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25635920855611276744776949 2403367580213557194822839)
    ·
      refine ⟨3605051370320335792234259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2403367580213557194822839 3605051370320335792234259)
      ·
        refine ⟨5407577055480503688351389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605051370320335792234259 5407577055480503688351389)
        ·
          refine ⟨2027841395805188883131771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5407577055480503688351389 2027841395805188883131771)
          ·
            refine ⟨3041762093707783324697657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027841395805188883131771 3041762093707783324697657)
            ·
              refine ⟨2281321570280837493523243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3041762093707783324697657 2281321570280837493523243)
              ·
                refine ⟨3421982355421256240284865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281321570280837493523243 3421982355421256240284865)
                ·
                  refine ⟨2566486766565942180213649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3421982355421256240284865 2566486766565942180213649)
                  ·
                    refine ⟨1924865074924456635160237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2566486766565942180213649 1924865074924456635160237)
                    ·
                      refine ⟨721824403096671238185089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1924865074924456635160237 721824403096671238185089)
                      ·
                        rfl

theorem cell23_1405748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1405748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405748 prefixEnd_1405748 := by exact prefixLift 1405748
  have htrace : WordTrace (prefixWord ++ tailWord_1405748) baseStart_1405748 baseEnd_1405748 := by
    simpa [prefixWord, tailWord_1405748, baseEnd_1405748] using wordTrace_append hprefix tailTrace_1405748
  have hstable : (prefixWord ++ tailWord_1405748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405748).length < 2 ^ (prefixWord ++ tailWord_1405748).sum := by decide
  have hdescent : baseEnd_1405748 < baseStart_1405748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405778 : List Nat := [3, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_1405778 : Nat := 118140960795 + 1405778 * 2 ^ 59
def prefixEnd_1405778 : Nat := 4983230072969 + 3 ^ 40 * 1405778 * 2
def baseEnd_1405778 : Nat := 721839807516306120809951

theorem tailTrace_1405778 : CollatzResearch.WordTrace tailWord_1405778 prefixEnd_1405778 721839807516306120809951 := by
  unfold tailWord_1405778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818233975278467153286497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34181957267409245742097325 12818233975278467153286497)
  ·
    refine ⟨9613675481458850364964873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12818233975278467153286497 9613675481458850364964873)
    ·
      refine ⟨7210256611094137773723655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9613675481458850364964873 7210256611094137773723655)
      ·
        refine ⟨10815384916641206660585483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7210256611094137773723655 10815384916641206660585483)
        ·
          refine ⟨16223077374961809990878225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10815384916641206660585483 16223077374961809990878225)
          ·
            refine ⟨12167308031221357493158669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16223077374961809990878225 12167308031221357493158669)
            ·
              refine ⟨4562740511708009059934501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12167308031221357493158669 4562740511708009059934501)
              ·
                refine ⟨855513845945251698737719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4562740511708009059934501 855513845945251698737719)
                ·
                  refine ⟨1283270768917877548106579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855513845945251698737719 1283270768917877548106579)
                  ·
                    refine ⟨1924906153376816322159869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1283270768917877548106579 1924906153376816322159869)
                    ·
                      refine ⟨721839807516306120809951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1924906153376816322159869 721839807516306120809951)
                      ·
                        rfl

theorem cell23_1405778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_1405778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405778 prefixEnd_1405778 := by exact prefixLift 1405778
  have htrace : WordTrace (prefixWord ++ tailWord_1405778) baseStart_1405778 baseEnd_1405778 := by
    simpa [prefixWord, tailWord_1405778, baseEnd_1405778] using wordTrace_append hprefix tailTrace_1405778
  have hstable : (prefixWord ++ tailWord_1405778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405778).length < 2 ^ (prefixWord ++ tailWord_1405778).sum := by decide
  have hdescent : baseEnd_1405778 < baseStart_1405778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405797 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1405797 : Nat := 118140960795 + 1405797 * 2 ^ 59
def prefixEnd_1405797 : Nat := 4983230072969 + 3 ^ 40 * 1405797 * 2
def baseEnd_1405797 : Nat := 721849563648741546472363

theorem tailTrace_1405797 : CollatzResearch.WordTrace tailWord_1405797 prefixEnd_1405797 721849563648741546472363 := by
  unfold tailWord_1405797
  simp only [CollatzResearch.WordTrace]
  refine ⟨51273628888045034858087645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34182419258696689905391763 51273628888045034858087645)
  ·
    refine ⟨19227610833016888071782867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51273628888045034858087645 19227610833016888071782867)
    ·
      refine ⟨28841416249525332107674301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19227610833016888071782867 28841416249525332107674301)
      ·
        refine ⟨10815531093571999540377863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28841416249525332107674301 10815531093571999540377863)
        ·
          refine ⟨16223296640357999310566795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10815531093571999540377863 16223296640357999310566795)
          ·
            refine ⟨24334944960536998965850193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16223296640357999310566795 24334944960536998965850193)
            ·
              refine ⟨18251208720402749224387645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24334944960536998965850193 18251208720402749224387645)
              ·
                refine ⟨6844203270151030959145367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18251208720402749224387645 6844203270151030959145367)
                ·
                  refine ⟨10266304905226546438718051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6844203270151030959145367 10266304905226546438718051)
                  ·
                    refine ⟨15399457357839819658077077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10266304905226546438718051 15399457357839819658077077)
                    ·
                      refine ⟨721849563648741546472363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15399457357839819658077077 721849563648741546472363)
                      ·
                        rfl

theorem cell23_1405797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1405797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405797 prefixEnd_1405797 := by exact prefixLift 1405797
  have htrace : WordTrace (prefixWord ++ tailWord_1405797) baseStart_1405797 baseEnd_1405797 := by
    simpa [prefixWord, tailWord_1405797, baseEnd_1405797] using wordTrace_append hprefix tailTrace_1405797
  have hstable : (prefixWord ++ tailWord_1405797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405797).length < 2 ^ (prefixWord ++ tailWord_1405797).sum := by decide
  have hdescent : baseEnd_1405797 < baseStart_1405797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405804 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 3]
def baseStart_1405804 : Nat := 118140960795 + 1405804 * 2 ^ 59
def prefixEnd_1405804 : Nat := 4983230072969 + 3 ^ 40 * 1405804 * 2
def baseEnd_1405804 : Nat := 721853158013323019084831

theorem tailTrace_1405804 : CollatzResearch.WordTrace tailWord_1405804 prefixEnd_1405804 721853158013323019084831 := by
  unfold tailWord_1405804
  simp only [CollatzResearch.WordTrace]
  refine ⟨25636942099509837526796233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34182589466013116702394977 25636942099509837526796233)
  ·
    refine ⟨19227706574632378145097175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25636942099509837526796233 19227706574632378145097175)
    ·
      refine ⟨28841559861948567217645763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19227706574632378145097175 28841559861948567217645763)
      ·
        refine ⟨43262339792922850826468645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28841559861948567217645763 43262339792922850826468645)
        ·
          refine ⟨8111688711173034529962871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43262339792922850826468645 8111688711173034529962871)
          ·
            refine ⟨12167533066759551794944307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8111688711173034529962871 12167533066759551794944307)
            ·
              refine ⟨18251299600139327692416461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12167533066759551794944307 18251299600139327692416461)
              ·
                refine ⟨6844237350052247884656173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18251299600139327692416461 6844237350052247884656173)
                ·
                  refine ⟨2566589006269592956746065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6844237350052247884656173 2566589006269592956746065)
                  ·
                    refine ⟨1924941754702194717559549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2566589006269592956746065 1924941754702194717559549)
                    ·
                      refine ⟨721853158013323019084831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1924941754702194717559549 721853158013323019084831)
                      ·
                        rfl

theorem cell23_1405804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_1405804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405804 prefixEnd_1405804 := by exact prefixLift 1405804
  have htrace : WordTrace (prefixWord ++ tailWord_1405804) baseStart_1405804 baseEnd_1405804 := by
    simpa [prefixWord, tailWord_1405804, baseEnd_1405804] using wordTrace_append hprefix tailTrace_1405804
  have hstable : (prefixWord ++ tailWord_1405804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405804).length < 2 ^ (prefixWord ++ tailWord_1405804).sum := by decide
  have hdescent : baseEnd_1405804 < baseStart_1405804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405887 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 6]
def baseStart_1405887 : Nat := 118140960795 + 1405887 * 2 ^ 59
def prefixEnd_1405887 : Nat := 4983230072969 + 3 ^ 40 * 1405887 * 2
def baseEnd_1405887 : Nat := 721895776907646194346949

theorem tailTrace_1405887 : CollatzResearch.WordTrace tailWord_1405887 prefixEnd_1405887 721895776907646194346949 := by
  unfold tailWord_1405887
  simp only [CollatzResearch.WordTrace]
  refine ⟨51276911457718980228863915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34184607638479320152575943 51276911457718980228863915)
  ·
    refine ⟨76915367186578470343295873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51276911457718980228863915 76915367186578470343295873)
    ·
      refine ⟨57686525389933852757471905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76915367186578470343295873 57686525389933852757471905)
      ·
        refine ⟨43264894042450389568103929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57686525389933852757471905 43264894042450389568103929)
        ·
          refine ⟨32448670531837792176077947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43264894042450389568103929 32448670531837792176077947)
          ·
            refine ⟨48673005797756688264116921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32448670531837792176077947 48673005797756688264116921)
            ·
              refine ⟨36504754348317516198087691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48673005797756688264116921 36504754348317516198087691)
              ·
                refine ⟨54757131522476274297131537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36504754348317516198087691 54757131522476274297131537)
                ·
                  refine ⟨41067848641857205722848653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54757131522476274297131537 41067848641857205722848653)
                  ·
                    refine ⟨15400443240696452146068245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41067848641857205722848653 15400443240696452146068245)
                    ·
                      refine ⟨721895776907646194346949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15400443240696452146068245 721895776907646194346949)
                      ·
                        rfl

theorem cell23_1405887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_1405887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405887 prefixEnd_1405887 := by exact prefixLift 1405887
  have htrace : WordTrace (prefixWord ++ tailWord_1405887) baseStart_1405887 baseEnd_1405887 := by
    simpa [prefixWord, tailWord_1405887, baseEnd_1405887] using wordTrace_append hprefix tailTrace_1405887
  have hstable : (prefixWord ++ tailWord_1405887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405887).length < 2 ^ (prefixWord ++ tailWord_1405887).sum := by decide
  have hdescent : baseEnd_1405887 < baseStart_1405887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405924 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_1405924 : Nat := 118140960795 + 1405924 * 2 ^ 59
def prefixEnd_1405924 : Nat := 4983230072969 + 3 ^ 40 * 1405924 * 2
def baseEnd_1405924 : Nat := 721914775691862549584279

theorem tailTrace_1405924 : CollatzResearch.WordTrace tailWord_1405924 prefixEnd_1405924 721914775691862549584279 := by
  unfold tailWord_1405924
  simp only [CollatzResearch.WordTrace]
  refine ⟨25639130479292467773980413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34185507305723290365307217 25639130479292467773980413)
  ·
    refine ⟨9614673929734675415242655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25639130479292467773980413 9614673929734675415242655)
    ·
      refine ⟨14422010894602013122863983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9614673929734675415242655 14422010894602013122863983)
      ·
        refine ⟨21633016341903019684295975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14422010894602013122863983 21633016341903019684295975)
        ·
          refine ⟨32449524512854529526443963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21633016341903019684295975 32449524512854529526443963)
          ·
            refine ⟨48674286769281794289665945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32449524512854529526443963 48674286769281794289665945)
            ·
              refine ⟨36505715076961345717249459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48674286769281794289665945 36505715076961345717249459)
              ·
                refine ⟨54758572615442018575874189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36505715076961345717249459 54758572615442018575874189)
                ·
                  refine ⟨20534464730790756965952821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54758572615442018575874189 20534464730790756965952821)
                  ·
                    refine ⟨1925106068511633465558077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20534464730790756965952821 1925106068511633465558077)
                    ·
                      refine ⟨721914775691862549584279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1925106068511633465558077 721914775691862549584279)
                      ·
                        rfl

theorem cell23_1405924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_1405924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405924 prefixEnd_1405924 := by exact prefixLift 1405924
  have htrace : WordTrace (prefixWord ++ tailWord_1405924) baseStart_1405924 baseEnd_1405924 := by
    simpa [prefixWord, tailWord_1405924, baseEnd_1405924] using wordTrace_append hprefix tailTrace_1405924
  have hstable : (prefixWord ++ tailWord_1405924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405924).length < 2 ^ (prefixWord ++ tailWord_1405924).sum := by decide
  have hdescent : baseEnd_1405924 < baseStart_1405924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405925 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1405925 : Nat := 118140960795 + 1405925 * 2 ^ 59
def prefixEnd_1405925 : Nat := 4983230072969 + 3 ^ 40 * 1405925 * 2
def baseEnd_1405925 : Nat := 721915289172517045671775

theorem tailTrace_1405925 : CollatzResearch.WordTrace tailWord_1405925 prefixEnd_1405925 721915289172517045671775 := by
  unfold tailWord_1405925
  simp only [CollatzResearch.WordTrace]
  refine ⟨51278297431581312718747229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34185531621054208479164819 51278297431581312718747229)
  ·
    refine ⟨19229361536842992269530211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51278297431581312718747229 19229361536842992269530211)
    ·
      refine ⟨28844042305264488404295317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19229361536842992269530211 28844042305264488404295317)
      ·
        refine ⟨1352064483059272893951343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28844042305264488404295317 1352064483059272893951343)
        ·
          refine ⟨2028096724588909340927015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352064483059272893951343 2028096724588909340927015)
          ·
            refine ⟨3042145086883364011390523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028096724588909340927015 3042145086883364011390523)
            ·
              refine ⟨4563217630325046017085785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042145086883364011390523 4563217630325046017085785)
              ·
                refine ⟨3422413222743784512814339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4563217630325046017085785 3422413222743784512814339)
                ·
                  refine ⟨5133619834115676769221509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422413222743784512814339 5133619834115676769221509)
                  ·
                    refine ⟨962553718896689394229033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133619834115676769221509 962553718896689394229033)
                    ·
                      refine ⟨721915289172517045671775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962553718896689394229033 721915289172517045671775)
                      ·
                        rfl

theorem cell23_1405925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1405925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405925 prefixEnd_1405925 := by exact prefixLift 1405925
  have htrace : WordTrace (prefixWord ++ tailWord_1405925) baseStart_1405925 baseEnd_1405925 := by
    simpa [prefixWord, tailWord_1405925, baseEnd_1405925] using wordTrace_append hprefix tailTrace_1405925
  have hstable : (prefixWord ++ tailWord_1405925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405925).length < 2 ^ (prefixWord ++ tailWord_1405925).sum := by decide
  have hdescent : baseEnd_1405925 < baseStart_1405925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405942 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_1405942 : Nat := 118140960795 + 1405942 * 2 ^ 59
def prefixEnd_1405942 : Nat := 4983230072969 + 3 ^ 40 * 1405942 * 2
def baseEnd_1405942 : Nat := 721924018343643479159197

theorem tailTrace_1405942 : CollatzResearch.WordTrace tailWord_1405942 prefixEnd_1405942 721924018343643479159197 := by
  unfold tailWord_1405942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204932342032482788882255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34185944981679816414744053 3204932342032482788882255)
  ·
    refine ⟨4807398513048724183323383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3204932342032482788882255 4807398513048724183323383)
    ·
      refine ⟨7211097769573086274985075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4807398513048724183323383 7211097769573086274985075)
      ·
        refine ⟨10816646654359629412477613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7211097769573086274985075 10816646654359629412477613)
        ·
          refine ⟨4056242495384861029679105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10816646654359629412477613 4056242495384861029679105)
          ·
            refine ⟨3042181871538645772259329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4056242495384861029679105 3042181871538645772259329)
            ·
              refine ⟨2281636403653984329194497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042181871538645772259329 2281636403653984329194497)
              ·
                refine ⟨1711227302740488246895873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281636403653984329194497 1711227302740488246895873)
                ·
                  refine ⟨1283420477055366185171905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711227302740488246895873 1283420477055366185171905)
                  ·
                    refine ⟨962565357791524638878929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1283420477055366185171905 962565357791524638878929)
                    ·
                      refine ⟨721924018343643479159197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962565357791524638878929 721924018343643479159197)
                      ·
                        rfl

theorem cell23_1405942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_1405942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405942 prefixEnd_1405942 := by exact prefixLift 1405942
  have htrace : WordTrace (prefixWord ++ tailWord_1405942) baseStart_1405942 baseEnd_1405942 := by
    simpa [prefixWord, tailWord_1405942, baseEnd_1405942] using wordTrace_append hprefix tailTrace_1405942
  have hstable : (prefixWord ++ tailWord_1405942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405942).length < 2 ^ (prefixWord ++ tailWord_1405942).sum := by decide
  have hdescent : baseEnd_1405942 < baseStart_1405942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405948 : List Nat := [2, 2, 2, 1, 2, 3, 4, 2, 5]
def baseStart_1405948 : Nat := 118140960795 + 1405948 * 2 ^ 59
def prefixEnd_1405948 : Nat := 4983230072969 + 3 ^ 40 * 1405948 * 2
def baseEnd_1405948 : Nat := 80214122136396717298241

theorem tailTrace_1405948 : CollatzResearch.WordTrace tailWord_1405948 prefixEnd_1405948 80214122136396717298241 := by
  unfold tailWord_1405948
  simp only [CollatzResearch.WordTrace]
  refine ⟨25639568155248993823417249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34186090873665325097889665 25639568155248993823417249)
  ·
    refine ⟨19229676116436745367562937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25639568155248993823417249 19229676116436745367562937)
    ·
      refine ⟨14422257087327559025672203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19229676116436745367562937 14422257087327559025672203)
      ·
        refine ⟨21633385630991338538508305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14422257087327559025672203 21633385630991338538508305)
        ·
          refine ⟨16225039223243503903881229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21633385630991338538508305 16225039223243503903881229)
          ·
            refine ⟨6084389708716313963955461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16225039223243503903881229 6084389708716313963955461)
            ·
              refine ⟨1140823070384308868241649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6084389708716313963955461 1140823070384308868241649)
              ·
                refine ⟨855617302788231651181237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1140823070384308868241649 855617302788231651181237)
                ·
                  refine ⟨80214122136396717298241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 855617302788231651181237 80214122136396717298241)
                  ·
                    rfl

theorem cell23_1405948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_1405948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405948 prefixEnd_1405948 := by exact prefixLift 1405948
  have htrace : WordTrace (prefixWord ++ tailWord_1405948) baseStart_1405948 baseEnd_1405948 := by
    simpa [prefixWord, tailWord_1405948, baseEnd_1405948] using wordTrace_append hprefix tailTrace_1405948
  have hstable : (prefixWord ++ tailWord_1405948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405948).length < 2 ^ (prefixWord ++ tailWord_1405948).sum := by decide
  have hdescent : baseEnd_1405948 < baseStart_1405948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1405998 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_1405998 : Nat := 118140960795 + 1405998 * 2 ^ 59
def prefixEnd_1405998 : Nat := 4983230072969 + 3 ^ 40 * 1405998 * 2
def baseEnd_1405998 : Nat := 721952773260295260058939

theorem tailTrace_1405998 : CollatzResearch.WordTrace tailWord_1405998 prefixEnd_1405998 721952773260295260058939 := by
  unfold tailWord_1405998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6410119995039605773269331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34187306640211230790769765 6410119995039605773269331)
  ·
    refine ⟨9615179992559408659903997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6410119995039605773269331 9615179992559408659903997)
    ·
      refine ⟨3605692497209778247463999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9615179992559408659903997 3605692497209778247463999)
      ·
        refine ⟨5408538745814667371195999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605692497209778247463999 5408538745814667371195999)
        ·
          refine ⟨8112808118722001056793999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5408538745814667371195999 8112808118722001056793999)
          ·
            refine ⟨12169212178083001585190999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8112808118722001056793999 12169212178083001585190999)
            ·
              refine ⟨18253818267124502377786499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12169212178083001585190999 18253818267124502377786499)
              ·
                refine ⟨27380727400686753566679749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18253818267124502377786499 27380727400686753566679749)
                ·
                  refine ⟨5133886387628766293752453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27380727400686753566679749 5133886387628766293752453)
                  ·
                    refine ⟨962603697680393680078585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133886387628766293752453 962603697680393680078585)
                    ·
                      refine ⟨721952773260295260058939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962603697680393680078585 721952773260295260058939)
                      ·
                        rfl

theorem cell23_1405998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_1405998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1405998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1405998 prefixEnd_1405998 := by exact prefixLift 1405998
  have htrace : WordTrace (prefixWord ++ tailWord_1405998) baseStart_1405998 baseEnd_1405998 := by
    simpa [prefixWord, tailWord_1405998, baseEnd_1405998] using wordTrace_append hprefix tailTrace_1405998
  have hstable : (prefixWord ++ tailWord_1405998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1405998).length < 2 ^ (prefixWord ++ tailWord_1405998).sum := by decide
  have hdescent : baseEnd_1405998 < baseStart_1405998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1405998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406001 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_1406001 : Nat := 118140960795 + 1406001 * 2 ^ 59
def prefixEnd_1406001 : Nat := 4983230072969 + 3 ^ 40 * 1406001 * 2
def baseEnd_1406001 : Nat := 721954313702258748321425

theorem tailTrace_1406001 : CollatzResearch.WordTrace tailWord_1406001 prefixEnd_1406001 721954313702258748321425 := by
  unfold tailWord_1406001
  simp only [CollatzResearch.WordTrace]
  refine ⟨51281069379305977698513857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34187379586203985132342571 51281069379305977698513857)
  ·
    refine ⟨38460802034479483273885393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51281069379305977698513857 38460802034479483273885393)
    ·
      refine ⟨28845601525859612455414045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38460802034479483273885393 28845601525859612455414045)
      ·
        refine ⟨10817100572197354670780267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28845601525859612455414045 10817100572197354670780267)
        ·
          refine ⟨16225650858296032006170401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10817100572197354670780267 16225650858296032006170401)
          ·
            refine ⟨12169238143722024004627801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16225650858296032006170401 12169238143722024004627801)
            ·
              refine ⟨9126928607791518003470851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12169238143722024004627801 9126928607791518003470851)
              ·
                refine ⟨13690392911687277005206277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9126928607791518003470851 13690392911687277005206277)
                ·
                  refine ⟨2566948670941364438476177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13690392911687277005206277 2566948670941364438476177)
                  ·
                    refine ⟨1925211503206023328857133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2566948670941364438476177 1925211503206023328857133)
                    ·
                      refine ⟨721954313702258748321425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1925211503206023328857133 721954313702258748321425)
                      ·
                        rfl

theorem cell23_1406001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_1406001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406001 prefixEnd_1406001 := by exact prefixLift 1406001
  have htrace : WordTrace (prefixWord ++ tailWord_1406001) baseStart_1406001 baseEnd_1406001 := by
    simpa [prefixWord, tailWord_1406001, baseEnd_1406001] using wordTrace_append hprefix tailTrace_1406001
  have hstable : (prefixWord ++ tailWord_1406001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406001).length < 2 ^ (prefixWord ++ tailWord_1406001).sum := by decide
  have hdescent : baseEnd_1406001 < baseStart_1406001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406008 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 3, 4]
def baseStart_1406008 : Nat := 118140960795 + 1406008 * 2 ^ 59
def prefixEnd_1406008 : Nat := 4983230072969 + 3 ^ 40 * 1406008 * 2
def baseEnd_1406008 : Nat := 240652636022280073644631

theorem tailTrace_1406008 : CollatzResearch.WordTrace tailWord_1406008 prefixEnd_1406008 240652636022280073644631 := by
  unfold tailWord_1406008
  simp only [CollatzResearch.WordTrace]
  refine ⟨25640662345140308947009339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34187549793520411929345785 25640662345140308947009339)
  ·
    refine ⟨38460993517710463420514009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25640662345140308947009339 38460993517710463420514009)
    ·
      refine ⟨28845745138282847565385507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38460993517710463420514009 28845745138282847565385507)
      ·
        refine ⟨43268617707424271348078261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28845745138282847565385507 43268617707424271348078261)
        ·
          refine ⟨4056432910071025438882337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43268617707424271348078261 4056432910071025438882337)
          ·
            refine ⟨3042324682553269079161753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4056432910071025438882337 3042324682553269079161753)
            ·
              refine ⟨2281743511914951809371315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042324682553269079161753 2281743511914951809371315)
              ·
                refine ⟨3422615267872427714056973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281743511914951809371315 3422615267872427714056973)
                ·
                  refine ⟨1283480725452160392771365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3422615267872427714056973 1283480725452160392771365)
                  ·
                    refine ⟨240652636022280073644631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1283480725452160392771365 240652636022280073644631)
                    ·
                      rfl

theorem cell23_1406008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_1406008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406008 prefixEnd_1406008 := by exact prefixLift 1406008
  have htrace : WordTrace (prefixWord ++ tailWord_1406008) baseStart_1406008 baseEnd_1406008 := by
    simpa [prefixWord, tailWord_1406008, baseEnd_1406008] using wordTrace_append hprefix tailTrace_1406008
  have hstable : (prefixWord ++ tailWord_1406008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406008).length < 2 ^ (prefixWord ++ tailWord_1406008).sum := by decide
  have hdescent : baseEnd_1406008 < baseStart_1406008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406024 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_1406024 : Nat := 118140960795 + 1406024 * 2 ^ 59
def prefixEnd_1406024 : Nat := 4983230072969 + 3 ^ 40 * 1406024 * 2
def baseEnd_1406024 : Nat := 721966123757312158333819

theorem tailTrace_1406024 : CollatzResearch.WordTrace tailWord_1406024 prefixEnd_1406024 721966123757312158333819 := by
  unfold tailWord_1406024
  simp only [CollatzResearch.WordTrace]
  refine ⟨25640954129111326313300563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34187938838815101751067417 25640954129111326313300563)
  ·
    refine ⟨38461431193666989469950845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25640954129111326313300563 38461431193666989469950845)
    ·
      refine ⟨14423036697625121051231567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38461431193666989469950845 14423036697625121051231567)
      ·
        refine ⟨21634555046437681576847351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14423036697625121051231567 21634555046437681576847351)
        ·
          refine ⟨32451832569656522365271027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21634555046437681576847351 32451832569656522365271027)
          ·
            refine ⟨48677748854484783547906541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32451832569656522365271027 48677748854484783547906541)
            ·
              refine ⟨18254155820431793830464953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48677748854484783547906541 18254155820431793830464953)
              ·
                refine ⟨13690616865323845372848715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18254155820431793830464953 13690616865323845372848715)
                ·
                  refine ⟨20535925297985768059273073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13690616865323845372848715 20535925297985768059273073)
                  ·
                    refine ⟨15401943973489326044454805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20535925297985768059273073 15401943973489326044454805)
                    ·
                      refine ⟨721966123757312158333819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15401943973489326044454805 721966123757312158333819)
                      ·
                        rfl

theorem cell23_1406024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_1406024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406024 prefixEnd_1406024 := by exact prefixLift 1406024
  have htrace : WordTrace (prefixWord ++ tailWord_1406024) baseStart_1406024 baseEnd_1406024 := by
    simpa [prefixWord, tailWord_1406024, baseEnd_1406024] using wordTrace_append hprefix tailTrace_1406024
  have hstable : (prefixWord ++ tailWord_1406024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406024).length < 2 ^ (prefixWord ++ tailWord_1406024).sum := by decide
  have hdescent : baseEnd_1406024 < baseStart_1406024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406071 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_1406071 : Nat := 118140960795 + 1406071 * 2 ^ 59
def prefixEnd_1406071 : Nat := 4983230072969 + 3 ^ 40 * 1406071 * 2
def baseEnd_1406071 : Nat := 721990257348073474446103

theorem tailTrace_1406071 : CollatzResearch.WordTrace tailWord_1406071 prefixEnd_1406071 721990257348073474446103 := by
  unfold tailWord_1406071
  simp only [CollatzResearch.WordTrace]
  refine ⟨51283622489052379653562067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34189081659368253102374711 51283622489052379653562067)
  ·
    refine ⟨76925433733578569480343101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51283622489052379653562067 76925433733578569480343101)
    ·
      refine ⟨28847037650091963555128663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76925433733578569480343101 28847037650091963555128663)
      ·
        refine ⟨43270556475137945332692995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28847037650091963555128663 43270556475137945332692995)
        ·
          refine ⟨64905834712706917999039493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43270556475137945332692995 64905834712706917999039493)
          ·
            refine ⟨12169844008632547124819905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64905834712706917999039493 12169844008632547124819905)
            ·
              refine ⟨9127383006474410343614929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12169844008632547124819905 9127383006474410343614929)
              ·
                refine ⟨6845537254855807757711197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9127383006474410343614929 6845537254855807757711197)
                ·
                  refine ⟨2567076470570927909141699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6845537254855807757711197 2567076470570927909141699)
                  ·
                    refine ⟨3850614705856391863712549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2567076470570927909141699 3850614705856391863712549)
                    ·
                      refine ⟨721990257348073474446103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3850614705856391863712549 721990257348073474446103)
                      ·
                        rfl

theorem cell23_1406071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_1406071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406071 prefixEnd_1406071 := by exact prefixLift 1406071
  have htrace : WordTrace (prefixWord ++ tailWord_1406071) baseStart_1406071 baseEnd_1406071 := by
    simpa [prefixWord, tailWord_1406071, baseEnd_1406071] using wordTrace_append hprefix tailTrace_1406071
  have hstable : (prefixWord ++ tailWord_1406071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406071).length < 2 ^ (prefixWord ++ tailWord_1406071).sum := by decide
  have hdescent : baseEnd_1406071 < baseStart_1406071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406085 : List Nat := [1, 3, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_1406085 : Nat := 118140960795 + 1406085 * 2 ^ 59
def prefixEnd_1406085 : Nat := 4983230072969 + 3 ^ 40 * 1406085 * 2
def baseEnd_1406085 : Nat := 240665815359078806557013

theorem tailTrace_1406085 : CollatzResearch.WordTrace tailWord_1406085 prefixEnd_1406085 240665815359078806557013 := by
  unfold tailWord_1406085
  simp only [CollatzResearch.WordTrace]
  refine ⟨51284133111001660044571709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34189422074001106696381139 51284133111001660044571709)
  ·
    refine ⟨19231549916625622516714391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51284133111001660044571709 19231549916625622516714391)
    ·
      refine ⟨28847324874938433775071587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19231549916625622516714391 28847324874938433775071587)
      ·
        refine ⟨43270987312407650662607381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28847324874938433775071587 43270987312407650662607381)
        ·
          refine ⟨2028327530269108624809721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43270987312407650662607381 2028327530269108624809721)
          ·
            refine ⟨1521245647701831468607291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2028327530269108624809721 1521245647701831468607291)
            ·
              refine ⟨2281868471552747202910937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521245647701831468607291 2281868471552747202910937)
              ·
                refine ⟨1711401353664560402183203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281868471552747202910937 1711401353664560402183203)
                ·
                  refine ⟨2567102030496840603274805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711401353664560402183203 2567102030496840603274805)
                  ·
                    refine ⟨240665815359078806557013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2567102030496840603274805 240665815359078806557013)
                    ·
                      rfl

theorem cell23_1406085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_1406085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406085 prefixEnd_1406085 := by exact prefixLift 1406085
  have htrace : WordTrace (prefixWord ++ tailWord_1406085) baseStart_1406085 baseEnd_1406085 := by
    simpa [prefixWord, tailWord_1406085, baseEnd_1406085] using wordTrace_append hprefix tailTrace_1406085
  have hstable : (prefixWord ++ tailWord_1406085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406085).length < 2 ^ (prefixWord ++ tailWord_1406085).sum := by decide
  have hdescent : baseEnd_1406085 < baseStart_1406085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406098 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_1406098 : Nat := 118140960795 + 1406098 * 2 ^ 59
def prefixEnd_1406098 : Nat := 4983230072969 + 3 ^ 40 * 1406098 * 2
def baseEnd_1406098 : Nat := 240668040441914956269493

theorem tailTrace_1406098 : CollatzResearch.WordTrace tailWord_1406098 prefixEnd_1406098 240668040441914956269493 := by
  unfold tailWord_1406098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12821151814988640816198737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34189738173303042176529965 12821151814988640816198737)
  ·
    refine ⟨9615863861241480612149053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12821151814988640816198737 9615863861241480612149053)
    ·
      refine ⟨3605948947965555229555895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9615863861241480612149053 3605948947965555229555895)
      ·
        refine ⟨5408923421948332844333843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605948947965555229555895 5408923421948332844333843)
        ·
          refine ⟨8113385132922499266500765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5408923421948332844333843 8113385132922499266500765)
          ·
            refine ⟨3042519424845937224937787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8113385132922499266500765 3042519424845937224937787)
            ·
              refine ⟨4563779137268905837406681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042519424845937224937787 4563779137268905837406681)
              ·
                refine ⟨3422834352951679378055011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4563779137268905837406681 3422834352951679378055011)
                ·
                  refine ⟨5134251529427519067082517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422834352951679378055011 5134251529427519067082517)
                  ·
                    refine ⟨240668040441914956269493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5134251529427519067082517 240668040441914956269493)
                    ·
                      rfl

theorem cell23_1406098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_1406098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406098 prefixEnd_1406098 := by exact prefixLift 1406098
  have htrace : WordTrace (prefixWord ++ tailWord_1406098) baseStart_1406098 baseEnd_1406098 := by
    simpa [prefixWord, tailWord_1406098, baseEnd_1406098] using wordTrace_append hprefix tailTrace_1406098
  have hstable : (prefixWord ++ tailWord_1406098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406098).length < 2 ^ (prefixWord ++ tailWord_1406098).sum := by decide
  have hdescent : baseEnd_1406098 < baseStart_1406098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406108 : List Nat := [2, 2, 3, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1406108 : Nat := 118140960795 + 1406108 * 2 ^ 59
def prefixEnd_1406108 : Nat := 4983230072969 + 3 ^ 40 * 1406108 * 2
def baseEnd_1406108 : Nat := 722009256132289829683433

theorem tailTrace_1406108 : CollatzResearch.WordTrace tailWord_1406108 prefixEnd_1406108 722009256132289829683433 := by
  unfold tailWord_1406108
  simp only [CollatzResearch.WordTrace]
  refine ⟨25642485994959167486329489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34189981326612223315105985 25642485994959167486329489)
  ·
    refine ⟨19231864496219375614747117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25642485994959167486329489 19231864496219375614747117)
    ·
      refine ⟨7211949186082265855530169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19231864496219375614747117 7211949186082265855530169)
      ·
        refine ⟨5408961889561699391647627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7211949186082265855530169 5408961889561699391647627)
        ·
          refine ⟨8113442834342549087471441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5408961889561699391647627 8113442834342549087471441)
          ·
            refine ⟨6085082125756911815603581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8113442834342549087471441 6085082125756911815603581)
            ·
              refine ⟨2281905797158841930851343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6085082125756911815603581 2281905797158841930851343)
              ·
                refine ⟨3422858695738262896277015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281905797158841930851343 3422858695738262896277015)
                ·
                  refine ⟨5134288043607394344415523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422858695738262896277015 5134288043607394344415523)
                  ·
                    refine ⟨7701432065411091516623285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5134288043607394344415523 7701432065411091516623285)
                    ·
                      refine ⟨722009256132289829683433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7701432065411091516623285 722009256132289829683433)
                      ·
                        rfl

theorem cell23_1406108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1406108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406108 prefixEnd_1406108 := by exact prefixLift 1406108
  have htrace : WordTrace (prefixWord ++ tailWord_1406108) baseStart_1406108 baseEnd_1406108 := by
    simpa [prefixWord, tailWord_1406108, baseEnd_1406108] using wordTrace_append hprefix tailTrace_1406108
  have hstable : (prefixWord ++ tailWord_1406108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406108).length < 2 ^ (prefixWord ++ tailWord_1406108).sum := by decide
  have hdescent : baseEnd_1406108 < baseStart_1406108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406111 : List Nat := [1, 1, 2, 6, 2, 11]
def baseStart_1406111 : Nat := 118140960795 + 1406111 * 2 ^ 59
def prefixEnd_1406111 : Nat := 4983230072969 + 3 ^ 40 * 1406111 * 2
def baseEnd_1406111 : Nat := 2971237845984581555333

theorem tailTrace_1406111 : CollatzResearch.WordTrace tailWord_1406111 prefixEnd_1406111 2971237845984581555333 := by
  unfold tailWord_1406111
  simp only [CollatzResearch.WordTrace]
  refine ⟨51285081408907466485018187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34190054272604977656678791 51285081408907466485018187)
  ·
    refine ⟨76927622113361199727527281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51285081408907466485018187 76927622113361199727527281)
    ·
      refine ⟨57695716585020899795645461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76927622113361199727527281 57695716585020899795645461)
      ·
        refine ⟨2704486714922854677920881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57695716585020899795645461 2704486714922854677920881)
        ·
          refine ⟨2028365036192141008440661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2704486714922854677920881 2028365036192141008440661)
          ·
            refine ⟨2971237845984581555333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2028365036192141008440661 2971237845984581555333)
            ·
              rfl

theorem cell23_1406111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 11].length) (baseStart_1406111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406111 prefixEnd_1406111 := by exact prefixLift 1406111
  have htrace : WordTrace (prefixWord ++ tailWord_1406111) baseStart_1406111 baseEnd_1406111 := by
    simpa [prefixWord, tailWord_1406111, baseEnd_1406111] using wordTrace_append hprefix tailTrace_1406111
  have hstable : (prefixWord ++ tailWord_1406111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406111).length < 2 ^ (prefixWord ++ tailWord_1406111).sum := by decide
  have hdescent : baseEnd_1406111 < baseStart_1406111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406138 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3]
def baseStart_1406138 : Nat := 118140960795 + 1406138 * 2 ^ 59
def prefixEnd_1406138 : Nat := 4983230072969 + 3 ^ 40 * 1406138 * 2
def baseEnd_1406138 : Nat := 722024660551924712308295

theorem tailTrace_1406138 : CollatzResearch.WordTrace tailWord_1406138 prefixEnd_1406138 722024660551924712308295 := by
  unfold tailWord_1406138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12821516544952412524062767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34190710786539766730834045 12821516544952412524062767)
  ·
    refine ⟨19232274817428618786094151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12821516544952412524062767 19232274817428618786094151)
    ·
      refine ⟨28848412226142928179141227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19232274817428618786094151 28848412226142928179141227)
      ·
        refine ⟨43272618339214392268711841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28848412226142928179141227 43272618339214392268711841)
        ·
          refine ⟨32454463754410794201533881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43272618339214392268711841 32454463754410794201533881)
          ·
            refine ⟨24340847815808095651150411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32454463754410794201533881 24340847815808095651150411)
            ·
              refine ⟨36511271723712143476725617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24340847815808095651150411 36511271723712143476725617)
              ·
                refine ⟨27383453792784107607544213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36511271723712143476725617 27383453792784107607544213)
                ·
                  refine ⟨1283599396536755044103635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27383453792784107607544213 1283599396536755044103635)
                  ·
                    refine ⟨1925399094805132566155453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1283599396536755044103635 1925399094805132566155453)
                    ·
                      refine ⟨722024660551924712308295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1925399094805132566155453 722024660551924712308295)
                      ·
                        rfl

theorem cell23_1406138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_1406138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406138 prefixEnd_1406138 := by exact prefixLift 1406138
  have htrace : WordTrace (prefixWord ++ tailWord_1406138) baseStart_1406138 baseEnd_1406138 := by
    simpa [prefixWord, tailWord_1406138, baseEnd_1406138] using wordTrace_append hprefix tailTrace_1406138
  have hstable : (prefixWord ++ tailWord_1406138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406138).length < 2 ^ (prefixWord ++ tailWord_1406138).sum := by decide
  have hdescent : baseEnd_1406138 < baseStart_1406138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406145 : List Nat := [1, 2, 6, 1, 1, 2, 3, 7]
def baseStart_1406145 : Nat := 118140960795 + 1406145 * 2 ^ 59
def prefixEnd_1406145 : Nat := 4983230072969 + 3 ^ 40 * 1406145 * 2
def baseEnd_1406145 : Nat := 26741787219129858700769

theorem tailTrace_1406145 : CollatzResearch.WordTrace tailWord_1406145 prefixEnd_1406145 26741787219129858700769 := by
  unfold tailWord_1406145
  simp only [CollatzResearch.WordTrace]
  refine ⟨51286321490784290291755889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34190880993856193527837259 51286321490784290291755889)
  ·
    refine ⟨38464741118088217718816917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51286321490784290291755889 38464741118088217718816917)
    ·
      refine ⟨1803034739910385205569543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38464741118088217718816917 1803034739910385205569543)
      ·
        refine ⟨2704552109865577808354315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803034739910385205569543 2704552109865577808354315)
        ·
          refine ⟨4056828164798366712531473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704552109865577808354315 4056828164798366712531473)
          ·
            refine ⟨3042621123598775034398605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4056828164798366712531473 3042621123598775034398605)
            ·
              refine ⟨1140982921349540637899477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3042621123598775034398605 1140982921349540637899477)
              ·
                refine ⟨26741787219129858700769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1140982921349540637899477 26741787219129858700769)
                ·
                  rfl

theorem cell23_1406145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 7].length) (baseStart_1406145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406145 prefixEnd_1406145 := by exact prefixLift 1406145
  have htrace : WordTrace (prefixWord ++ tailWord_1406145) baseStart_1406145 baseEnd_1406145 := by
    simpa [prefixWord, tailWord_1406145, baseEnd_1406145] using wordTrace_append hprefix tailTrace_1406145
  have hstable : (prefixWord ++ tailWord_1406145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406145).length < 2 ^ (prefixWord ++ tailWord_1406145).sum := by decide
  have hdescent : baseEnd_1406145 < baseStart_1406145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406166 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1406166 : Nat := 118140960795 + 1406166 * 2 ^ 59
def prefixEnd_1406166 : Nat := 4983230072969 + 3 ^ 40 * 1406166 * 2
def baseEnd_1406166 : Nat := 240679679336750200919389

theorem tailTrace_1406166 : CollatzResearch.WordTrace tailWord_1406166 prefixEnd_1406166 240679679336750200919389 := by
  unfold tailWord_1406166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3205442963981763179891897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34191391615805473918846901 3205442963981763179891897)
  ·
    refine ⟨2404082222986322384918923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3205442963981763179891897 2404082222986322384918923)
    ·
      refine ⟨3606123334479483577378385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2404082222986322384918923 3606123334479483577378385)
      ·
        refine ⟨2704592500859612683033789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3606123334479483577378385 2704592500859612683033789)
        ·
          refine ⟨1014222187822354756137671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2704592500859612683033789 1014222187822354756137671)
          ·
            refine ⟨1521333281733532134206507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014222187822354756137671 1521333281733532134206507)
            ·
              refine ⟨2281999922600298201309761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521333281733532134206507 2281999922600298201309761)
              ·
                refine ⟨1711499941950223650982321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281999922600298201309761 1711499941950223650982321)
                ·
                  refine ⟨1283624956462667738236741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711499941950223650982321 1283624956462667738236741)
                  ·
                    refine ⟨240679679336750200919389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1283624956462667738236741 240679679336750200919389)
                    ·
                      rfl

theorem cell23_1406166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1406166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406166 prefixEnd_1406166 := by exact prefixLift 1406166
  have htrace : WordTrace (prefixWord ++ tailWord_1406166) baseStart_1406166 baseEnd_1406166 := by
    simpa [prefixWord, tailWord_1406166, baseEnd_1406166] using wordTrace_append hprefix tailTrace_1406166
  have hstable : (prefixWord ++ tailWord_1406166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406166).length < 2 ^ (prefixWord ++ tailWord_1406166).sum := by decide
  have hdescent : baseEnd_1406166 < baseStart_1406166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406189 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_1406189 : Nat := 118140960795 + 1406189 * 2 ^ 59
def prefixEnd_1406189 : Nat := 4983230072969 + 3 ^ 40 * 1406189 * 2
def baseEnd_1406189 : Nat := 722050848065304012770561

theorem tailTrace_1406189 : CollatzResearch.WordTrace tailWord_1406189 prefixEnd_1406189 722050848065304012770561 := by
  unfold tailWord_1406189
  simp only [CollatzResearch.WordTrace]
  refine ⟨51287926302624885806357621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34191950868416590537571747 51287926302624885806357621)
  ·
    refine ⟨4808243090871083044346027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51287926302624885806357621 4808243090871083044346027)
    ·
      refine ⟨7212364636306624566519041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4808243090871083044346027 7212364636306624566519041)
      ·
        refine ⟨5409273477229968424889281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7212364636306624566519041 5409273477229968424889281)
        ·
          refine ⟨4056955107922476318666961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5409273477229968424889281 4056955107922476318666961)
          ·
            refine ⟨3042716330941857239000221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4056955107922476318666961 3042716330941857239000221)
            ·
              refine ⟨1141018624103196464625083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3042716330941857239000221 1141018624103196464625083)
              ·
                refine ⟨1711527936154794696937625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141018624103196464625083 1711527936154794696937625)
                ·
                  refine ⟨1283645952116096022703219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1711527936154794696937625 1283645952116096022703219)
                  ·
                    refine ⟨1925468928174144034054829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1283645952116096022703219 1925468928174144034054829)
                    ·
                      refine ⟨722050848065304012770561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1925468928174144034054829 722050848065304012770561)
                      ·
                        rfl

theorem cell23_1406189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_1406189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406189 prefixEnd_1406189 := by exact prefixLift 1406189
  have htrace : WordTrace (prefixWord ++ tailWord_1406189) baseStart_1406189 baseEnd_1406189 := by
    simpa [prefixWord, tailWord_1406189, baseEnd_1406189] using wordTrace_append hprefix tailTrace_1406189
  have hstable : (prefixWord ++ tailWord_1406189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406189).length < 2 ^ (prefixWord ++ tailWord_1406189).sum := by decide
  have hdescent : baseEnd_1406189 < baseStart_1406189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406195 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 1, 4, 2]
def baseStart_1406195 : Nat := 118140960795 + 1406195 * 2 ^ 59
def prefixEnd_1406195 : Nat := 4983230072969 + 3 ^ 40 * 1406195 * 2
def baseEnd_1406195 : Nat := 722053928949230989295533

theorem tailTrace_1406195 : CollatzResearch.WordTrace tailWord_1406195 prefixEnd_1406195 722053928949230989295533 := by
  unfold tailWord_1406195
  simp only [CollatzResearch.WordTrace]
  refine ⟨51288145140603148831076039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34192096760402099220717359 51288145140603148831076039)
  ·
    refine ⟨76932217710904723246614059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51288145140603148831076039 76932217710904723246614059)
    ·
      refine ⟨115398326566357084869921089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76932217710904723246614059 115398326566357084869921089)
      ·
        refine ⟨86548744924767813652440817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115398326566357084869921089 86548744924767813652440817)
        ·
          refine ⟨64911558693575860239330613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86548744924767813652440817 64911558693575860239330613)
          ·
            refine ⟨6085458627522736897437245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64911558693575860239330613 6085458627522736897437245)
            ·
              refine ⟨2282046985321026336538967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6085458627522736897437245 2282046985321026336538967)
              ·
                refine ⟨3423070477981539504808451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282046985321026336538967 3423070477981539504808451)
                ·
                  refine ⟨5134605716972309257212677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423070477981539504808451 5134605716972309257212677)
                  ·
                    refine ⟨962738571932307985727377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5134605716972309257212677 962738571932307985727377)
                    ·
                      refine ⟨722053928949230989295533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962738571932307985727377 722053928949230989295533)
                      ·
                        rfl

theorem cell23_1406195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 4, 2].length) (baseStart_1406195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406195 prefixEnd_1406195 := by exact prefixLift 1406195
  have htrace : WordTrace (prefixWord ++ tailWord_1406195) baseStart_1406195 baseEnd_1406195 := by
    simpa [prefixWord, tailWord_1406195, baseEnd_1406195] using wordTrace_append hprefix tailTrace_1406195
  have hstable : (prefixWord ++ tailWord_1406195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406195).length < 2 ^ (prefixWord ++ tailWord_1406195).sum := by decide
  have hdescent : baseEnd_1406195 < baseStart_1406195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406196 : List Nat := [2, 6, 1, 2, 2, 1, 2, 7]
def baseStart_1406196 : Nat := 118140960795 + 1406196 * 2 ^ 59
def prefixEnd_1406196 : Nat := 4983230072969 + 3 ^ 40 * 1406196 * 2
def baseEnd_1406196 : Nat := 26742757127032795754927

theorem tailTrace_1406196 : CollatzResearch.WordTrace tailWord_1406196 prefixEnd_1406196 26742757127032795754927 := by
  unfold tailWord_1406196
  simp only [CollatzResearch.WordTrace]
  refine ⟨25644090806799763000931221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34192121075733017334574961 25644090806799763000931221)
  ·
    refine ⟨1202066756568738890668651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25644090806799763000931221 1202066756568738890668651)
    ·
      refine ⟨1803100134853108336002977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1202066756568738890668651 1803100134853108336002977)
      ·
        refine ⟨1352325101139831252002233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1803100134853108336002977 1352325101139831252002233)
        ·
          refine ⟨1014243825854873439001675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1352325101139831252002233 1014243825854873439001675)
          ·
            refine ⟨1521365738782310158502513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014243825854873439001675 1521365738782310158502513)
            ·
              refine ⟨1141024304086732618876885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1521365738782310158502513 1141024304086732618876885)
              ·
                refine ⟨26742757127032795754927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1141024304086732618876885 26742757127032795754927)
                ·
                  rfl

theorem cell23_1406196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 7].length) (baseStart_1406196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406196 prefixEnd_1406196 := by exact prefixLift 1406196
  have htrace : WordTrace (prefixWord ++ tailWord_1406196) baseStart_1406196 baseEnd_1406196 := by
    simpa [prefixWord, tailWord_1406196, baseEnd_1406196] using wordTrace_append hprefix tailTrace_1406196
  have hstable : (prefixWord ++ tailWord_1406196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406196).length < 2 ^ (prefixWord ++ tailWord_1406196).sum := by decide
  have hdescent : baseEnd_1406196 < baseStart_1406196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406198 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1406198 : Nat := 118140960795 + 1406198 * 2 ^ 59
def prefixEnd_1406198 : Nat := 4983230072969 + 3 ^ 40 * 1406198 * 2
def baseEnd_1406198 : Nat := 722055469391194477558019

theorem tailTrace_1406198 : CollatzResearch.WordTrace tailWord_1406198 prefixEnd_1406198 722055469391194477558019 := by
  unfold tailWord_1406198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3205515909974517521464703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34192169706394853562290165 3205515909974517521464703)
  ·
    refine ⟨4808273864961776282197055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3205515909974517521464703 4808273864961776282197055)
    ·
      refine ⟨7212410797442664423295583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4808273864961776282197055 7212410797442664423295583)
      ·
        refine ⟨10818616196163996634943375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7212410797442664423295583 10818616196163996634943375)
        ·
          refine ⟨16227924294245994952415063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10818616196163996634943375 16227924294245994952415063)
          ·
            refine ⟨24341886441368992428622595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16227924294245994952415063 24341886441368992428622595)
            ·
              refine ⟨36512829662053488642933893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24341886441368992428622595 36512829662053488642933893)
              ·
                refine ⟨6846155561635029120550105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36512829662053488642933893 6846155561635029120550105)
                ·
                  refine ⟨5134616671226271840412579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6846155561635029120550105 5134616671226271840412579)
                  ·
                    refine ⟨7701925006839407760618869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5134616671226271840412579 7701925006839407760618869)
                    ·
                      refine ⟨722055469391194477558019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7701925006839407760618869 722055469391194477558019)
                      ·
                        rfl

theorem cell23_1406198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1406198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406198 prefixEnd_1406198 := by exact prefixLift 1406198
  have htrace : WordTrace (prefixWord ++ tailWord_1406198) baseStart_1406198 baseEnd_1406198 := by
    simpa [prefixWord, tailWord_1406198, baseEnd_1406198] using wordTrace_append hprefix tailTrace_1406198
  have hstable : (prefixWord ++ tailWord_1406198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406198).length < 2 ^ (prefixWord ++ tailWord_1406198).sum := by decide
  have hdescent : baseEnd_1406198 < baseStart_1406198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406201 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 7]
def baseStart_1406201 : Nat := 118140960795 + 1406201 * 2 ^ 59
def prefixEnd_1406201 : Nat := 4983230072969 + 3 ^ 40 * 1406201 * 2
def baseEnd_1406201 : Nat := 80228556648128662868945

theorem tailTrace_1406201 : CollatzResearch.WordTrace tailWord_1406201 prefixEnd_1406201 80228556648128662868945 := by
  unfold tailWord_1406201
  simp only [CollatzResearch.WordTrace]
  refine ⟨51288363978581411855794457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34192242652387607903862971 51288363978581411855794457)
  ·
    refine ⟨38466272983936058891845843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51288363978581411855794457 38466272983936058891845843)
    ·
      refine ⟨57699409475904088337768765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38466272983936058891845843 57699409475904088337768765)
      ·
        refine ⟨21637278553464033126663287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57699409475904088337768765 21637278553464033126663287)
        ·
          refine ⟨32455917830196049689994931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21637278553464033126663287 32455917830196049689994931)
          ·
            refine ⟨48683876745294074534992397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32455917830196049689994931 48683876745294074534992397)
            ·
              refine ⟨18256453779485277950622149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48683876745294074534992397 18256453779485277950622149)
              ·
                refine ⟨3423085083653489615741653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18256453779485277950622149 3423085083653489615741653)
                ·
                  refine ⟨80228556648128662868945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3423085083653489615741653 80228556648128662868945)
                  ·
                    rfl

theorem cell23_1406201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 7].length) (baseStart_1406201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406201 prefixEnd_1406201 := by exact prefixLift 1406201
  have htrace : WordTrace (prefixWord ++ tailWord_1406201) baseStart_1406201 baseEnd_1406201 := by
    simpa [prefixWord, tailWord_1406201, baseEnd_1406201] using wordTrace_append hprefix tailTrace_1406201
  have hstable : (prefixWord ++ tailWord_1406201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406201).length < 2 ^ (prefixWord ++ tailWord_1406201).sum := by decide
  have hdescent : baseEnd_1406201 < baseStart_1406201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406212 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_1406212 : Nat := 118140960795 + 1406212 * 2 ^ 59
def prefixEnd_1406212 : Nat := 4983230072969 + 3 ^ 40 * 1406212 * 2
def baseEnd_1406212 : Nat := 722062658120357422782955

theorem tailTrace_1406212 : CollatzResearch.WordTrace tailWord_1406212 prefixEnd_1406212 722062658120357422782955 := by
  unfold tailWord_1406212
  simp only [CollatzResearch.WordTrace]
  refine ⟨25644382590770780367222445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34192510121027707156296593 25644382590770780367222445)
  ·
    refine ⟨9616643471539042637708417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25644382590770780367222445 9616643471539042637708417)
    ·
      refine ⟨7212482603654281978281313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9616643471539042637708417 7212482603654281978281313)
      ·
        refine ⟨5409361952740711483710985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7212482603654281978281313 5409361952740711483710985)
        ·
          refine ⟨4057021464555533612783239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5409361952740711483710985 4057021464555533612783239)
          ·
            refine ⟨6085532196833300419174859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4057021464555533612783239 6085532196833300419174859)
            ·
              refine ⟨9128298295249950628762289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6085532196833300419174859 9128298295249950628762289)
              ·
                refine ⟨6846223721437462971571717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9128298295249950628762289 6846223721437462971571717)
                ·
                  refine ⟨1283666947769524307169697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6846223721437462971571717 1283666947769524307169697)
                  ·
                    refine ⟨962750210827143230377273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1283666947769524307169697 962750210827143230377273)
                    ·
                      refine ⟨722062658120357422782955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962750210827143230377273 722062658120357422782955)
                      ·
                        rfl

theorem cell23_1406212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_1406212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406212 prefixEnd_1406212 := by exact prefixLift 1406212
  have htrace : WordTrace (prefixWord ++ tailWord_1406212) baseStart_1406212 baseEnd_1406212 := by
    simpa [prefixWord, tailWord_1406212, baseEnd_1406212] using wordTrace_append hprefix tailTrace_1406212
  have hstable : (prefixWord ++ tailWord_1406212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406212).length < 2 ^ (prefixWord ++ tailWord_1406212).sum := by decide
  have hdescent : baseEnd_1406212 < baseStart_1406212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406312 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 3, 4]
def baseStart_1406312 : Nat := 118140960795 + 1406312 * 2 ^ 59
def prefixEnd_1406312 : Nat := 4983230072969 + 3 ^ 40 * 1406312 * 2
def baseEnd_1406312 : Nat := 240704668728602343844165

theorem tailTrace_1406312 : CollatzResearch.WordTrace tailWord_1406312 prefixEnd_1406312 240704668728602343844165 := by
  unfold tailWord_1406312
  simp only [CollatzResearch.WordTrace]
  refine ⟨25646206240589638906542595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34194941654119518542056793 25646206240589638906542595)
  ·
    refine ⟨38469309360884458359813893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25646206240589638906542595 38469309360884458359813893)
    ·
      refine ⟨7212995505165835942465105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38469309360884458359813893 7212995505165835942465105)
      ·
        refine ⟨5409746628874376956848829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7212995505165835942465105 5409746628874376956848829)
        ·
          refine ⟨2028654985827891358818311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5409746628874376956848829 2028654985827891358818311)
          ·
            refine ⟨3042982478741837038227467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028654985827891358818311 3042982478741837038227467)
            ·
              refine ⟨4564473718112755557341201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042982478741837038227467 4564473718112755557341201)
              ·
                refine ⟨3423355288584566668005901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4564473718112755557341201 3423355288584566668005901)
                ·
                  refine ⟨1283758233219212500502213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3423355288584566668005901 1283758233219212500502213)
                  ·
                    refine ⟨240704668728602343844165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1283758233219212500502213 240704668728602343844165)
                    ·
                      rfl

theorem cell23_1406312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_1406312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406312 prefixEnd_1406312 := by exact prefixLift 1406312
  have htrace : WordTrace (prefixWord ++ tailWord_1406312) baseStart_1406312 baseEnd_1406312 := by
    simpa [prefixWord, tailWord_1406312, baseEnd_1406312] using wordTrace_append hprefix tailTrace_1406312
  have hstable : (prefixWord ++ tailWord_1406312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406312).length < 2 ^ (prefixWord ++ tailWord_1406312).sum := by decide
  have hdescent : baseEnd_1406312 < baseStart_1406312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406385 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 6, 4]
def baseStart_1406385 : Nat := 118140960795 + 1406385 * 2 ^ 59
def prefixEnd_1406385 : Nat := 4983230072969 + 3 ^ 40 * 1406385 * 2
def baseEnd_1406385 : Nat := 240717163424528415306553

theorem tailTrace_1406385 : CollatzResearch.WordTrace tailWord_1406385 prefixEnd_1406385 240717163424528415306553 := by
  unfold tailWord_1406385
  simp only [CollatzResearch.WordTrace]
  refine ⟨51295075009914811280492609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34196716673276540853661739 51295075009914811280492609)
  ·
    refine ⟨38471306257436108460369457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51295075009914811280492609 38471306257436108460369457)
    ·
      refine ⟨28853479693077081345277093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38471306257436108460369457 28853479693077081345277093)
      ·
        refine ⟨5410027442451952752239455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28853479693077081345277093 5410027442451952752239455)
        ·
          refine ⟨8115041163677929128359183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410027442451952752239455 8115041163677929128359183)
          ·
            refine ⟨12172561745516893692538775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8115041163677929128359183 12172561745516893692538775)
            ·
              refine ⟨18258842618275340538808163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12172561745516893692538775 18258842618275340538808163)
              ·
                refine ⟨27388263927413010808212245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18258842618275340538808163 27388263927413010808212245)
                ·
                  refine ⟨1283824871597484881634949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27388263927413010808212245 1283824871597484881634949)
                  ·
                    refine ⟨240717163424528415306553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1283824871597484881634949 240717163424528415306553)
                    ·
                      rfl

theorem cell23_1406385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_1406385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406385 prefixEnd_1406385 := by exact prefixLift 1406385
  have htrace : WordTrace (prefixWord ++ tailWord_1406385) baseStart_1406385 baseEnd_1406385 := by
    simpa [prefixWord, tailWord_1406385, baseEnd_1406385] using wordTrace_append hprefix tailTrace_1406385
  have hstable : (prefixWord ++ tailWord_1406385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406385).length < 2 ^ (prefixWord ++ tailWord_1406385).sum := by decide
  have hdescent : baseEnd_1406385 < baseStart_1406385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406392 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 5, 2, 2]
def baseStart_1406392 : Nat := 118140960795 + 1406392 * 2 ^ 59
def prefixEnd_1406392 : Nat := 4983230072969 + 3 ^ 40 * 1406392 * 2
def baseEnd_1406392 : Nat := 722155084638166718532127

theorem tailTrace_1406392 : CollatzResearch.WordTrace tailWord_1406392 prefixEnd_1406392 722155084638166718532127 := by
  unfold tailWord_1406392
  simp only [CollatzResearch.WordTrace]
  refine ⟨25647665160444725737998715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34196886880592967650664953 25647665160444725737998715)
  ·
    refine ⟨38471497740667088606998073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25647665160444725737998715 38471497740667088606998073)
    ·
      refine ⟨28853623305500316455248555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38471497740667088606998073 28853623305500316455248555)
      ·
        refine ⟨43280434958250474682872833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28853623305500316455248555 43280434958250474682872833)
        ·
          refine ⟨32460326218687856012154625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43280434958250474682872833 32460326218687856012154625)
          ·
            refine ⟨24345244664015892009115969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32460326218687856012154625 24345244664015892009115969)
            ·
              refine ⟨18258933498011919006836977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24345244664015892009115969 18258933498011919006836977)
              ·
                refine ⟨13694200123508939255127733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18258933498011919006836977 13694200123508939255127733)
                ·
                  refine ⟨1283831261578963055168225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13694200123508939255127733 1283831261578963055168225)
                  ·
                    refine ⟨962873446184222291376169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1283831261578963055168225 962873446184222291376169)
                    ·
                      refine ⟨722155084638166718532127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962873446184222291376169 722155084638166718532127)
                      ·
                        rfl

theorem cell23_1406392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_1406392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406392 prefixEnd_1406392 := by exact prefixLift 1406392
  have htrace : WordTrace (prefixWord ++ tailWord_1406392) baseStart_1406392 baseEnd_1406392 := by
    simpa [prefixWord, tailWord_1406392, baseEnd_1406392] using wordTrace_append hprefix tailTrace_1406392
  have hstable : (prefixWord ++ tailWord_1406392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406392).length < 2 ^ (prefixWord ++ tailWord_1406392).sum := by decide
  have hdescent : baseEnd_1406392 < baseStart_1406392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406422 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1406422 : Nat := 118140960795 + 1406422 * 2 ^ 59
def prefixEnd_1406422 : Nat := 4983230072969 + 3 ^ 40 * 1406422 * 2
def baseEnd_1406422 : Nat := 722170489057801601156989

theorem tailTrace_1406422 : CollatzResearch.WordTrace tailWord_1406422 prefixEnd_1406422 722170489057801601156989 := by
  unfold tailWord_1406422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3206026531923797912474345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34197616340520511066393013 3206026531923797912474345)
  ·
    refine ⟨2404519898942848434355759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3206026531923797912474345 2404519898942848434355759)
    ·
      refine ⟨3606779848414272651533639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2404519898942848434355759 3606779848414272651533639)
      ·
        refine ⟨5410169772621408977300459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3606779848414272651533639 5410169772621408977300459)
        ·
          refine ⟨8115254658932113465950689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410169772621408977300459 8115254658932113465950689)
          ·
            refine ⟨6086440994199085099463017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8115254658932113465950689 6086440994199085099463017)
            ·
              refine ⟨4564830745649313824597263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6086440994199085099463017 4564830745649313824597263)
              ·
                refine ⟨6847246118473970736895895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4564830745649313824597263 6847246118473970736895895)
                ·
                  refine ⟨10270869177710956105343843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6847246118473970736895895 10270869177710956105343843)
                  ·
                    refine ⟨15406303766566434158015765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10270869177710956105343843 15406303766566434158015765)
                    ·
                      refine ⟨722170489057801601156989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15406303766566434158015765 722170489057801601156989)
                      ·
                        rfl

theorem cell23_1406422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1406422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406422 prefixEnd_1406422 := by exact prefixLift 1406422
  have htrace : WordTrace (prefixWord ++ tailWord_1406422) baseStart_1406422 baseEnd_1406422 := by
    simpa [prefixWord, tailWord_1406422, baseEnd_1406422] using wordTrace_append hprefix tailTrace_1406422
  have hstable : (prefixWord ++ tailWord_1406422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406422).length < 2 ^ (prefixWord ++ tailWord_1406422).sum := by decide
  have hdescent : baseEnd_1406422 < baseStart_1406422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406429 : List Nat := [1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_1406429 : Nat := 118140960795 + 1406429 * 2 ^ 59
def prefixEnd_1406429 : Nat := 4983230072969 + 3 ^ 40 * 1406429 * 2
def baseEnd_1406429 : Nat := 722174083422383073769457

theorem tailTrace_1406429 : CollatzResearch.WordTrace tailWord_1406429 prefixEnd_1406429 722174083422383073769457 := by
  unfold tailWord_1406429
  simp only [CollatzResearch.WordTrace]
  refine ⟨51296679821755406795094341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34197786547836937863396227 51296679821755406795094341)
  ·
    refine ⟨9618127466579138774080189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51296679821755406795094341 9618127466579138774080189)
    ·
      refine ⟨3606797799967177040280071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9618127466579138774080189 3606797799967177040280071)
      ·
        refine ⟨5410196699950765560420107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3606797799967177040280071 5410196699950765560420107)
        ·
          refine ⟨8115295049926148340630161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410196699950765560420107 8115295049926148340630161)
          ·
            refine ⟨6086471287444611255472621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8115295049926148340630161 6086471287444611255472621)
            ·
              refine ⟨2282426732791729220802233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6086471287444611255472621 2282426732791729220802233)
              ·
                refine ⟨1711820049593796915601675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2282426732791729220802233 1711820049593796915601675)
                ·
                  refine ⟨2567730074390695373402513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711820049593796915601675 2567730074390695373402513)
                  ·
                    refine ⟨1925797555793021530051885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2567730074390695373402513 1925797555793021530051885)
                    ·
                      refine ⟨722174083422383073769457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1925797555793021530051885 722174083422383073769457)
                      ·
                        rfl

theorem cell23_1406429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_1406429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406429 prefixEnd_1406429 := by exact prefixLift 1406429
  have htrace : WordTrace (prefixWord ++ tailWord_1406429) baseStart_1406429 baseEnd_1406429 := by
    simpa [prefixWord, tailWord_1406429, baseEnd_1406429] using wordTrace_append hprefix tailTrace_1406429
  have hstable : (prefixWord ++ tailWord_1406429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406429).length < 2 ^ (prefixWord ++ tailWord_1406429).sum := by decide
  have hdescent : baseEnd_1406429 < baseStart_1406429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406494 : List Nat := [4, 3, 3, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1406494 : Nat := 118140960795 + 1406494 * 2 ^ 59
def prefixEnd_1406494 : Nat := 4983230072969 + 3 ^ 40 * 1406494 * 2
def baseEnd_1406494 : Nat := 722207459664925319456659

theorem tailTrace_1406494 : CollatzResearch.WordTrace tailWord_1406494 prefixEnd_1406494 722207459664925319456659 := by
  unfold tailWord_1406494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412381320814990362026317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34199367044346615264140357 6412381320814990362026317)
  ·
    refine ⟨2404642995305621385759869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6412381320814990362026317 2404642995305621385759869)
    ·
      refine ⟨901741123239608019659951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2404642995305621385759869 901741123239608019659951)
      ·
        refine ⟨1352611684859412029489927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901741123239608019659951 1352611684859412029489927)
        ·
          refine ⟨2028917527289118044234891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352611684859412029489927 2028917527289118044234891)
          ·
            refine ⟨3043376290933677066352337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028917527289118044234891 3043376290933677066352337)
            ·
              refine ⟨2282532218200257799764253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3043376290933677066352337 2282532218200257799764253)
              ·
                refine ⟨855949581825096674911595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2282532218200257799764253 855949581825096674911595)
                ·
                  refine ⟨1283924372737645012367393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 855949581825096674911595 1283924372737645012367393)
                  ·
                    refine ⟨962943279553233759275545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1283924372737645012367393 962943279553233759275545)
                    ·
                      refine ⟨722207459664925319456659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 962943279553233759275545 722207459664925319456659)
                      ·
                        rfl

theorem cell23_1406494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1406494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406494 prefixEnd_1406494 := by exact prefixLift 1406494
  have htrace : WordTrace (prefixWord ++ tailWord_1406494) baseStart_1406494 baseEnd_1406494 := by
    simpa [prefixWord, tailWord_1406494, baseEnd_1406494] using wordTrace_append hprefix tailTrace_1406494
  have hstable : (prefixWord ++ tailWord_1406494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406494).length < 2 ^ (prefixWord ++ tailWord_1406494).sum := by decide
  have hdescent : baseEnd_1406494 < baseStart_1406494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406522 : List Nat := [3, 1, 1, 1, 3, 2, 1, 6, 5]
def baseStart_1406522 : Nat := 118140960795 + 1406522 * 2 ^ 59
def prefixEnd_1406522 : Nat := 4983230072969 + 3 ^ 40 * 1406522 * 2
def baseEnd_1406522 : Nat := 80246870791472356656281

theorem tailTrace_1406522 : CollatzResearch.WordTrace tailWord_1406522 prefixEnd_1406522 80246870791472356656281 := by
  unfold tailWord_1406522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12825017952604620919557455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34200047873612322452153213 12825017952604620919557455)
  ·
    refine ⟨19237526928906931379336183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12825017952604620919557455 19237526928906931379336183)
    ·
      refine ⟨28856290393360397069004275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19237526928906931379336183 28856290393360397069004275)
      ·
        refine ⟨43284435590040595603506413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28856290393360397069004275 43284435590040595603506413)
        ·
          refine ⟨16231663346265223351314905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43284435590040595603506413 16231663346265223351314905)
          ·
            refine ⟨12173747509698917513486179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16231663346265223351314905 12173747509698917513486179)
            ·
              refine ⟨18260621264548376270229269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12173747509698917513486179 18260621264548376270229269)
              ·
                refine ⟨855966621775705137666997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18260621264548376270229269 855966621775705137666997)
                ·
                  refine ⟨80246870791472356656281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 855966621775705137666997 80246870791472356656281)
                  ·
                    rfl

theorem cell23_1406522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_1406522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406522 prefixEnd_1406522 := by exact prefixLift 1406522
  have htrace : WordTrace (prefixWord ++ tailWord_1406522) baseStart_1406522 baseEnd_1406522 := by
    simpa [prefixWord, tailWord_1406522, baseEnd_1406522] using wordTrace_append hprefix tailTrace_1406522
  have hstable : (prefixWord ++ tailWord_1406522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406522).length < 2 ^ (prefixWord ++ tailWord_1406522).sum := by decide
  have hdescent : baseEnd_1406522 < baseStart_1406522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406556 : List Nat := [2, 2, 4, 1, 2, 3, 1, 3, 5]
def baseStart_1406556 : Nat := 118140960795 + 1406556 * 2 ^ 59
def prefixEnd_1406556 : Nat := 4983230072969 + 3 ^ 40 * 1406556 * 2
def baseEnd_1406556 : Nat := 80248810607278230764597

theorem tailTrace_1406556 : CollatzResearch.WordTrace tailWord_1406556 prefixEnd_1406556 80248810607278230764597 := by
  unfold tailWord_1406556
  simp only [CollatzResearch.WordTrace]
  refine ⟨25650655946147653742483761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34200874594863538323311681 25650655946147653742483761)
  ·
    refine ⟨19237991959610740306862821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25650655946147653742483761 19237991959610740306862821)
    ·
      refine ⟨3607123492427013807536779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19237991959610740306862821 3607123492427013807536779)
      ·
        refine ⟨5410685238640520711305169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607123492427013807536779 5410685238640520711305169)
        ·
          refine ⟨4058013928980390533478877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5410685238640520711305169 4058013928980390533478877)
          ·
            refine ⟨1521755223367646450054579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4058013928980390533478877 1521755223367646450054579)
            ·
              refine ⟨2282632835051469675081869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1521755223367646450054579 2282632835051469675081869)
              ·
                refine ⟨855987313144301128155701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2282632835051469675081869 855987313144301128155701)
                ·
                  refine ⟨80248810607278230764597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 855987313144301128155701 80248810607278230764597)
                  ·
                    rfl

theorem cell23_1406556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_1406556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406556 prefixEnd_1406556 := by exact prefixLift 1406556
  have htrace : WordTrace (prefixWord ++ tailWord_1406556) baseStart_1406556 baseEnd_1406556 := by
    simpa [prefixWord, tailWord_1406556, baseEnd_1406556] using wordTrace_append hprefix tailTrace_1406556
  have hstable : (prefixWord ++ tailWord_1406556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406556).length < 2 ^ (prefixWord ++ tailWord_1406556).sum := by decide
  have hdescent : baseEnd_1406556 < baseStart_1406556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406592 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 3]
def baseStart_1406592 : Nat := 118140960795 + 1406592 * 2 ^ 59
def prefixEnd_1406592 : Nat := 4983230072969 + 3 ^ 40 * 1406592 * 2
def baseEnd_1406592 : Nat := 722257780769065936031207

theorem tailTrace_1406592 : CollatzResearch.WordTrace tailWord_1406592 prefixEnd_1406592 722257780769065936031207 := by
  unfold tailWord_1406592
  simp only [CollatzResearch.WordTrace]
  refine ⟨25651312460082442816639015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34201749946776590422185353 25651312460082442816639015)
  ·
    refine ⟨38476968690123664224958523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25651312460082442816639015 38476968690123664224958523)
    ·
      refine ⟨57715453035185496337437785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38476968690123664224958523 57715453035185496337437785)
      ·
        refine ⟨43286589776389122253078339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57715453035185496337437785 43286589776389122253078339)
        ·
          refine ⟨64929884664583683379617509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43286589776389122253078339 64929884664583683379617509)
          ·
            refine ⟨12174353374609440633678283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64929884664583683379617509 12174353374609440633678283)
            ·
              refine ⟨18261530061914160950517425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12174353374609440633678283 18261530061914160950517425)
              ·
                refine ⟨13696147546435620712888069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18261530061914160950517425 13696147546435620712888069)
                ·
                  refine ⟨2568027664956678883666513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13696147546435620712888069 2568027664956678883666513)
                  ·
                    refine ⟨1926020748717509162749885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2568027664956678883666513 1926020748717509162749885)
                    ·
                      refine ⟨722257780769065936031207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1926020748717509162749885 722257780769065936031207)
                      ·
                        rfl

theorem cell23_1406592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_1406592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406592 prefixEnd_1406592 := by exact prefixLift 1406592
  have htrace : WordTrace (prefixWord ++ tailWord_1406592) baseStart_1406592 baseEnd_1406592 := by
    simpa [prefixWord, tailWord_1406592, baseEnd_1406592] using wordTrace_append hprefix tailTrace_1406592
  have hstable : (prefixWord ++ tailWord_1406592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406592).length < 2 ^ (prefixWord ++ tailWord_1406592).sum := by decide
  have hdescent : baseEnd_1406592 < baseStart_1406592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406639 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 3]
def baseStart_1406639 : Nat := 118140960795 + 1406639 * 2 ^ 59
def prefixEnd_1406639 : Nat := 4983230072969 + 3 ^ 40 * 1406639 * 2
def baseEnd_1406639 : Nat := 722281914359827252143491

theorem tailTrace_1406639 : CollatzResearch.WordTrace tailWord_1406639 prefixEnd_1406639 722281914359827252143491 := by
  unfold tailWord_1406639
  simp only [CollatzResearch.WordTrace]
  refine ⟨51304339150994612660238971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34202892767329741773492647 51304339150994612660238971)
  ·
    refine ⟨76956508726491918990358457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51304339150994612660238971 76956508726491918990358457)
    ·
      refine ⟨57717381544868939242768843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76956508726491918990358457 57717381544868939242768843)
      ·
        refine ⟨86576072317303408864153265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57717381544868939242768843 86576072317303408864153265)
        ·
          refine ⟨64932054237977556648114949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86576072317303408864153265 64932054237977556648114949)
          ·
            refine ⟨12174760169620791871521553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64932054237977556648114949 12174760169620791871521553)
            ·
              refine ⟨9131070127215593903641165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12174760169620791871521553 9131070127215593903641165)
              ·
                refine ⟨3424151297705847713865437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9131070127215593903641165 3424151297705847713865437)
                ·
                  refine ⟨1284056736639692892699539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3424151297705847713865437 1284056736639692892699539)
                  ·
                    refine ⟨1926085104959539339049309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1284056736639692892699539 1926085104959539339049309)
                    ·
                      refine ⟨722281914359827252143491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1926085104959539339049309 722281914359827252143491)
                      ·
                        rfl

theorem cell23_1406639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 3].length) (baseStart_1406639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406639 prefixEnd_1406639 := by exact prefixLift 1406639
  have htrace : WordTrace (prefixWord ++ tailWord_1406639) baseStart_1406639 baseEnd_1406639 := by
    simpa [prefixWord, tailWord_1406639, baseEnd_1406639] using wordTrace_append hprefix tailTrace_1406639
  have hstable : (prefixWord ++ tailWord_1406639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406639).length < 2 ^ (prefixWord ++ tailWord_1406639).sum := by decide
  have hdescent : baseEnd_1406639 < baseStart_1406639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406642 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_1406642 : Nat := 118140960795 + 1406642 * 2 ^ 59
def prefixEnd_1406642 : Nat := 4983230072969 + 3 ^ 40 * 1406642 * 2
def baseEnd_1406642 : Nat := 240761151600596913468659

theorem tailTrace_1406642 : CollatzResearch.WordTrace tailWord_1406642 prefixEnd_1406642 240761151600596913468659 := by
  unfold tailWord_1406642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12826112142495936043149545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34202965713322496115065453 12826112142495936043149545)
  ·
    refine ⟨9619584106871952032362159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12826112142495936043149545 9619584106871952032362159)
    ·
      refine ⟨14429376160307928048543239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9619584106871952032362159 14429376160307928048543239)
      ·
        refine ⟨21644064240461892072814859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14429376160307928048543239 21644064240461892072814859)
        ·
          refine ⟨32466096360692838109222289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21644064240461892072814859 32466096360692838109222289)
          ·
            refine ⟨24349572270519628581916717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32466096360692838109222289 24349572270519628581916717)
            ·
              refine ⟨9131089601444860718218769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24349572270519628581916717 9131089601444860718218769)
              ·
                refine ⟨6848317201083645538664077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9131089601444860718218769 6848317201083645538664077)
                ·
                  refine ⟨2568118950406367076999029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6848317201083645538664077 2568118950406367076999029)
                  ·
                    refine ⟨240761151600596913468659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2568118950406367076999029 240761151600596913468659)
                    ·
                      rfl

theorem cell23_1406642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_1406642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406642 prefixEnd_1406642 := by exact prefixLift 1406642
  have htrace : WordTrace (prefixWord ++ tailWord_1406642) baseStart_1406642 baseEnd_1406642 := by
    simpa [prefixWord, tailWord_1406642, baseEnd_1406642] using wordTrace_append hprefix tailTrace_1406642
  have hstable : (prefixWord ++ tailWord_1406642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406642).length < 2 ^ (prefixWord ++ tailWord_1406642).sum := by decide
  have hdescent : baseEnd_1406642 < baseStart_1406642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406646 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_1406646 : Nat := 118140960795 + 1406646 * 2 ^ 59
def prefixEnd_1406646 : Nat := 4983230072969 + 3 ^ 40 * 1406646 * 2
def baseEnd_1406646 : Nat := 80253945413823191639551

theorem tailTrace_1406646 : CollatzResearch.WordTrace tailWord_1406646 prefixEnd_1406646 80253945413823191639551 := by
  unfold tailWord_1406646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3206537153873078303483987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34203062974646168570495861 3206537153873078303483987)
  ·
    refine ⟨4809805730809617455225981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3206537153873078303483987 4809805730809617455225981)
    ·
      refine ⟨1803677149053606545709743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4809805730809617455225981 1803677149053606545709743)
      ·
        refine ⟨2705515723580409818564615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803677149053606545709743 2705515723580409818564615)
        ·
          refine ⟨4058273585370614727846923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705515723580409818564615 4058273585370614727846923)
          ·
            refine ⟨6087410378055922091770385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058273585370614727846923 6087410378055922091770385)
            ·
              refine ⟨4565557783541941568827789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087410378055922091770385 4565557783541941568827789)
              ·
                refine ⟨1712084168828228088310421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4565557783541941568827789 1712084168828228088310421)
                ·
                  refine ⟨80253945413823191639551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1712084168828228088310421 80253945413823191639551)
                  ·
                    rfl

theorem cell23_1406646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_1406646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406646 prefixEnd_1406646 := by exact prefixLift 1406646
  have htrace : WordTrace (prefixWord ++ tailWord_1406646) baseStart_1406646 baseEnd_1406646 := by
    simpa [prefixWord, tailWord_1406646, baseEnd_1406646] using wordTrace_append hprefix tailTrace_1406646
  have hstable : (prefixWord ++ tailWord_1406646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406646).length < 2 ^ (prefixWord ++ tailWord_1406646).sum := by decide
  have hdescent : baseEnd_1406646 < baseStart_1406646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406649 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 4, 3, 2]
def baseStart_1406649 : Nat := 118140960795 + 1406649 * 2 ^ 59
def prefixEnd_1406649 : Nat := 4983230072969 + 3 ^ 40 * 1406649 * 2
def baseEnd_1406649 : Nat := 722287049166372213018445

theorem tailTrace_1406649 : CollatzResearch.WordTrace tailWord_1406649 prefixEnd_1406649 722287049166372213018445 := by
  unfold tailWord_1406649
  simp only [CollatzResearch.WordTrace]
  refine ⟨51304703880958384368103001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34203135920638922912068667 51304703880958384368103001)
  ·
    refine ⟨38478527910718788276077251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51304703880958384368103001 38478527910718788276077251)
    ·
      refine ⟨57717791866078182414115877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38478527910718788276077251 57717791866078182414115877)
      ·
        refine ⟨10822085974889659202646727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57717791866078182414115877 10822085974889659202646727)
        ·
          refine ⟨16233128962334488803970091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10822085974889659202646727 16233128962334488803970091)
          ·
            refine ⟨24349693443501733205955137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16233128962334488803970091 24349693443501733205955137)
            ·
              refine ⟨18262270082626299904466353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24349693443501733205955137 18262270082626299904466353)
              ·
                refine ⟨13696702561969724928349765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18262270082626299904466353 13696702561969724928349765)
                ·
                  refine ⟨2568131730369323424065581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13696702561969724928349765 2568131730369323424065581)
                  ·
                    refine ⟨963049398888496284024593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568131730369323424065581 963049398888496284024593)
                    ·
                      refine ⟨722287049166372213018445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963049398888496284024593 722287049166372213018445)
                      ·
                        rfl

theorem cell23_1406649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_1406649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406649 prefixEnd_1406649 := by exact prefixLift 1406649
  have htrace : WordTrace (prefixWord ++ tailWord_1406649) baseStart_1406649 baseEnd_1406649 := by
    simpa [prefixWord, tailWord_1406649, baseEnd_1406649] using wordTrace_append hprefix tailTrace_1406649
  have hstable : (prefixWord ++ tailWord_1406649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406649).length < 2 ^ (prefixWord ++ tailWord_1406649).sum := by decide
  have hdescent : baseEnd_1406649 < baseStart_1406649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406666 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_1406666 : Nat := 118140960795 + 1406666 * 2 ^ 59
def prefixEnd_1406666 : Nat := 4983230072969 + 3 ^ 40 * 1406666 * 2
def baseEnd_1406666 : Nat := 722295778337498646505867

theorem tailTrace_1406666 : CollatzResearch.WordTrace tailWord_1406666 prefixEnd_1406666 722295778337498646505867 := by
  unfold tailWord_1406666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12826330980474199067867963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34203549281264530847647901 12826330980474199067867963)
  ·
    refine ⟨19239496470711298601801945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12826330980474199067867963 19239496470711298601801945)
    ·
      refine ⟨14429622353033473951351459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19239496470711298601801945 14429622353033473951351459)
      ·
        refine ⟨21644433529550210927027189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14429622353033473951351459 21644433529550210927027189)
        ·
          refine ⟨2029165643395332274408799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21644433529550210927027189 2029165643395332274408799)
          ·
            refine ⟨3043748465092998411613199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029165643395332274408799 3043748465092998411613199)
            ·
              refine ⟨4565622697639497617419799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043748465092998411613199 4565622697639497617419799)
              ·
                refine ⟨6848434046459246426129699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565622697639497617419799 6848434046459246426129699)
                ·
                  refine ⟨10272651069688869639194549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6848434046459246426129699 10272651069688869639194549)
                  ·
                    refine ⟨963061037783331528674489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10272651069688869639194549 963061037783331528674489)
                    ·
                      refine ⟨722295778337498646505867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963061037783331528674489 722295778337498646505867)
                      ·
                        rfl

theorem cell23_1406666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_1406666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406666 prefixEnd_1406666 := by exact prefixLift 1406666
  have htrace : WordTrace (prefixWord ++ tailWord_1406666) baseStart_1406666 baseEnd_1406666 := by
    simpa [prefixWord, tailWord_1406666, baseEnd_1406666] using wordTrace_append hprefix tailTrace_1406666
  have hstable : (prefixWord ++ tailWord_1406666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406666).length < 2 ^ (prefixWord ++ tailWord_1406666).sum := by decide
  have hdescent : baseEnd_1406666 < baseStart_1406666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406673 : List Nat := [1, 2, 2, 1, 2, 5, 2, 3, 1, 1, 3]
def baseStart_1406673 : Nat := 118140960795 + 1406673 * 2 ^ 59
def prefixEnd_1406673 : Nat := 4983230072969 + 3 ^ 40 * 1406673 * 2
def baseEnd_1406673 : Nat := 722299372702080119118335

theorem tailTrace_1406673 : CollatzResearch.WordTrace tailWord_1406673 prefixEnd_1406673 722299372702080119118335 := by
  unfold tailWord_1406673
  simp only [CollatzResearch.WordTrace]
  refine ⟨51305579232871436466976673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34203719488580957644651115 51305579232871436466976673)
  ·
    refine ⟨38479184424653577350232505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51305579232871436466976673 38479184424653577350232505)
    ·
      refine ⟨28859388318490183012674379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38479184424653577350232505 28859388318490183012674379)
      ·
        refine ⟨43289082477735274519011569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28859388318490183012674379 43289082477735274519011569)
        ·
          refine ⟨32466811858301455889258677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43289082477735274519011569 32466811858301455889258677)
          ·
            refine ⟨3043763611715761489618001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32466811858301455889258677 3043763611715761489618001)
            ·
              refine ⟨2282822708786821117213501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3043763611715761489618001 2282822708786821117213501)
              ·
                refine ⟨856058515795057918955063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2282822708786821117213501 856058515795057918955063)
                ·
                  refine ⟨1284087773692586878432595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856058515795057918955063 1284087773692586878432595)
                  ·
                    refine ⟨1926131660538880317648893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1284087773692586878432595 1926131660538880317648893)
                    ·
                      refine ⟨722299372702080119118335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1926131660538880317648893 722299372702080119118335)
                      ·
                        rfl

theorem cell23_1406673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 1, 3].length) (baseStart_1406673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406673 prefixEnd_1406673 := by exact prefixLift 1406673
  have htrace : WordTrace (prefixWord ++ tailWord_1406673) baseStart_1406673 baseEnd_1406673 := by
    simpa [prefixWord, tailWord_1406673, baseEnd_1406673] using wordTrace_append hprefix tailTrace_1406673
  have hstable : (prefixWord ++ tailWord_1406673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406673).length < 2 ^ (prefixWord ++ tailWord_1406673).sum := by decide
  have hdescent : baseEnd_1406673 < baseStart_1406673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406676 : List Nat := [2, 4, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_1406676 : Nat := 118140960795 + 1406676 * 2 ^ 59
def prefixEnd_1406676 : Nat := 4983230072969 + 3 ^ 40 * 1406676 * 2
def baseEnd_1406676 : Nat := 240766971048014535793607

theorem tailTrace_1406676 : CollatzResearch.WordTrace tailWord_1406676 prefixEnd_1406676 240766971048014535793607 := by
  unfold tailWord_1406676
  simp only [CollatzResearch.WordTrace]
  refine ⟨25652844325930283989667941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34203792434573711986223921 25652844325930283989667941)
  ·
    refine ⟨4809908311111928248062739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25652844325930283989667941 4809908311111928248062739)
    ·
      refine ⟨7214862466667892372094109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4809908311111928248062739 7214862466667892372094109)
      ·
        refine ⟨2705573425000459639535291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7214862466667892372094109 2705573425000459639535291)
        ·
          refine ⟨4058360137500689459302937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705573425000459639535291 4058360137500689459302937)
          ·
            refine ⟨3043770103125517094477203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4058360137500689459302937 3043770103125517094477203)
            ·
              refine ⟨4565655154688275641715805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043770103125517094477203 4565655154688275641715805)
              ·
                refine ⟨1712120683008103365643427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4565655154688275641715805 1712120683008103365643427)
                ·
                  refine ⟨2568181024512155048465141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712120683008103365643427 2568181024512155048465141)
                  ·
                    refine ⟨240766971048014535793607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2568181024512155048465141 240766971048014535793607)
                    ·
                      rfl

theorem cell23_1406676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_1406676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406676 prefixEnd_1406676 := by exact prefixLift 1406676
  have htrace : WordTrace (prefixWord ++ tailWord_1406676) baseStart_1406676 baseEnd_1406676 := by
    simpa [prefixWord, tailWord_1406676, baseEnd_1406676] using wordTrace_append hprefix tailTrace_1406676
  have hstable : (prefixWord ++ tailWord_1406676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406676).length < 2 ^ (prefixWord ++ tailWord_1406676).sum := by decide
  have hdescent : baseEnd_1406676 < baseStart_1406676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406679 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 4]
def baseStart_1406679 : Nat := 118140960795 + 1406679 * 2 ^ 59
def prefixEnd_1406679 : Nat := 4983230072969 + 3 ^ 40 * 1406679 * 2
def baseEnd_1406679 : Nat := 722302453586007095643307

theorem tailTrace_1406679 : CollatzResearch.WordTrace tailWord_1406679 prefixEnd_1406679 722302453586007095643307 := by
  unfold tailWord_1406679
  simp only [CollatzResearch.WordTrace]
  refine ⟨51305798070849699491695091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34203865380566466327796727 51305798070849699491695091)
  ·
    refine ⟨76958697106274549237542637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51305798070849699491695091 76958697106274549237542637)
    ·
      refine ⟨28859511414852955964078489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76958697106274549237542637 28859511414852955964078489)
      ·
        refine ⟨21644633561139716973058867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28859511414852955964078489 21644633561139716973058867)
        ·
          refine ⟨32466950341709575459588301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21644633561139716973058867 32466950341709575459588301)
          ·
            refine ⟨12175106378141090797345613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32466950341709575459588301 12175106378141090797345613)
            ·
              refine ⟨4565664891802909049004605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12175106378141090797345613 4565664891802909049004605)
              ·
                refine ⟨1712124334426090893376727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4565664891802909049004605 1712124334426090893376727)
                ·
                  refine ⟨2568186501639136340065091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712124334426090893376727 2568186501639136340065091)
                  ·
                    refine ⟨3852279752458704510097637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568186501639136340065091 3852279752458704510097637)
                    ·
                      refine ⟨722302453586007095643307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3852279752458704510097637 722302453586007095643307)
                      ·
                        rfl

theorem cell23_1406679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_1406679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406679 prefixEnd_1406679 := by exact prefixLift 1406679
  have htrace : WordTrace (prefixWord ++ tailWord_1406679) baseStart_1406679 baseEnd_1406679 := by
    simpa [prefixWord, tailWord_1406679, baseEnd_1406679] using wordTrace_append hprefix tailTrace_1406679
  have hstable : (prefixWord ++ tailWord_1406679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406679).length < 2 ^ (prefixWord ++ tailWord_1406679).sum := by decide
  have hdescent : baseEnd_1406679 < baseStart_1406679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406692 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_1406692 : Nat := 118140960795 + 1406692 * 2 ^ 59
def prefixEnd_1406692 : Nat := 4983230072969 + 3 ^ 40 * 1406692 * 2
def baseEnd_1406692 : Nat := 722309128834515544780747

theorem tailTrace_1406692 : CollatzResearch.WordTrace tailWord_1406692 prefixEnd_1406692 722309128834515544780747 := by
  unfold tailWord_1406692
  simp only [CollatzResearch.WordTrace]
  refine ⟨25653136109901301355959165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34204181479868401807945553 25653136109901301355959165)
  ·
    refine ⟨9619926041212988008484687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25653136109901301355959165 9619926041212988008484687)
    ·
      refine ⟨14429889061819482012727031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9619926041212988008484687 14429889061819482012727031)
      ·
        refine ⟨21644833592729223019090547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14429889061819482012727031 21644833592729223019090547)
        ·
          refine ⟨32467250389093834528635821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21644833592729223019090547 32467250389093834528635821)
          ·
            refine ⟨12175218895910187948238433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32467250389093834528635821 12175218895910187948238433)
            ·
              refine ⟨9131414171932640961178825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12175218895910187948238433 9131414171932640961178825)
              ·
                refine ⟨6848560628949480720884119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9131414171932640961178825 6848560628949480720884119)
                ·
                  refine ⟨10272840943424221081326179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6848560628949480720884119 10272840943424221081326179)
                  ·
                    refine ⟨15409261415136331621989269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10272840943424221081326179 15409261415136331621989269)
                    ·
                      refine ⟨722309128834515544780747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15409261415136331621989269 722309128834515544780747)
                      ·
                        rfl

theorem cell23_1406692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_1406692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406692 prefixEnd_1406692 := by exact prefixLift 1406692
  have htrace : WordTrace (prefixWord ++ tailWord_1406692) baseStart_1406692 baseEnd_1406692 := by
    simpa [prefixWord, tailWord_1406692, baseEnd_1406692] using wordTrace_append hprefix tailTrace_1406692
  have hstable : (prefixWord ++ tailWord_1406692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406692).length < 2 ^ (prefixWord ++ tailWord_1406692).sum := by decide
  have hdescent : baseEnd_1406692 < baseStart_1406692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406702 : List Nat := [4, 1, 2, 1, 1, 2, 2, 10]
def baseStart_1406702 : Nat := 118140960795 + 1406702 * 2 ^ 59
def prefixEnd_1406702 : Nat := 4983230072969 + 3 ^ 40 * 1406702 * 2
def baseEnd_1406702 : Nat := 26752380134854092802063

theorem tailTrace_1406702 : CollatzResearch.WordTrace tailWord_1406702 prefixEnd_1406702 26752380134854092802063 := by
  unfold tailWord_1406702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6413329618720796802472795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34204424633177582946521573 6413329618720796802472795)
  ·
    refine ⟨9619994428081195203709193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6413329618720796802472795 9619994428081195203709193)
    ·
      refine ⟨7214995821060896402781895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9619994428081195203709193 7214995821060896402781895)
      ·
        refine ⟨10822493731591344604172843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7214995821060896402781895 10822493731591344604172843)
        ·
          refine ⟨16233740597387016906259265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10822493731591344604172843 16233740597387016906259265)
          ·
            refine ⟨12175305448040262679694449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16233740597387016906259265 12175305448040262679694449)
            ·
              refine ⟨9131479086030197009770837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12175305448040262679694449 9131479086030197009770837)
              ·
                refine ⟨26752380134854092802063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9131479086030197009770837 26752380134854092802063)
                ·
                  rfl

theorem cell23_1406702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_1406702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406702 prefixEnd_1406702 := by exact prefixLift 1406702
  have htrace : WordTrace (prefixWord ++ tailWord_1406702) baseStart_1406702 baseEnd_1406702 := by
    simpa [prefixWord, tailWord_1406702, baseEnd_1406702] using wordTrace_append hprefix tailTrace_1406702
  have hstable : (prefixWord ++ tailWord_1406702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406702).length < 2 ^ (prefixWord ++ tailWord_1406702).sum := by decide
  have hdescent : baseEnd_1406702 < baseStart_1406702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406716 : List Nat := [2, 2, 2, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_1406716 : Nat := 118140960795 + 1406716 * 2 ^ 59
def prefixEnd_1406716 : Nat := 4983230072969 + 3 ^ 40 * 1406716 * 2
def baseEnd_1406716 : Nat := 722321452370223450880637

theorem tailTrace_1406716 : CollatzResearch.WordTrace tailWord_1406716 prefixEnd_1406716 722321452370223450880637 := by
  unfold tailWord_1406716
  simp only [CollatzResearch.WordTrace]
  refine ⟨25653573785857827405396001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34204765047810436540528001 25653573785857827405396001)
  ·
    refine ⟨19240180339393370554047001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25653573785857827405396001 19240180339393370554047001)
    ·
      refine ⟨14430135254545027915535251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19240180339393370554047001 14430135254545027915535251)
      ·
        refine ⟨21645202881817541873302877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14430135254545027915535251 21645202881817541873302877)
        ·
          refine ⟨8116951080681578202488579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21645202881817541873302877 8116951080681578202488579)
          ·
            refine ⟨12175426621022367303732869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8116951080681578202488579 12175426621022367303732869)
            ·
              refine ⟨2282892491441693869449913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12175426621022367303732869 2282892491441693869449913)
              ·
                refine ⟨1712169368581270402087435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2282892491441693869449913 1712169368581270402087435)
                ·
                  refine ⟨2568254052871905603131153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712169368581270402087435 2568254052871905603131153)
                  ·
                    refine ⟨1926190539653929202348365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2568254052871905603131153 1926190539653929202348365)
                    ·
                      refine ⟨722321452370223450880637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1926190539653929202348365 722321452370223450880637)
                      ·
                        rfl

theorem cell23_1406716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_1406716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406716 prefixEnd_1406716 := by exact prefixLift 1406716
  have htrace : WordTrace (prefixWord ++ tailWord_1406716) baseStart_1406716 baseEnd_1406716 := by
    simpa [prefixWord, tailWord_1406716, baseEnd_1406716] using wordTrace_append hprefix tailTrace_1406716
  have hstable : (prefixWord ++ tailWord_1406716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406716).length < 2 ^ (prefixWord ++ tailWord_1406716).sum := by decide
  have hdescent : baseEnd_1406716 < baseStart_1406716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406730 : List Nat := [3, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2]
def baseStart_1406730 : Nat := 118140960795 + 1406730 * 2 ^ 59
def prefixEnd_1406730 : Nat := 4983230072969 + 3 ^ 40 * 1406730 * 2
def baseEnd_1406730 : Nat := 722328641099386396105573

theorem tailTrace_1406730 : CollatzResearch.WordTrace tailWord_1406730 prefixEnd_1406730 722328641099386396105573 := by
  unfold tailWord_1406730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12826914548416233800450411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34205105462443290134534429 12826914548416233800450411)
  ·
    refine ⟨19240371822624350700675617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12826914548416233800450411 19240371822624350700675617)
    ·
      refine ⟨14430278866968263025506713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19240371822624350700675617 14430278866968263025506713)
      ·
        refine ⟨10822709150226197269130035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14430278866968263025506713 10822709150226197269130035)
        ·
          refine ⟨16234063725339295903695053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10822709150226197269130035 16234063725339295903695053)
          ·
            refine ⟨6087773897002235963885645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16234063725339295903695053 6087773897002235963885645)
            ·
              refine ⟨2282915211375838486457117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6087773897002235963885645 2282915211375838486457117)
              ·
                refine ⟨856093204265939432421419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2282915211375838486457117 856093204265939432421419)
                ·
                  refine ⟨1284139806398909148632129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856093204265939432421419 1284139806398909148632129)
                  ·
                    refine ⟨963104854799181861474097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1284139806398909148632129 963104854799181861474097)
                    ·
                      refine ⟨722328641099386396105573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963104854799181861474097 722328641099386396105573)
                      ·
                        rfl

theorem cell23_1406730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_1406730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406730 prefixEnd_1406730 := by exact prefixLift 1406730
  have htrace : WordTrace (prefixWord ++ tailWord_1406730) baseStart_1406730 baseEnd_1406730 := by
    simpa [prefixWord, tailWord_1406730, baseEnd_1406730] using wordTrace_append hprefix tailTrace_1406730
  have hstable : (prefixWord ++ tailWord_1406730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406730).length < 2 ^ (prefixWord ++ tailWord_1406730).sum := by decide
  have hdescent : baseEnd_1406730 < baseStart_1406730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406746 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3]
def baseStart_1406746 : Nat := 118140960795 + 1406746 * 2 ^ 59
def prefixEnd_1406746 : Nat := 4983230072969 + 3 ^ 40 * 1406746 * 2
def baseEnd_1406746 : Nat := 722336856789858333505499

theorem tailTrace_1406746 : CollatzResearch.WordTrace tailWord_1406746 prefixEnd_1406746 722336856789858333505499 := by
  unfold tailWord_1406746
  simp only [CollatzResearch.WordTrace]
  refine ⟨12827060440401742483596023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34205494507737979956256061 12827060440401742483596023)
  ·
    refine ⟨19240590660602613725394035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12827060440401742483596023 19240590660602613725394035)
    ·
      refine ⟨28860885990903920588091053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19240590660602613725394035 28860885990903920588091053)
      ·
        refine ⟨10822832246588970220534145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28860885990903920588091053 10822832246588970220534145)
        ·
          refine ⟨8117124184941727665400609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10822832246588970220534145 8117124184941727665400609)
          ·
            refine ⟨6087843138706295749050457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8117124184941727665400609 6087843138706295749050457)
            ·
              refine ⟨4565882354029721811787843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087843138706295749050457 4565882354029721811787843)
              ·
                refine ⟨6848823531044582717681765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565882354029721811787843 6848823531044582717681765)
                ·
                  refine ⟨1284154412070859259565331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6848823531044582717681765 1284154412070859259565331)
                  ·
                    refine ⟨1926231618106288889347997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1284154412070859259565331 1926231618106288889347997)
                    ·
                      refine ⟨722336856789858333505499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1926231618106288889347997 722336856789858333505499)
                      ·
                        rfl

theorem cell23_1406746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_1406746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406746 prefixEnd_1406746 := by exact prefixLift 1406746
  have htrace : WordTrace (prefixWord ++ tailWord_1406746) baseStart_1406746 baseEnd_1406746 := by
    simpa [prefixWord, tailWord_1406746, baseEnd_1406746] using wordTrace_append hprefix tailTrace_1406746
  have hstable : (prefixWord ++ tailWord_1406746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406746).length < 2 ^ (prefixWord ++ tailWord_1406746).sum := by decide
  have hdescent : baseEnd_1406746 < baseStart_1406746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406773 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_1406773 : Nat := 118140960795 + 1406773 * 2 ^ 59
def prefixEnd_1406773 : Nat := 4983230072969 + 3 ^ 40 * 1406773 * 2
def baseEnd_1406773 : Nat := 722350720767529727867875

theorem tailTrace_1406773 : CollatzResearch.WordTrace tailWord_1406773 prefixEnd_1406773 722350720767529727867875 := by
  unfold tailWord_1406773
  simp only [CollatzResearch.WordTrace]
  refine ⟨51309226532509153545616973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34206151021672769030411315 51309226532509153545616973)
  ·
    refine ⟨19240959949690932579606365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51309226532509153545616973 19240959949690932579606365)
    ·
      refine ⟨7215359981134099717352387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19240959949690932579606365 7215359981134099717352387)
      ·
        refine ⟨10823039971701149576028581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7215359981134099717352387 10823039971701149576028581)
        ·
          refine ⟨2029319994693965545505359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10823039971701149576028581 2029319994693965545505359)
          ·
            refine ⟨3043979992040948318258039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029319994693965545505359 3043979992040948318258039)
            ·
              refine ⟨4565969988061422477387059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043979992040948318258039 4565969988061422477387059)
              ·
                refine ⟨6848954982092133716080589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565969988061422477387059 6848954982092133716080589)
                ·
                  refine ⟨2568358118284550143530221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6848954982092133716080589 2568358118284550143530221)
                  ·
                    refine ⟨963134294356706303823833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568358118284550143530221 963134294356706303823833)
                    ·
                      refine ⟨722350720767529727867875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963134294356706303823833 722350720767529727867875)
                      ·
                        rfl

theorem cell23_1406773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_1406773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406773 prefixEnd_1406773 := by exact prefixLift 1406773
  have htrace : WordTrace (prefixWord ++ tailWord_1406773) baseStart_1406773 baseEnd_1406773 := by
    simpa [prefixWord, tailWord_1406773, baseEnd_1406773] using wordTrace_append hprefix tailTrace_1406773
  have hstable : (prefixWord ++ tailWord_1406773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406773).length < 2 ^ (prefixWord ++ tailWord_1406773).sum := by decide
  have hdescent : baseEnd_1406773 < baseStart_1406773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406859 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 4]
def baseStart_1406859 : Nat := 118140960795 + 1406859 * 2 ^ 59
def prefixEnd_1406859 : Nat := 4983230072969 + 3 ^ 40 * 1406859 * 2
def baseEnd_1406859 : Nat := 722394880103816391392479

theorem tailTrace_1406859 : CollatzResearch.WordTrace tailWord_1406859 prefixEnd_1406859 722394880103816391392479 := by
  unfold tailWord_1406859
  simp only [CollatzResearch.WordTrace]
  refine ⟨51312363210197590233247631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34208242140131726822165087 51312363210197590233247631)
  ·
    refine ⟨76968544815296385349871447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51312363210197590233247631 76968544815296385349871447)
    ·
      refine ⟨115452817222944578024807171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76968544815296385349871447 115452817222944578024807171)
      ·
        refine ⟨173179225834416867037210757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115452817222944578024807171 173179225834416867037210757)
        ·
          refine ⟨32471104843953162569477017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173179225834416867037210757 32471104843953162569477017)
          ·
            refine ⟨24353328632964871927107763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32471104843953162569477017 24353328632964871927107763)
            ·
              refine ⟨36529992949447307890661645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24353328632964871927107763 36529992949447307890661645)
              ·
                refine ⟨13698747356042740458998117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36529992949447307890661645 13698747356042740458998117)
                ·
                  refine ⟨2568515129258013836062147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13698747356042740458998117 2568515129258013836062147)
                  ·
                    refine ⟨3852772693887020754093221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2568515129258013836062147 3852772693887020754093221)
                    ·
                      refine ⟨722394880103816391392479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3852772693887020754093221 722394880103816391392479)
                      ·
                        rfl

theorem cell23_1406859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 4].length) (baseStart_1406859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406859 prefixEnd_1406859 := by exact prefixLift 1406859
  have htrace : WordTrace (prefixWord ++ tailWord_1406859) baseStart_1406859 baseEnd_1406859 := by
    simpa [prefixWord, tailWord_1406859, baseEnd_1406859] using wordTrace_append hprefix tailTrace_1406859
  have hstable : (prefixWord ++ tailWord_1406859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406859).length < 2 ^ (prefixWord ++ tailWord_1406859).sum := by decide
  have hdescent : baseEnd_1406859 < baseStart_1406859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406876 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1406876 : Nat := 118140960795 + 1406876 * 2 ^ 59
def prefixEnd_1406876 : Nat := 4983230072969 + 3 ^ 40 * 1406876 * 2
def baseEnd_1406876 : Nat := 722403609274942824879901

theorem tailTrace_1406876 : CollatzResearch.WordTrace tailWord_1406876 prefixEnd_1406876 722403609274942824879901 := by
  unfold tailWord_1406876
  simp only [CollatzResearch.WordTrace]
  refine ⟨25656491625568001068308241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34208655500757334757744321 25656491625568001068308241)
  ·
    refine ⟨19242368719176000801231181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25656491625568001068308241 19242368719176000801231181)
    ·
      refine ⟨7215888269691000300461693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19242368719176000801231181 7215888269691000300461693)
      ·
        refine ⟨2705958101134125112673135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7215888269691000300461693 2705958101134125112673135)
        ·
          refine ⟨4058937151701187669009703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705958101134125112673135 4058937151701187669009703)
          ·
            refine ⟨6088405727551781503514555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058937151701187669009703 6088405727551781503514555)
            ·
              refine ⟨9132608591327672255271833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088405727551781503514555 9132608591327672255271833)
              ·
                refine ⟨6849456443495754191453875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9132608591327672255271833 6849456443495754191453875)
                ·
                  refine ⟨10274184665243631287180813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6849456443495754191453875 10274184665243631287180813)
                  ·
                    refine ⟨3852819249466361732692805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10274184665243631287180813 3852819249466361732692805)
                    ·
                      refine ⟨722403609274942824879901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3852819249466361732692805 722403609274942824879901)
                      ·
                        rfl

theorem cell23_1406876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1406876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406876 prefixEnd_1406876 := by exact prefixLift 1406876
  have htrace : WordTrace (prefixWord ++ tailWord_1406876) baseStart_1406876 baseEnd_1406876 := by
    simpa [prefixWord, tailWord_1406876, baseEnd_1406876] using wordTrace_append hprefix tailTrace_1406876
  have hstable : (prefixWord ++ tailWord_1406876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406876).length < 2 ^ (prefixWord ++ tailWord_1406876).sum := by decide
  have hdescent : baseEnd_1406876 < baseStart_1406876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406894 : List Nat := [4, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_1406894 : Nat := 118140960795 + 1406894 * 2 ^ 59
def prefixEnd_1406894 : Nat := 4983230072969 + 3 ^ 40 * 1406894 * 2
def baseEnd_1406894 : Nat := 80268094658524861606091

theorem tailTrace_1406894 : CollatzResearch.WordTrace tailWord_1406894 prefixEnd_1406894 80268094658524861606091 := by
  unfold tailWord_1406894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414204970633848901346467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34209093176713860807181157 6414204970633848901346467)
  ·
    refine ⟨9621307455950773352019701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6414204970633848901346467 9621307455950773352019701)
    ·
      refine ⟨901997573995385001751847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9621307455950773352019701 901997573995385001751847)
      ·
        refine ⟨1352996360993077502627771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901997573995385001751847 1352996360993077502627771)
        ·
          refine ⟨2029494541489616253941657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352996360993077502627771 2029494541489616253941657)
          ·
            refine ⟨1522120906117212190456243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2029494541489616253941657 1522120906117212190456243)
            ·
              refine ⟨2283181359175818285684365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522120906117212190456243 2283181359175818285684365)
              ·
                refine ⟨856193009690931857131637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2283181359175818285684365 856193009690931857131637)
                ·
                  refine ⟨80268094658524861606091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 856193009690931857131637 80268094658524861606091)
                  ·
                    rfl

theorem cell23_1406894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_1406894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406894 prefixEnd_1406894 := by exact prefixLift 1406894
  have htrace : WordTrace (prefixWord ++ tailWord_1406894) baseStart_1406894 baseEnd_1406894 := by
    simpa [prefixWord, tailWord_1406894, baseEnd_1406894] using wordTrace_append hprefix tailTrace_1406894
  have hstable : (prefixWord ++ tailWord_1406894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406894).length < 2 ^ (prefixWord ++ tailWord_1406894).sum := by decide
  have hdescent : baseEnd_1406894 < baseStart_1406894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406933 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 6]
def baseStart_1406933 : Nat := 118140960795 + 1406933 * 2 ^ 59
def prefixEnd_1406933 : Nat := 4983230072969 + 3 ^ 40 * 1406933 * 2
def baseEnd_1406933 : Nat := 80270319741361011318571

theorem tailTrace_1406933 : CollatzResearch.WordTrace tailWord_1406933 prefixEnd_1406933 80270319741361011318571 := by
  unfold tailWord_1406933
  simp only [CollatzResearch.WordTrace]
  refine ⟨51315062211929500871441453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34210041474619667247627635 51315062211929500871441453)
  ·
    refine ⟨19243148329473562826790545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51315062211929500871441453 19243148329473562826790545)
    ·
      refine ⟨14432361247105172120092909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19243148329473562826790545 14432361247105172120092909)
      ·
        refine ⟨5412135467664439545034841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14432361247105172120092909 5412135467664439545034841)
        ·
          refine ⟨4059101600748329658776131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5412135467664439545034841 4059101600748329658776131)
          ·
            refine ⟨6088652401122494488164197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059101600748329658776131 6088652401122494488164197)
            ·
              refine ⟨1141622325210467716530787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6088652401122494488164197 1141622325210467716530787)
              ·
                refine ⟨1712433487815701574796181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1141622325210467716530787 1712433487815701574796181)
                ·
                  refine ⟨80270319741361011318571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1712433487815701574796181 80270319741361011318571)
                  ·
                    rfl

theorem cell23_1406933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_1406933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406933 prefixEnd_1406933 := by exact prefixLift 1406933
  have htrace : WordTrace (prefixWord ++ tailWord_1406933) baseStart_1406933 baseEnd_1406933 := by
    simpa [prefixWord, tailWord_1406933, baseEnd_1406933] using wordTrace_append hprefix tailTrace_1406933
  have hstable : (prefixWord ++ tailWord_1406933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406933).length < 2 ^ (prefixWord ++ tailWord_1406933).sum := by decide
  have hdescent : baseEnd_1406933 < baseStart_1406933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1406979 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 6]
def baseStart_1406979 : Nat := 118140960795 + 1406979 * 2 ^ 59
def prefixEnd_1406979 : Nat := 4983230072969 + 3 ^ 40 * 1406979 * 2
def baseEnd_1406979 : Nat := 722456497782355921891927

theorem tailTrace_1406979 : CollatzResearch.WordTrace tailWord_1406979 prefixEnd_1406979 722456497782355921891927 := by
  unfold tailWord_1406979
  simp only [CollatzResearch.WordTrace]
  refine ⟨51316739969762850727615991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34211159979841900485077327 51316739969762850727615991)
  ·
    refine ⟨76975109954644276091423987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51316739969762850727615991 76975109954644276091423987)
    ·
      refine ⟨115462664931966414137135981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76975109954644276091423987 115462664931966414137135981)
      ·
        refine ⟨43298499349487405301425993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115462664931966414137135981 43298499349487405301425993)
        ·
          refine ⟨32473874512115553976069495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43298499349487405301425993 32473874512115553976069495)
          ·
            refine ⟨48710811768173330964104243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32473874512115553976069495 48710811768173330964104243)
            ·
              refine ⟨73066217652259996446156365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48710811768173330964104243 73066217652259996446156365)
              ·
                refine ⟨27399831619597498667308637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73066217652259996446156365 27399831619597498667308637)
                ·
                  refine ⟨10274936857349062000240739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27399831619597498667308637 10274936857349062000240739)
                  ·
                    refine ⟨15412405286023593000361109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10274936857349062000240739 15412405286023593000361109)
                    ·
                      refine ⟨722456497782355921891927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15412405286023593000361109 722456497782355921891927)
                      ·
                        rfl

theorem cell23_1406979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_1406979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1406979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1406979 prefixEnd_1406979 := by exact prefixLift 1406979
  have htrace : WordTrace (prefixWord ++ tailWord_1406979) baseStart_1406979 baseEnd_1406979 := by
    simpa [prefixWord, tailWord_1406979, baseEnd_1406979] using wordTrace_append hprefix tailTrace_1406979
  have hstable : (prefixWord ++ tailWord_1406979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1406979).length < 2 ^ (prefixWord ++ tailWord_1406979).sum := by decide
  have hdescent : baseEnd_1406979 < baseStart_1406979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1406979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407000 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 3, 2, 2]
def baseStart_1407000 : Nat := 118140960795 + 1407000 * 2 ^ 59
def prefixEnd_1407000 : Nat := 4983230072969 + 3 ^ 40 * 1407000 * 2
def baseEnd_1407000 : Nat := 722467280876100339729331

theorem tailTrace_1407000 : CollatzResearch.WordTrace tailWord_1407000 prefixEnd_1407000 722467280876100339729331 := by
  unfold tailWord_1407000
  simp only [CollatzResearch.WordTrace]
  refine ⟨25658752951343385657065227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34211670601791180876086969 25658752951343385657065227)
  ·
    refine ⟨38488129427015078485597841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25658752951343385657065227 38488129427015078485597841)
    ·
      refine ⟨28866097070261308864198381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38488129427015078485597841 28866097070261308864198381)
      ·
        refine ⟨10824786401347990824074393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28866097070261308864198381 10824786401347990824074393)
        ·
          refine ⟨8118589801010993118055795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10824786401347990824074393 8118589801010993118055795)
          ·
            refine ⟨12177884701516489677083693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118589801010993118055795 12177884701516489677083693)
            ·
              refine ⟨4566706763068683628906385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12177884701516489677083693 4566706763068683628906385)
              ·
                refine ⟨3425030072301512721679789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4566706763068683628906385 3425030072301512721679789)
                ·
                  refine ⟨1284386277113067270629921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3425030072301512721679789 1284386277113067270629921)
                  ·
                    refine ⟨963289707834800452972441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1284386277113067270629921 963289707834800452972441)
                    ·
                      refine ⟨722467280876100339729331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963289707834800452972441 722467280876100339729331)
                      ·
                        rfl

theorem cell23_1407000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_1407000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407000 prefixEnd_1407000 := by exact prefixLift 1407000
  have htrace : WordTrace (prefixWord ++ tailWord_1407000) baseStart_1407000 baseEnd_1407000 := by
    simpa [prefixWord, tailWord_1407000, baseEnd_1407000] using wordTrace_append hprefix tailTrace_1407000
  have hstable : (prefixWord ++ tailWord_1407000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407000).length < 2 ^ (prefixWord ++ tailWord_1407000).sum := by decide
  have hdescent : baseEnd_1407000 < baseStart_1407000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407019 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 1, 9]
def baseStart_1407019 : Nat := 118140960795 + 1407019 * 2 ^ 59
def prefixEnd_1407019 : Nat := 4983230072969 + 3 ^ 40 * 1407019 * 2
def baseEnd_1407019 : Nat := 240825679002845255130581

theorem tailTrace_1407019 : CollatzResearch.WordTrace tailWord_1407019 prefixEnd_1407019 240825679002845255130581 := by
  unfold tailWord_1407019
  simp only [CollatzResearch.WordTrace]
  refine ⟨51318198889617937559072111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34212132593078625039381407 51318198889617937559072111)
  ·
    refine ⟨76977298334426906338608167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51318198889617937559072111 76977298334426906338608167)
    ·
      refine ⟨115465947501640359507912251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76977298334426906338608167 115465947501640359507912251)
      ·
        refine ⟨173198921252460539261868377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115465947501640359507912251 173198921252460539261868377)
        ·
          refine ⟨129899190939345404446401283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173198921252460539261868377 129899190939345404446401283)
          ·
            refine ⟨194848786409018106669601925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129899190939345404446401283 194848786409018106669601925)
            ·
              refine ⟨36534147451690895000550361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194848786409018106669601925 36534147451690895000550361)
              ·
                refine ⟨27400610588768171250412771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36534147451690895000550361 27400610588768171250412771)
                ·
                  refine ⟨41100915883152256875619157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27400610588768171250412771 41100915883152256875619157)
                  ·
                    refine ⟨240825679002845255130581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 41100915883152256875619157 240825679002845255130581)
                    ·
                      rfl

theorem cell23_1407019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 9].length) (baseStart_1407019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407019 prefixEnd_1407019 := by exact prefixLift 1407019
  have htrace : WordTrace (prefixWord ++ tailWord_1407019) baseStart_1407019 baseEnd_1407019 := by
    simpa [prefixWord, tailWord_1407019, baseEnd_1407019] using wordTrace_append hprefix tailTrace_1407019
  have hstable : (prefixWord ++ tailWord_1407019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407019).length < 2 ^ (prefixWord ++ tailWord_1407019).sum := by decide
  have hdescent : baseEnd_1407019 < baseStart_1407019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407043 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 3, 3, 2]
def baseStart_1407043 : Nat := 118140960795 + 1407043 * 2 ^ 59
def prefixEnd_1407043 : Nat := 4983230072969 + 3 ^ 40 * 1407043 * 2
def baseEnd_1407043 : Nat := 722489360544243671491633

theorem tailTrace_1407043 : CollatzResearch.WordTrace tailWord_1407043 prefixEnd_1407043 722489360544243671491633 := by
  unfold tailWord_1407043
  simp only [CollatzResearch.WordTrace]
  refine ⟨51319074241530989657945783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34212716161020659771963855 51319074241530989657945783)
  ·
    refine ⟨76978611362296484486918675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51319074241530989657945783 76978611362296484486918675)
    ·
      refine ⟨115467917043444726730378013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76978611362296484486918675 115467917043444726730378013)
      ·
        refine ⟨43300468891291772523891755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115467917043444726730378013 43300468891291772523891755)
        ·
          refine ⟨64950703336937658785837633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43300468891291772523891755 64950703336937658785837633)
          ·
            refine ⟨48713027502703244089378225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64950703336937658785837633 48713027502703244089378225)
            ·
              refine ⟨36534770627027433067033669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48713027502703244089378225 36534770627027433067033669)
              ·
                refine ⟨6850269492567643700068813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36534770627027433067033669 6850269492567643700068813)
                ·
                  refine ⟨2568851059712866387525805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6850269492567643700068813 2568851059712866387525805)
                  ·
                    refine ⟨963319147392324895322177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568851059712866387525805 963319147392324895322177)
                    ·
                      refine ⟨722489360544243671491633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963319147392324895322177 722489360544243671491633)
                      ·
                        rfl

theorem cell23_1407043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_1407043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407043 prefixEnd_1407043 := by exact prefixLift 1407043
  have htrace : WordTrace (prefixWord ++ tailWord_1407043) baseStart_1407043 baseEnd_1407043 := by
    simpa [prefixWord, tailWord_1407043, baseEnd_1407043] using wordTrace_append hprefix tailTrace_1407043
  have hstable : (prefixWord ++ tailWord_1407043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407043).length < 2 ^ (prefixWord ++ tailWord_1407043).sum := by decide
  have hdescent : baseEnd_1407043 < baseStart_1407043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407073 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_1407073 : Nat := 118140960795 + 1407073 * 2 ^ 59
def prefixEnd_1407073 : Nat := 4983230072969 + 3 ^ 40 * 1407073 * 2
def baseEnd_1407073 : Nat := 722504764963878554116495

theorem tailTrace_1407073 : CollatzResearch.WordTrace tailWord_1407073 prefixEnd_1407073 722504764963878554116495 := by
  unfold tailWord_1407073
  simp only [CollatzResearch.WordTrace]
  refine ⟨51320168431422304781537873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34213445620948203187691915 51320168431422304781537873)
  ·
    refine ⟨38490126323566728586153405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51320168431422304781537873 38490126323566728586153405)
    ·
      refine ⟨14433797371337523219807527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38490126323566728586153405 14433797371337523219807527)
      ·
        refine ⟨21650696057006284829711291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14433797371337523219807527 21650696057006284829711291)
        ·
          refine ⟨32476044085509427244566937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21650696057006284829711291 32476044085509427244566937)
          ·
            refine ⟨24357033064132070433425203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32476044085509427244566937 24357033064132070433425203)
            ·
              refine ⟨36535549596198105650137805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24357033064132070433425203 36535549596198105650137805)
              ·
                refine ⟨13700831098574289618801677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36535549596198105650137805 13700831098574289618801677)
                ·
                  refine ⟨5137811661965358607050629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13700831098574289618801677 5137811661965358607050629)
                  ·
                    refine ⟨963339686618504738821993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137811661965358607050629 963339686618504738821993)
                    ·
                      refine ⟨722504764963878554116495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963339686618504738821993 722504764963878554116495)
                      ·
                        rfl

theorem cell23_1407073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_1407073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407073 prefixEnd_1407073 := by exact prefixLift 1407073
  have htrace : WordTrace (prefixWord ++ tailWord_1407073) baseStart_1407073 baseEnd_1407073 := by
    simpa [prefixWord, tailWord_1407073, baseEnd_1407073] using wordTrace_append hprefix tailTrace_1407073
  have hstable : (prefixWord ++ tailWord_1407073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407073).length < 2 ^ (prefixWord ++ tailWord_1407073).sum := by decide
  have hdescent : baseEnd_1407073 < baseStart_1407073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407076 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_1407076 : Nat := 118140960795 + 1407076 * 2 ^ 59
def prefixEnd_1407076 : Nat := 4983230072969 + 3 ^ 40 * 1407076 * 2
def baseEnd_1407076 : Nat := 722506305405842042378981

theorem tailTrace_1407076 : CollatzResearch.WordTrace tailWord_1407076 prefixEnd_1407076 722506305405842042378981 := by
  unfold tailWord_1407076
  simp only [CollatzResearch.WordTrace]
  refine ⟨25660138925205718146948541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34213518566940957529264721 25660138925205718146948541)
  ·
    refine ⟨9622552096952144305105703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25660138925205718146948541 9622552096952144305105703)
    ·
      refine ⟨14433828145428216457658555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9622552096952144305105703 14433828145428216457658555)
      ·
        refine ⟨21650742218142324686487833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14433828145428216457658555 21650742218142324686487833)
        ·
          refine ⟨16238056663606743514865875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21650742218142324686487833 16238056663606743514865875)
          ·
            refine ⟨24357084995410115272298813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16238056663606743514865875 24357084995410115272298813)
            ·
              refine ⟨9133906873278793227112055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24357084995410115272298813 9133906873278793227112055)
              ·
                refine ⟨13700860309918189840668083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9133906873278793227112055 13700860309918189840668083)
                ·
                  refine ⟨20551290464877284761002125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13700860309918189840668083 20551290464877284761002125)
                  ·
                    refine ⟨7706733924328981785375797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20551290464877284761002125 7706733924328981785375797)
                    ·
                      refine ⟨722506305405842042378981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7706733924328981785375797 722506305405842042378981)
                      ·
                        rfl

theorem cell23_1407076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_1407076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407076 prefixEnd_1407076 := by exact prefixLift 1407076
  have htrace : WordTrace (prefixWord ++ tailWord_1407076) baseStart_1407076 baseEnd_1407076 := by
    simpa [prefixWord, tailWord_1407076, baseEnd_1407076] using wordTrace_append hprefix tailTrace_1407076
  have hstable : (prefixWord ++ tailWord_1407076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407076).length < 2 ^ (prefixWord ++ tailWord_1407076).sum := by decide
  have hdescent : baseEnd_1407076 < baseStart_1407076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407107 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 2, 2, 2]
def baseStart_1407107 : Nat := 118140960795 + 1407107 * 2 ^ 59
def prefixEnd_1407107 : Nat := 4983230072969 + 3 ^ 40 * 1407107 * 2
def baseEnd_1407107 : Nat := 722522223306131421091339

theorem tailTrace_1407107 : CollatzResearch.WordTrace tailWord_1407107 prefixEnd_1407107 722522223306131421091339 := by
  unfold tailWord_1407107
  simp only [CollatzResearch.WordTrace]
  refine ⟨51321408513299128588275575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34214272342199419058850383 51321408513299128588275575)
  ·
    refine ⟨76982112769948692882413363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51321408513299128588275575 76982112769948692882413363)
    ·
      refine ⟨115473169154923039323620045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76982112769948692882413363 115473169154923039323620045)
      ·
        refine ⟨43302438433096139746357517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115473169154923039323620045 43302438433096139746357517)
        ·
          refine ⟨16238414412411052404884069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43302438433096139746357517 16238414412411052404884069)
          ·
            refine ⟨3044702702327072325915763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16238414412411052404884069 3044702702327072325915763)
            ·
              refine ⟨4567054053490608488873645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044702702327072325915763 4567054053490608488873645)
              ·
                refine ⟨1712645270058978183327617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4567054053490608488873645 1712645270058978183327617)
                ·
                  refine ⟨1284483952544233637495713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1712645270058978183327617 1284483952544233637495713)
                  ·
                    refine ⟨963362964408175228121785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1284483952544233637495713 963362964408175228121785)
                    ·
                      refine ⟨722522223306131421091339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963362964408175228121785 722522223306131421091339)
                      ·
                        rfl

theorem cell23_1407107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_1407107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407107 prefixEnd_1407107 := by exact prefixLift 1407107
  have htrace : WordTrace (prefixWord ++ tailWord_1407107) baseStart_1407107 baseEnd_1407107 := by
    simpa [prefixWord, tailWord_1407107, baseEnd_1407107] using wordTrace_append hprefix tailTrace_1407107
  have hstable : (prefixWord ++ tailWord_1407107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407107).length < 2 ^ (prefixWord ++ tailWord_1407107).sum := by decide
  have hdescent : baseEnd_1407107 < baseStart_1407107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407124 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1407124 : Nat := 118140960795 + 1407124 * 2 ^ 59
def prefixEnd_1407124 : Nat := 4983230072969 + 3 ^ 40 * 1407124 * 2
def baseEnd_1407124 : Nat := 722530952477257854578761

theorem tailTrace_1407124 : CollatzResearch.WordTrace tailWord_1407124 prefixEnd_1407124 722530952477257854578761 := by
  unfold tailWord_1407124
  simp only [CollatzResearch.WordTrace]
  refine ⟨25661014277118770245822213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34214685702825026994429617 25661014277118770245822213)
  ·
    refine ⟨4811440176959769421091665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25661014277118770245822213 4811440176959769421091665)
    ·
      refine ⟨3608580132719827065818749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4811440176959769421091665 3608580132719827065818749)
      ·
        refine ⟨1353217549769935149682031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3608580132719827065818749 1353217549769935149682031)
        ·
          refine ⟨2029826324654902724523047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353217549769935149682031 2029826324654902724523047)
          ·
            refine ⟨3044739486982354086784571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029826324654902724523047 3044739486982354086784571)
            ·
              refine ⟨4567109230473531130176857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044739486982354086784571 4567109230473531130176857)
              ·
                refine ⟨3425331922855148347632643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4567109230473531130176857 3425331922855148347632643)
                ·
                  refine ⟨5137997884282722521448965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425331922855148347632643 5137997884282722521448965)
                  ·
                    refine ⟨963374603303010472771681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137997884282722521448965 963374603303010472771681)
                    ·
                      refine ⟨722530952477257854578761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963374603303010472771681 722530952477257854578761)
                      ·
                        rfl

theorem cell23_1407124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1407124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407124 prefixEnd_1407124 := by exact prefixLift 1407124
  have htrace : WordTrace (prefixWord ++ tailWord_1407124) baseStart_1407124 baseEnd_1407124 := by
    simpa [prefixWord, tailWord_1407124, baseEnd_1407124] using wordTrace_append hprefix tailTrace_1407124
  have hstable : (prefixWord ++ tailWord_1407124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407124).length < 2 ^ (prefixWord ++ tailWord_1407124).sum := by decide
  have hdescent : baseEnd_1407124 < baseStart_1407124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407157 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1407157 : Nat := 118140960795 + 1407157 * 2 ^ 59
def prefixEnd_1407157 : Nat := 4983230072969 + 3 ^ 40 * 1407157 * 2
def baseEnd_1407157 : Nat := 722547897338856225466109

theorem tailTrace_1407157 : CollatzResearch.WordTrace tailWord_1407157 prefixEnd_1407157 722547897338856225466109 := by
  unfold tailWord_1407157
  simp only [CollatzResearch.WordTrace]
  refine ⟨51323232163117987127595725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34215488108745324751730483 51323232163117987127595725)
  ·
    refine ⟨19246212061169245172848397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51323232163117987127595725 19246212061169245172848397)
    ·
      refine ⟨7217329522938466939818149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19246212061169245172848397 7217329522938466939818149)
      ·
        refine ⟨1353249285550962551215903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7217329522938466939818149 1353249285550962551215903)
        ·
          refine ⟨2029873928326443826823855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353249285550962551215903 2029873928326443826823855)
          ·
            refine ⟨3044810892489665740235783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029873928326443826823855 3044810892489665740235783)
            ·
              refine ⟨4567216338734498610353675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044810892489665740235783 4567216338734498610353675)
              ·
                refine ⟨6850824508101747915530513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567216338734498610353675 6850824508101747915530513)
                ·
                  refine ⟨5138118381076310936647885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6850824508101747915530513 5138118381076310936647885)
                  ·
                    refine ⟨1926794392903616601242957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5138118381076310936647885 1926794392903616601242957)
                    ·
                      refine ⟨722547897338856225466109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1926794392903616601242957 722547897338856225466109)
                      ·
                        rfl

theorem cell23_1407157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1407157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407157 prefixEnd_1407157 := by exact prefixLift 1407157
  have htrace : WordTrace (prefixWord ++ tailWord_1407157) baseStart_1407157 baseEnd_1407157 := by
    simpa [prefixWord, tailWord_1407157, baseEnd_1407157] using wordTrace_append hprefix tailTrace_1407157
  have hstable : (prefixWord ++ tailWord_1407157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407157).length < 2 ^ (prefixWord ++ tailWord_1407157).sum := by decide
  have hdescent : baseEnd_1407157 < baseStart_1407157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407173 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_1407173 : Nat := 118140960795 + 1407173 * 2 ^ 59
def prefixEnd_1407173 : Nat := 4983230072969 + 3 ^ 40 * 1407173 * 2
def baseEnd_1407173 : Nat := 240852037676442720955345

theorem tailTrace_1407173 : CollatzResearch.WordTrace tailWord_1407173 prefixEnd_1407173 240852037676442720955345 := by
  unfold tailWord_1407173
  simp only [CollatzResearch.WordTrace]
  refine ⟨51323815731060021860178173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34215877154040014573452115 51323815731060021860178173)
  ·
    refine ⟨19246430899147508197566815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51323815731060021860178173 19246430899147508197566815)
    ·
      refine ⟨28869646348721262296350223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19246430899147508197566815 28869646348721262296350223)
      ·
        refine ⟨43304469523081893444525335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28869646348721262296350223 43304469523081893444525335)
        ·
          refine ⟨64956704284622840166788003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43304469523081893444525335 64956704284622840166788003)
          ·
            refine ⟨97435056426934260250182005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64956704284622840166788003 97435056426934260250182005)
            ·
              refine ⟨9134536540025086898454563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97435056426934260250182005 9134536540025086898454563)
              ·
                refine ⟨13701804810037630347681845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9134536540025086898454563 13701804810037630347681845)
                ·
                  refine ⟨1284544200941027845095173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13701804810037630347681845 1284544200941027845095173)
                  ·
                    refine ⟨240852037676442720955345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1284544200941027845095173 240852037676442720955345)
                    ·
                      rfl

theorem cell23_1407173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_1407173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407173 prefixEnd_1407173 := by exact prefixLift 1407173
  have htrace : WordTrace (prefixWord ++ tailWord_1407173) baseStart_1407173 baseEnd_1407173 := by
    simpa [prefixWord, tailWord_1407173, baseEnd_1407173] using wordTrace_append hprefix tailTrace_1407173
  have hstable : (prefixWord ++ tailWord_1407173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407173).length < 2 ^ (prefixWord ++ tailWord_1407173).sum := by decide
  have hdescent : baseEnd_1407173 < baseStart_1407173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407183 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 3]
def baseStart_1407183 : Nat := 118140960795 + 1407183 * 2 ^ 59
def prefixEnd_1407183 : Nat := 4983230072969 + 3 ^ 40 * 1407183 * 2
def baseEnd_1407183 : Nat := 722561247835873123740989

theorem tailTrace_1407183 : CollatzResearch.WordTrace tailWord_1407183 prefixEnd_1407183 722561247835873123740989 := by
  unfold tailWord_1407183
  simp only [CollatzResearch.WordTrace]
  refine ⟨51324180461023793568042203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34216120307349195712028135 51324180461023793568042203)
  ·
    refine ⟨76986270691535690352063305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51324180461023793568042203 76986270691535690352063305)
    ·
      refine ⟨57739703018651767764047479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76986270691535690352063305 57739703018651767764047479)
      ·
        refine ⟨86609554527977651646071219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57739703018651767764047479 86609554527977651646071219)
        ·
          refine ⟨129914331791966477469106829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86609554527977651646071219 129914331791966477469106829)
          ·
            refine ⟨48717874421987429050915061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129914331791966477469106829 48717874421987429050915061)
            ·
              refine ⟨4567300727061321473523287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48717874421987429050915061 4567300727061321473523287)
              ·
                refine ⟨6850951090591982210284931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567300727061321473523287 6850951090591982210284931)
                ·
                  refine ⟨10276426635887973315427397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6850951090591982210284931 10276426635887973315427397)
                  ·
                    refine ⟨1926829994228994996642637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10276426635887973315427397 1926829994228994996642637)
                    ·
                      refine ⟨722561247835873123740989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1926829994228994996642637 722561247835873123740989)
                      ·
                        rfl

theorem cell23_1407183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_1407183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407183 prefixEnd_1407183 := by exact prefixLift 1407183
  have htrace : WordTrace (prefixWord ++ tailWord_1407183) baseStart_1407183 baseEnd_1407183 := by
    simpa [prefixWord, tailWord_1407183, baseEnd_1407183] using wordTrace_append hprefix tailTrace_1407183
  have hstable : (prefixWord ++ tailWord_1407183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407183).length < 2 ^ (prefixWord ++ tailWord_1407183).sum := by decide
  have hdescent : baseEnd_1407183 < baseStart_1407183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407197 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_1407197 : Nat := 118140960795 + 1407197 * 2 ^ 59
def prefixEnd_1407197 : Nat := 4983230072969 + 3 ^ 40 * 1407197 * 2
def baseEnd_1407197 : Nat := 722568436565036068965925

theorem tailTrace_1407197 : CollatzResearch.WordTrace tailWord_1407197 prefixEnd_1407197 722568436565036068965925 := by
  unfold tailWord_1407197
  simp only [CollatzResearch.WordTrace]
  refine ⟨51324691082973073959051845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34216460721982049306034563 51324691082973073959051845)
  ·
    refine ⟨9623379578057451367322221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51324691082973073959051845 9623379578057451367322221)
    ·
      refine ⟨3608767341771544262745833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9623379578057451367322221 3608767341771544262745833)
      ·
        refine ⟨2706575506328658197059375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3608767341771544262745833 2706575506328658197059375)
        ·
          refine ⟨4059863259492987295589063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706575506328658197059375 4059863259492987295589063)
          ·
            refine ⟨6089794889239480943383595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059863259492987295589063 6089794889239480943383595)
            ·
              refine ⟨9134692333859221415075393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089794889239480943383595 9134692333859221415075393)
              ·
                refine ⟨6851019250394416061306545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9134692333859221415075393 6851019250394416061306545)
                ·
                  refine ⟨5138264437795812045979909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6851019250394416061306545 5138264437795812045979909)
                  ·
                    refine ⟨963424582086714758621233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5138264437795812045979909 963424582086714758621233)
                    ·
                      refine ⟨722568436565036068965925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963424582086714758621233 722568436565036068965925)
                      ·
                        rfl

theorem cell23_1407197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_1407197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407197 prefixEnd_1407197 := by exact prefixLift 1407197
  have htrace : WordTrace (prefixWord ++ tailWord_1407197) baseStart_1407197 baseEnd_1407197 := by
    simpa [prefixWord, tailWord_1407197, baseEnd_1407197] using wordTrace_append hprefix tailTrace_1407197
  have hstable : (prefixWord ++ tailWord_1407197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407197).length < 2 ^ (prefixWord ++ tailWord_1407197).sum := by decide
  have hdescent : baseEnd_1407197 < baseStart_1407197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407207 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 3, 4]
def baseStart_1407207 : Nat := 118140960795 + 1407207 * 2 ^ 59
def prefixEnd_1407207 : Nat := 4983230072969 + 3 ^ 40 * 1407207 * 2
def baseEnd_1407207 : Nat := 240857857123860343280293

theorem tailTrace_1407207 : CollatzResearch.WordTrace tailWord_1407207 prefixEnd_1407207 240857857123860343280293 := by
  unfold tailWord_1407207
  simp only [CollatzResearch.WordTrace]
  refine ⟨51325055812936845666915875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34216703875291230444610583 51325055812936845666915875)
  ·
    refine ⟨76987583719405268500373813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51325055812936845666915875 76987583719405268500373813)
    ·
      refine ⟨7217585973694243921910045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76987583719405268500373813 7217585973694243921910045)
      ·
        refine ⟨2706594740135341470716267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7217585973694243921910045 2706594740135341470716267)
        ·
          refine ⟨4059892110203012206074401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706594740135341470716267 4059892110203012206074401)
          ·
            refine ⟨3044919082652259154555801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4059892110203012206074401 3044919082652259154555801)
            ·
              refine ⟨2283689311989194365916851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3044919082652259154555801 2283689311989194365916851)
              ·
                refine ⟨3425533967983791548875277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283689311989194365916851 3425533967983791548875277)
                ·
                  refine ⟨1284575237993921830828229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3425533967983791548875277 1284575237993921830828229)
                  ·
                    refine ⟨240857857123860343280293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1284575237993921830828229 240857857123860343280293)
                    ·
                      rfl

theorem cell23_1407207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_1407207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407207 prefixEnd_1407207 := by exact prefixLift 1407207
  have htrace : WordTrace (prefixWord ++ tailWord_1407207) baseStart_1407207 baseEnd_1407207 := by
    simpa [prefixWord, tailWord_1407207, baseEnd_1407207] using wordTrace_append hprefix tailTrace_1407207
  have hstable : (prefixWord ++ tailWord_1407207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407207).length < 2 ^ (prefixWord ++ tailWord_1407207).sum := by decide
  have hdescent : baseEnd_1407207 < baseStart_1407207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407230 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1407230 : Nat := 118140960795 + 1407230 * 2 ^ 59
def prefixEnd_1407230 : Nat := 4983230072969 + 3 ^ 40 * 1407230 * 2
def baseEnd_1407230 : Nat := 722585381426634439853273

theorem tailTrace_1407230 : CollatzResearch.WordTrace tailWord_1407230 prefixEnd_1407230 722585381426634439853273 := by
  unfold tailWord_1407230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6415736836481690074375393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34217263127902347063335429 6415736836481690074375393)
  ·
    refine ⟨4811802627361267555781545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6415736836481690074375393 4811802627361267555781545)
    ·
      refine ⟨3608851970520950666836159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4811802627361267555781545 3608851970520950666836159)
      ·
        refine ⟨5413277955781426000254239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608851970520950666836159 5413277955781426000254239)
        ·
          refine ⟨8119916933672139000381359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413277955781426000254239 8119916933672139000381359)
          ·
            refine ⟨12179875400508208500572039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8119916933672139000381359 12179875400508208500572039)
            ·
              refine ⟨18269813100762312750858059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12179875400508208500572039 18269813100762312750858059)
              ·
                refine ⟨27404719651143469126287089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18269813100762312750858059 27404719651143469126287089)
                ·
                  refine ⟨20553539738357601844715317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27404719651143469126287089 20553539738357601844715317)
                  ·
                    refine ⟨1926894350471025172942061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20553539738357601844715317 1926894350471025172942061)
                    ·
                      refine ⟨722585381426634439853273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1926894350471025172942061 722585381426634439853273)
                      ·
                        rfl

theorem cell23_1407230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1407230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407230 prefixEnd_1407230 := by exact prefixLift 1407230
  have htrace : WordTrace (prefixWord ++ tailWord_1407230) baseStart_1407230 baseEnd_1407230 := by
    simpa [prefixWord, tailWord_1407230, baseEnd_1407230] using wordTrace_append hprefix tailTrace_1407230
  have hstable : (prefixWord ++ tailWord_1407230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407230).length < 2 ^ (prefixWord ++ tailWord_1407230).sum := by decide
  have hdescent : baseEnd_1407230 < baseStart_1407230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407264 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1407264 : Nat := 118140960795 + 1407264 * 2 ^ 59
def prefixEnd_1407264 : Nat := 4983230072969 + 3 ^ 40 * 1407264 * 2
def baseEnd_1407264 : Nat := 722602839768887306828117

theorem tailTrace_1407264 : CollatzResearch.WordTrace tailWord_1407264 prefixEnd_1407264 722602839768887306828117 := by
  unfold tailWord_1407264
  simp only [CollatzResearch.WordTrace]
  refine ⟨25663567386865172200870423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34218089849153562934493897 25663567386865172200870423)
  ·
    refine ⟨38495351080297758301305635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25663567386865172200870423 38495351080297758301305635)
    ·
      refine ⟨57743026620446637451958453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38495351080297758301305635 57743026620446637451958453)
      ·
        refine ⟨5413408745666872261121105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57743026620446637451958453 5413408745666872261121105)
        ·
          refine ⟨4060056559250154195840829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5413408745666872261121105 4060056559250154195840829)
          ·
            refine ⟨1522521209718807823440311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4060056559250154195840829 1522521209718807823440311)
            ·
              refine ⟨2283781814578211735160467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522521209718807823440311 2283781814578211735160467)
              ·
                refine ⟨3425672721867317602740701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283781814578211735160467 3425672721867317602740701)
                ·
                  refine ⟨1284627270700244101027763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3425672721867317602740701 1284627270700244101027763)
                  ·
                    refine ⟨1926940906050366151541645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1284627270700244101027763 1926940906050366151541645)
                    ·
                      refine ⟨722602839768887306828117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1926940906050366151541645 722602839768887306828117)
                      ·
                        rfl

theorem cell23_1407264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1407264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407264 prefixEnd_1407264 := by exact prefixLift 1407264
  have htrace : WordTrace (prefixWord ++ tailWord_1407264) baseStart_1407264 baseEnd_1407264 := by
    simpa [prefixWord, tailWord_1407264, baseEnd_1407264] using wordTrace_append hprefix tailTrace_1407264
  have hstable : (prefixWord ++ tailWord_1407264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407264).length < 2 ^ (prefixWord ++ tailWord_1407264).sum := by decide
  have hdescent : baseEnd_1407264 < baseStart_1407264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407283 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 6]
def baseStart_1407283 : Nat := 118140960795 + 1407283 * 2 ^ 59
def prefixEnd_1407283 : Nat := 4983230072969 + 3 ^ 40 * 1407283 * 2
def baseEnd_1407283 : Nat := 722612595901322732490529

theorem tailTrace_1407283 : CollatzResearch.WordTrace tailWord_1407283 prefixEnd_1407283 722612595901322732490529 := by
  unfold tailWord_1407283
  simp only [CollatzResearch.WordTrace]
  refine ⟨51327827760661510646682503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34218551840441007097788335 51327827760661510646682503)
  ·
    refine ⟨76991741640992265970023755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51327827760661510646682503 76991741640992265970023755)
    ·
      refine ⟨115487612461488398955035633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76991741640992265970023755 115487612461488398955035633)
      ·
        refine ⟨86615709346116299216276725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115487612461488398955035633 86615709346116299216276725)
        ·
          refine ⟨8120222751198403051525943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86615709346116299216276725 8120222751198403051525943)
          ·
            refine ⟨12180334126797604577288915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8120222751198403051525943 12180334126797604577288915)
            ·
              refine ⟨18270501190196406865933373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12180334126797604577288915 18270501190196406865933373)
              ·
                refine ⟨6851437946323652574725015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18270501190196406865933373 6851437946323652574725015)
                ·
                  refine ⟨10277156919485478862087523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6851437946323652574725015 10277156919485478862087523)
                  ·
                    refine ⟨15415735379228218293131285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10277156919485478862087523 15415735379228218293131285)
                    ·
                      refine ⟨722612595901322732490529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15415735379228218293131285 722612595901322732490529)
                      ·
                        rfl

theorem cell23_1407283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_1407283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407283 prefixEnd_1407283 := by exact prefixLift 1407283
  have htrace : WordTrace (prefixWord ++ tailWord_1407283) baseStart_1407283 baseEnd_1407283 := by
    simpa [prefixWord, tailWord_1407283, baseEnd_1407283] using wordTrace_append hprefix tailTrace_1407283
  have hstable : (prefixWord ++ tailWord_1407283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407283).length < 2 ^ (prefixWord ++ tailWord_1407283).sum := by decide
  have hdescent : baseEnd_1407283 < baseStart_1407283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407284 : List Nat := [2, 5, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1407284 : Nat := 118140960795 + 1407284 * 2 ^ 59
def prefixEnd_1407284 : Nat := 4983230072969 + 3 ^ 40 * 1407284 * 2
def baseEnd_1407284 : Nat := 240871036460659076192675

theorem tailTrace_1407284 : CollatzResearch.WordTrace tailWord_1407284 prefixEnd_1407284 240871036460659076192675 := by
  unfold tailWord_1407284
  simp only [CollatzResearch.WordTrace]
  refine ⟨25663932116828943908734453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34218576155771925211645937 25663932116828943908734453)
  ·
    refine ⟨2405993635952713491443855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25663932116828943908734453 2405993635952713491443855)
    ·
      refine ⟨3608990453929070237165783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2405993635952713491443855 3608990453929070237165783)
      ·
        refine ⟨5413485680893605355748675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608990453929070237165783 5413485680893605355748675)
        ·
          refine ⟨8120228521340408033623013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413485680893605355748675 8120228521340408033623013)
          ·
            refine ⟨1522542847751326506304315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8120228521340408033623013 1522542847751326506304315)
            ·
              refine ⟨2283814271626989759456473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522542847751326506304315 2283814271626989759456473)
              ·
                refine ⟨1712860703720242319592355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2283814271626989759456473 1712860703720242319592355)
                ·
                  refine ⟨2569291055580363479388533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712860703720242319592355 2569291055580363479388533)
                  ·
                    refine ⟨240871036460659076192675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2569291055580363479388533 240871036460659076192675)
                    ·
                      rfl

theorem cell23_1407284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1407284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407284 prefixEnd_1407284 := by exact prefixLift 1407284
  have htrace : WordTrace (prefixWord ++ tailWord_1407284) baseStart_1407284 baseEnd_1407284 := by
    simpa [prefixWord, tailWord_1407284, baseEnd_1407284] using wordTrace_append hprefix tailTrace_1407284
  have hstable : (prefixWord ++ tailWord_1407284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407284).length < 2 ^ (prefixWord ++ tailWord_1407284).sum := by decide
  have hdescent : baseEnd_1407284 < baseStart_1407284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407287 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 3, 2, 2]
def baseStart_1407287 : Nat := 118140960795 + 1407287 * 2 ^ 59
def prefixEnd_1407287 : Nat := 4983230072969 + 3 ^ 40 * 1407287 * 2
def baseEnd_1407287 : Nat := 722614649823940716840511

theorem tailTrace_1407287 : CollatzResearch.WordTrace tailWord_1407287 prefixEnd_1407287 722614649823940716840511 := by
  unfold tailWord_1407287
  simp only [CollatzResearch.WordTrace]
  refine ⟨51327973652647019329828115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34218649101764679553218743 51327973652647019329828115)
  ·
    refine ⟨76991960478970528994742173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51327973652647019329828115 76991960478970528994742173)
    ·
      refine ⟨28871985179613948373028315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76991960478970528994742173 28871985179613948373028315)
      ·
        refine ⟨43307977769420922559542473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28871985179613948373028315 43307977769420922559542473)
        ·
          refine ⟨32480983327065691919656855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43307977769420922559542473 32480983327065691919656855)
          ·
            refine ⟨48721474990598537879485283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32480983327065691919656855 48721474990598537879485283)
            ·
              refine ⟨73082212485897806819227925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48721474990598537879485283 73082212485897806819227925)
              ·
                refine ⟨3425728710276459694651309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73082212485897806819227925 3425728710276459694651309)
                ·
                  refine ⟨1284648266353672385494241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3425728710276459694651309 1284648266353672385494241)
                  ·
                    refine ⟨963486199765254289120681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1284648266353672385494241 963486199765254289120681)
                    ·
                      refine ⟨722614649823940716840511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963486199765254289120681 722614649823940716840511)
                      ·
                        rfl

theorem cell23_1407287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_1407287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407287 prefixEnd_1407287 := by exact prefixLift 1407287
  have htrace : WordTrace (prefixWord ++ tailWord_1407287) baseStart_1407287 baseEnd_1407287 := by
    simpa [prefixWord, tailWord_1407287, baseEnd_1407287] using wordTrace_append hprefix tailTrace_1407287
  have hstable : (prefixWord ++ tailWord_1407287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407287).length < 2 ^ (prefixWord ++ tailWord_1407287).sum := by decide
  have hdescent : baseEnd_1407287 < baseStart_1407287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407297 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1407297 : Nat := 118140960795 + 1407297 * 2 ^ 59
def prefixEnd_1407297 : Nat := 4983230072969 + 3 ^ 40 * 1407297 * 2
def baseEnd_1407297 : Nat := 240873261543495225905155

theorem tailTrace_1407297 : CollatzResearch.WordTrace tailWord_1407297 prefixEnd_1407297 240873261543495225905155 := by
  unfold tailWord_1407297
  simp only [CollatzResearch.WordTrace]
  refine ⟨51328338382610791037692145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34218892255073860691794763 51328338382610791037692145)
  ·
    refine ⟨38496253786958093278269109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51328338382610791037692145 38496253786958093278269109)
    ·
      refine ⟨3609023792527321244837729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38496253786958093278269109 3609023792527321244837729)
      ·
        refine ⟨2706767844395490933628297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3609023792527321244837729 2706767844395490933628297)
        ·
          refine ⟨2030075883296618200221223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2706767844395490933628297 2030075883296618200221223)
          ·
            refine ⟨3045113824944927300331835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030075883296618200221223 3045113824944927300331835)
            ·
              refine ⟨4567670737417390950497753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3045113824944927300331835 4567670737417390950497753)
              ·
                refine ⟨3425753053063043212873315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4567670737417390950497753 3425753053063043212873315)
                ·
                  refine ⟨5138629579594564819309973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425753053063043212873315 5138629579594564819309973)
                  ·
                    refine ⟨240873261543495225905155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5138629579594564819309973 240873261543495225905155)
                    ·
                      rfl

theorem cell23_1407297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1407297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407297 prefixEnd_1407297 := by exact prefixLift 1407297
  have htrace : WordTrace (prefixWord ++ tailWord_1407297) baseStart_1407297 baseEnd_1407297 := by
    simpa [prefixWord, tailWord_1407297, baseEnd_1407297] using wordTrace_append hprefix tailTrace_1407297
  have hstable : (prefixWord ++ tailWord_1407297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407297).length < 2 ^ (prefixWord ++ tailWord_1407297).sum := by decide
  have hdescent : baseEnd_1407297 < baseStart_1407297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407337 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 3]
def baseStart_1407337 : Nat := 118140960795 + 1407337 * 2 ^ 59
def prefixEnd_1407337 : Nat := 4983230072969 + 3 ^ 40 * 1407337 * 2
def baseEnd_1407337 : Nat := 722640323856665521215281

theorem tailTrace_1407337 : CollatzResearch.WordTrace tailWord_1407337 prefixEnd_1407337 722640323856665521215281 := by
  unfold tailWord_1407337
  simp only [CollatzResearch.WordTrace]
  refine ⟨51329797302465877869148265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34219864868310585246098843 51329797302465877869148265)
  ·
    refine ⟨38497347976849408401861199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51329797302465877869148265 38497347976849408401861199)
    ·
      refine ⟨57746021965274112602791799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38497347976849408401861199 57746021965274112602791799)
      ·
        refine ⟨86619032947911168904187699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57746021965274112602791799 86619032947911168904187699)
        ·
          refine ⟨129928549421866753356281549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86619032947911168904187699 129928549421866753356281549)
          ·
            refine ⟨48723206033200032508605581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129928549421866753356281549 48723206033200032508605581)
            ·
              refine ⟨18271202262450012190727093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48723206033200032508605581 18271202262450012190727093)
              ·
                refine ⟨1712925212104688642880665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18271202262450012190727093 1712925212104688642880665)
                ·
                  refine ⟨1284693909078516482160499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1712925212104688642880665 1284693909078516482160499)
                  ·
                    refine ⟨1927040863617774723240749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1284693909078516482160499 1927040863617774723240749)
                    ·
                      refine ⟨722640323856665521215281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1927040863617774723240749 722640323856665521215281)
                      ·
                        rfl

theorem cell23_1407337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 1, 3].length) (baseStart_1407337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407337 prefixEnd_1407337 := by exact prefixLift 1407337
  have htrace : WordTrace (prefixWord ++ tailWord_1407337) baseStart_1407337 baseEnd_1407337 := by
    simpa [prefixWord, tailWord_1407337, baseEnd_1407337] using wordTrace_append hprefix tailTrace_1407337
  have hstable : (prefixWord ++ tailWord_1407337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407337).length < 2 ^ (prefixWord ++ tailWord_1407337).sum := by decide
  have hdescent : baseEnd_1407337 < baseStart_1407337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407353 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 3, 8]
def baseStart_1407353 : Nat := 118140960795 + 1407353 * 2 ^ 59
def prefixEnd_1407353 : Nat := 4983230072969 + 3 ^ 40 * 1407353 * 2
def baseEnd_1407353 : Nat := 240882846515712486205069

theorem tailTrace_1407353 : CollatzResearch.WordTrace tailWord_1407353 prefixEnd_1407353 240882846515712486205069 := by
  unfold tailWord_1407353
  simp only [CollatzResearch.WordTrace]
  refine ⟨51330380870407912601730713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34220253913605275067820475 51330380870407912601730713)
  ·
    refine ⟨38497785652805934451298035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51330380870407912601730713 38497785652805934451298035)
    ·
      refine ⟨57746678479208901676947053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38497785652805934451298035 57746678479208901676947053)
      ·
        refine ⟨21655004429703338128855145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57746678479208901676947053 21655004429703338128855145)
        ·
          refine ⟨16241253322277503596641359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21655004429703338128855145 16241253322277503596641359)
          ·
            refine ⟨24361879983416255394962039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16241253322277503596641359 24361879983416255394962039)
            ·
              refine ⟨36542819975124383092443059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24361879983416255394962039 36542819975124383092443059)
              ·
                refine ⟨54814229962686574638664589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36542819975124383092443059 54814229962686574638664589)
                ·
                  refine ⟨20555336236007465489499221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54814229962686574638664589 20555336236007465489499221)
                  ·
                    refine ⟨240882846515712486205069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20555336236007465489499221 240882846515712486205069)
                    ·
                      rfl

theorem cell23_1407353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_1407353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407353 prefixEnd_1407353 := by exact prefixLift 1407353
  have htrace : WordTrace (prefixWord ++ tailWord_1407353) baseStart_1407353 baseEnd_1407353 := by
    simpa [prefixWord, tailWord_1407353, baseEnd_1407353] using wordTrace_append hprefix tailTrace_1407353
  have hstable : (prefixWord ++ tailWord_1407353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407353).length < 2 ^ (prefixWord ++ tailWord_1407353).sum := by decide
  have hdescent : baseEnd_1407353 < baseStart_1407353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407364 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_1407364 : Nat := 118140960795 + 1407364 * 2 ^ 59
def prefixEnd_1407364 : Nat := 4983230072969 + 3 ^ 40 * 1407364 * 2
def baseEnd_1407364 : Nat := 722654187834336915577657

theorem tailTrace_1407364 : CollatzResearch.WordTrace tailWord_1407364 prefixEnd_1407364 722654187834336915577657 := by
  unfold tailWord_1407364
  simp only [CollatzResearch.WordTrace]
  refine ⟨25665391036684030740190573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34220521382245374320254097 25665391036684030740190573)
  ·
    refine ⟨9624521638756511527571465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25665391036684030740190573 9624521638756511527571465)
    ·
      refine ⟨7218391229067383645678599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9624521638756511527571465 7218391229067383645678599)
      ·
        refine ⟨10827586843601075468517899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7218391229067383645678599 10827586843601075468517899)
        ·
          refine ⟨16241380265401613202776849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10827586843601075468517899 16241380265401613202776849)
          ·
            refine ⟨12181035199051209902082637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16241380265401613202776849 12181035199051209902082637)
            ·
              refine ⟨4567888199644203713280989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12181035199051209902082637 4567888199644203713280989)
              ·
                refine ⟨1712958074866576392480371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4567888199644203713280989 1712958074866576392480371)
                ·
                  refine ⟨2569437112299864588720557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712958074866576392480371 2569437112299864588720557)
                  ·
                    refine ⟨963538917112449220770209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569437112299864588720557 963538917112449220770209)
                    ·
                      refine ⟨722654187834336915577657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963538917112449220770209 722654187834336915577657)
                      ·
                        rfl

theorem cell23_1407364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_1407364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407364 prefixEnd_1407364 := by exact prefixLift 1407364
  have htrace : WordTrace (prefixWord ++ tailWord_1407364) baseStart_1407364 baseEnd_1407364 := by
    simpa [prefixWord, tailWord_1407364, baseEnd_1407364] using wordTrace_append hprefix tailTrace_1407364
  have hstable : (prefixWord ++ tailWord_1407364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407364).length < 2 ^ (prefixWord ++ tailWord_1407364).sum := by decide
  have hdescent : baseEnd_1407364 < baseStart_1407364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407434 : List Nat := [3, 1, 2, 1, 2, 2, 5, 2, 5]
def baseStart_1407434 : Nat := 118140960795 + 1407434 * 2 ^ 59
def prefixEnd_1407434 : Nat := 4983230072969 + 3 ^ 40 * 1407434 * 2
def baseEnd_1407434 : Nat := 80298903497794626855815

theorem tailTrace_1407434 : CollatzResearch.WordTrace tailWord_1407434 prefixEnd_1407434 80298903497794626855815 := by
  unfold tailWord_1407434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12833333795778615858857339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34222223455409642290286237 12833333795778615858857339)
  ·
    refine ⟨19250000693667923788286009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12833333795778615858857339 19250000693667923788286009)
    ·
      refine ⟨14437500520250942841214507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19250000693667923788286009 14437500520250942841214507)
      ·
        refine ⟨21656250780376414261821761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14437500520250942841214507 21656250780376414261821761)
        ·
          refine ⟨16242188085282310696366321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21656250780376414261821761 16242188085282310696366321)
          ·
            refine ⟨12181641063961733022274741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16242188085282310696366321 12181641063961733022274741)
            ·
              refine ⟨1142028849746412470838257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12181641063961733022274741 1142028849746412470838257)
              ·
                refine ⟨856521637309809353128693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1142028849746412470838257 856521637309809353128693)
                ·
                  refine ⟨80298903497794626855815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 856521637309809353128693 80298903497794626855815)
                  ·
                    rfl

theorem cell23_1407434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_1407434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407434 prefixEnd_1407434 := by exact prefixLift 1407434
  have htrace : WordTrace (prefixWord ++ tailWord_1407434) baseStart_1407434 baseEnd_1407434 := by
    simpa [prefixWord, tailWord_1407434, baseEnd_1407434] using wordTrace_append hprefix tailTrace_1407434
  have hstable : (prefixWord ++ tailWord_1407434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407434).length < 2 ^ (prefixWord ++ tailWord_1407434).sum := by decide
  have hdescent : baseEnd_1407434 < baseStart_1407434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407467 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 4]
def baseStart_1407467 : Nat := 118140960795 + 1407467 * 2 ^ 59
def prefixEnd_1407467 : Nat := 4983230072969 + 3 ^ 40 * 1407467 * 2
def baseEnd_1407467 : Nat := 722707076341750012589683

theorem tailTrace_1407467 : CollatzResearch.WordTrace tailWord_1407467 prefixEnd_1407467 722707076341750012589683 := by
  unfold tailWord_1407467
  simp only [CollatzResearch.WordTrace]
  refine ⟨51334538791994910071380655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34223025861329940047587103 51334538791994910071380655)
  ·
    refine ⟨77001808187992365107070983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51334538791994910071380655 77001808187992365107070983)
    ·
      refine ⟨115502712281988547660606475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77001808187992365107070983 115502712281988547660606475)
      ·
        refine ⟨173254068422982821490909713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115502712281988547660606475 173254068422982821490909713)
        ·
          refine ⟨129940551317237116118182285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173254068422982821490909713 129940551317237116118182285)
          ·
            refine ⟨48727706743963918544318357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129940551317237116118182285 48727706743963918544318357)
            ·
              refine ⟨2284111253623308681764923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48727706743963918544318357 2284111253623308681764923)
              ·
                refine ⟨3426166880434963022647385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284111253623308681764923 3426166880434963022647385)
                ·
                  refine ⟨2569625160326222266985539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426166880434963022647385 2569625160326222266985539)
                  ·
                    refine ⟨3854437740489333400478309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2569625160326222266985539 3854437740489333400478309)
                    ·
                      refine ⟨722707076341750012589683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3854437740489333400478309 722707076341750012589683)
                      ·
                        rfl

theorem cell23_1407467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 4].length) (baseStart_1407467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407467 prefixEnd_1407467 := by exact prefixLift 1407467
  have htrace : WordTrace (prefixWord ++ tailWord_1407467) baseStart_1407467 baseEnd_1407467 := by
    simpa [prefixWord, tailWord_1407467, baseEnd_1407467] using wordTrace_append hprefix tailTrace_1407467
  have hstable : (prefixWord ++ tailWord_1407467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407467).length < 2 ^ (prefixWord ++ tailWord_1407467).sum := by decide
  have hdescent : baseEnd_1407467 < baseStart_1407467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407480 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_1407480 : Nat := 118140960795 + 1407480 * 2 ^ 59
def prefixEnd_1407480 : Nat := 4983230072969 + 3 ^ 40 * 1407480 * 2
def baseEnd_1407480 : Nat := 722713751590258461727123

theorem tailTrace_1407480 : CollatzResearch.WordTrace tailWord_1407480 prefixEnd_1407480 722713751590258461727123 := by
  unfold tailWord_1407480
  simp only [CollatzResearch.WordTrace]
  refine ⟨25667506470473906645801947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34223341960631875527735929 25667506470473906645801947)
  ·
    refine ⟨38501259705710859968702921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25667506470473906645801947 38501259705710859968702921)
    ·
      refine ⟨28875944779283144976527191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38501259705710859968702921 28875944779283144976527191)
      ·
        refine ⟨43313917168924717464790787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28875944779283144976527191 43313917168924717464790787)
        ·
          refine ⟨64970875753387076197186181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43313917168924717464790787 64970875753387076197186181)
          ·
            refine ⟨12182039203760076786972409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64970875753387076197186181 12182039203760076786972409)
            ·
              refine ⟨9136529402820057590229307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12182039203760076786972409 9136529402820057590229307)
              ·
                refine ⟨13704794104230086385343961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9136529402820057590229307 13704794104230086385343961)
                ·
                  refine ⟨10278595578172564789007971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13704794104230086385343961 10278595578172564789007971)
                  ·
                    refine ⟨15417893367258847183511957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10278595578172564789007971 15417893367258847183511957)
                    ·
                      refine ⟨722713751590258461727123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15417893367258847183511957 722713751590258461727123)
                      ·
                        rfl

theorem cell23_1407480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_1407480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407480 prefixEnd_1407480 := by exact prefixLift 1407480
  have htrace : WordTrace (prefixWord ++ tailWord_1407480) baseStart_1407480 baseEnd_1407480 := by
    simpa [prefixWord, tailWord_1407480, baseEnd_1407480] using wordTrace_append hprefix tailTrace_1407480
  have hstable : (prefixWord ++ tailWord_1407480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407480).length < 2 ^ (prefixWord ++ tailWord_1407480).sum := by decide
  have hdescent : baseEnd_1407480 < baseStart_1407480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407487 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 3]
def baseStart_1407487 : Nat := 118140960795 + 1407487 * 2 ^ 59
def prefixEnd_1407487 : Nat := 4983230072969 + 3 ^ 40 * 1407487 * 2
def baseEnd_1407487 : Nat := 722717345954839934339591

theorem tailTrace_1407487 : CollatzResearch.WordTrace tailWord_1407487 prefixEnd_1407487 722717345954839934339591 := by
  unfold tailWord_1407487
  simp only [CollatzResearch.WordTrace]
  refine ⟨51335268251922453487108715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34223512167948302324739143 51335268251922453487108715)
  ·
    refine ⟨77002902377883680230663073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51335268251922453487108715 77002902377883680230663073)
    ·
      refine ⟨57752176783412760172997305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77002902377883680230663073 57752176783412760172997305)
      ·
        refine ⟨43314132587559570129747979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57752176783412760172997305 43314132587559570129747979)
        ·
          refine ⟨64971198881339355194621969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43314132587559570129747979 64971198881339355194621969)
          ·
            refine ⟨48728399161004516395966477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64971198881339355194621969 48728399161004516395966477)
            ·
              refine ⟨18273149685376693648487429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48728399161004516395966477 18273149685376693648487429)
              ·
                refine ⟨3426215566008130059091393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18273149685376693648487429 3426215566008130059091393)
                ·
                  refine ⟨2569661674506097544318545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426215566008130059091393 2569661674506097544318545)
                  ·
                    refine ⟨1927246255879573158238909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2569661674506097544318545 1927246255879573158238909)
                    ·
                      refine ⟨722717345954839934339591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1927246255879573158238909 722717345954839934339591)
                      ·
                        rfl

theorem cell23_1407487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_1407487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407487 prefixEnd_1407487 := by exact prefixLift 1407487
  have htrace : WordTrace (prefixWord ++ tailWord_1407487) baseStart_1407487 baseEnd_1407487 := by
    simpa [prefixWord, tailWord_1407487, baseEnd_1407487] using wordTrace_append hprefix tailTrace_1407487
  have hstable : (prefixWord ++ tailWord_1407487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407487).length < 2 ^ (prefixWord ++ tailWord_1407487).sum := by decide
  have hdescent : baseEnd_1407487 < baseStart_1407487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407511 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 3, 4]
def baseStart_1407511 : Nat := 118140960795 + 1407511 * 2 ^ 59
def prefixEnd_1407511 : Nat := 4983230072969 + 3 ^ 40 * 1407511 * 2
def baseEnd_1407511 : Nat := 240909889830182613479827

theorem tailTrace_1407511 : CollatzResearch.WordTrace tailWord_1407511 prefixEnd_1407511 240909889830182613479827 := by
  unfold tailWord_1407511
  simp only [CollatzResearch.WordTrace]
  refine ⟨51336143603835505585982387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34224095735890337057321591 51336143603835505585982387)
  ·
    refine ⟨77004215405753258378973581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51336143603835505585982387 77004215405753258378973581)
    ·
      refine ⟨28876580777157471892115093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77004215405753258378973581 28876580777157471892115093)
      ·
        refine ⟨1353589723929256494942895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28876580777157471892115093 1353589723929256494942895)
        ·
          refine ⟨2030384585893884742414343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353589723929256494942895 2030384585893884742414343)
          ·
            refine ⟨3045576878840827113621515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030384585893884742414343 3045576878840827113621515)
            ·
              refine ⟨4568365318261240670432273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3045576878840827113621515 4568365318261240670432273)
              ·
                refine ⟨3426273988695930502824205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4568365318261240670432273 3426273988695930502824205)
                ·
                  refine ⟨1284852745760973938559077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3426273988695930502824205 1284852745760973938559077)
                  ·
                    refine ⟨240909889830182613479827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1284852745760973938559077 240909889830182613479827)
                    ·
                      rfl

theorem cell23_1407511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_1407511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407511 prefixEnd_1407511 := by exact prefixLift 1407511
  have htrace : WordTrace (prefixWord ++ tailWord_1407511) baseStart_1407511 baseEnd_1407511 := by
    simpa [prefixWord, tailWord_1407511, baseEnd_1407511] using wordTrace_append hprefix tailTrace_1407511
  have hstable : (prefixWord ++ tailWord_1407511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407511).length < 2 ^ (prefixWord ++ tailWord_1407511).sum := by decide
  have hdescent : baseEnd_1407511 < baseStart_1407511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407528 : List Nat := [2, 1, 5, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1407528 : Nat := 118140960795 + 1407528 * 2 ^ 59
def prefixEnd_1407528 : Nat := 4983230072969 + 3 ^ 40 * 1407528 * 2
def baseEnd_1407528 : Nat := 240912799553891424642301

theorem tailTrace_1407528 : CollatzResearch.WordTrace tailWord_1407528 prefixEnd_1407528 240912799553891424642301 := by
  unfold tailWord_1407528
  simp only [CollatzResearch.WordTrace]
  refine ⟨25668381822386958744675619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34224509096515944992900825 25668381822386958744675619)
  ·
    refine ⟨38502572733580438117013429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25668381822386958744675619 38502572733580438117013429)
    ·
      refine ⟨3609616193773166073470009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38502572733580438117013429 3609616193773166073470009)
      ·
        refine ⟨2707212145329874555102507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3609616193773166073470009 2707212145329874555102507)
        ·
          refine ⟨4060818217994811832653761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707212145329874555102507 4060818217994811832653761)
          ·
            refine ⟨3045613663496108874490321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4060818217994811832653761 3045613663496108874490321)
            ·
              refine ⟨2284210247622081655867741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3045613663496108874490321 2284210247622081655867741)
              ·
                refine ⟨856578842858280620950403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2284210247622081655867741 856578842858280620950403)
                ·
                  refine ⟨1284868264287420931425605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856578842858280620950403 1284868264287420931425605)
                  ·
                    refine ⟨240912799553891424642301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1284868264287420931425605 240912799553891424642301)
                    ·
                      rfl

theorem cell23_1407528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1407528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407528 prefixEnd_1407528 := by exact prefixLift 1407528
  have htrace : WordTrace (prefixWord ++ tailWord_1407528) baseStart_1407528 baseEnd_1407528 := by
    simpa [prefixWord, tailWord_1407528, baseEnd_1407528] using wordTrace_append hprefix tailTrace_1407528
  have hstable : (prefixWord ++ tailWord_1407528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407528).length < 2 ^ (prefixWord ++ tailWord_1407528).sum := by decide
  have hdescent : baseEnd_1407528 < baseStart_1407528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407544 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 4, 3, 2]
def baseStart_1407544 : Nat := 118140960795 + 1407544 * 2 ^ 59
def prefixEnd_1407544 : Nat := 4983230072969 + 3 ^ 40 * 1407544 * 2
def baseEnd_1407544 : Nat := 722746614352146211326829

theorem tailTrace_1407544 : CollatzResearch.WordTrace tailWord_1407544 prefixEnd_1407544 722746614352146211326829 := by
  unfold tailWord_1407544
  simp only [CollatzResearch.WordTrace]
  refine ⟨25668673606357976110966843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34224898141810634814622457 25668673606357976110966843)
  ·
    refine ⟨38503010409536964166450265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25668673606357976110966843 38503010409536964166450265)
    ·
      refine ⟨28877257807152723124837699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38503010409536964166450265 28877257807152723124837699)
      ·
        refine ⟨43315886710729084687256549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28877257807152723124837699 43315886710729084687256549)
        ·
          refine ⟨8121728758261703378860603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43315886710729084687256549 8121728758261703378860603)
          ·
            refine ⟨12182593137392555068290905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8121728758261703378860603 12182593137392555068290905)
            ·
              refine ⟨9136944853044416301218179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12182593137392555068290905 9136944853044416301218179)
              ·
                refine ⟨13705417279566624451827269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9136944853044416301218179 13705417279566624451827269)
                ·
                  refine ⟨2569765739918742084717613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13705417279566624451827269 2569765739918742084717613)
                  ·
                    refine ⟨963662152469528281769105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569765739918742084717613 963662152469528281769105)
                    ·
                      refine ⟨722746614352146211326829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963662152469528281769105 722746614352146211326829)
                      ·
                        rfl

theorem cell23_1407544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_1407544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407544 prefixEnd_1407544 := by exact prefixLift 1407544
  have htrace : WordTrace (prefixWord ++ tailWord_1407544) baseStart_1407544 baseEnd_1407544 := by
    simpa [prefixWord, tailWord_1407544, baseEnd_1407544] using wordTrace_append hprefix tailTrace_1407544
  have hstable : (prefixWord ++ tailWord_1407544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407544).length < 2 ^ (prefixWord ++ tailWord_1407544).sum := by decide
  have hdescent : baseEnd_1407544 < baseStart_1407544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407551 : List Nat := [1, 1, 2, 2, 3, 2, 1, 6, 1, 1, 3]
def baseStart_1407551 : Nat := 118140960795 + 1407551 * 2 ^ 59
def prefixEnd_1407551 : Nat := 4983230072969 + 3 ^ 40 * 1407551 * 2
def baseEnd_1407551 : Nat := 722750208716727683939297

theorem tailTrace_1407551 : CollatzResearch.WordTrace tailWord_1407551 prefixEnd_1407551 722750208716727683939297 := by
  unfold tailWord_1407551
  simp only [CollatzResearch.WordTrace]
  refine ⟨51337602523690592417438507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34225068349127061611625671 51337602523690592417438507)
  ·
    refine ⟨77006403785535888626157761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51337602523690592417438507 77006403785535888626157761)
    ·
      refine ⟨57754802839151916469618321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77006403785535888626157761 57754802839151916469618321)
      ·
        refine ⟨43316102129363937352213741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57754802839151916469618321 43316102129363937352213741)
        ·
          refine ⟨16243538298511476507080153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43316102129363937352213741 16243538298511476507080153)
          ·
            refine ⟨12182653723883607380310115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16243538298511476507080153 12182653723883607380310115)
            ·
              refine ⟨18273980585825411070465173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12182653723883607380310115 18273980585825411070465173)
              ·
                refine ⟨856592839960566143928055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18273980585825411070465173 856592839960566143928055)
                ·
                  refine ⟨1284889259940849215892083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856592839960566143928055 1284889259940849215892083)
                  ·
                    refine ⟨1927333889911273823838125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1284889259940849215892083 1927333889911273823838125)
                    ·
                      refine ⟨722750208716727683939297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1927333889911273823838125 722750208716727683939297)
                      ·
                        rfl

theorem cell23_1407551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 1, 1, 3].length) (baseStart_1407551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407551 prefixEnd_1407551 := by exact prefixLift 1407551
  have htrace : WordTrace (prefixWord ++ tailWord_1407551) baseStart_1407551 baseEnd_1407551 := by
    simpa [prefixWord, tailWord_1407551, baseEnd_1407551] using wordTrace_append hprefix tailTrace_1407551
  have hstable : (prefixWord ++ tailWord_1407551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407551).length < 2 ^ (prefixWord ++ tailWord_1407551).sum := by decide
  have hdescent : baseEnd_1407551 < baseStart_1407551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407558 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_1407558 : Nat := 118140960795 + 1407558 * 2 ^ 59
def prefixEnd_1407558 : Nat := 4983230072969 + 3 ^ 40 * 1407558 * 2
def baseEnd_1407558 : Nat := 80305978120145461839085

theorem tailTrace_1407558 : CollatzResearch.WordTrace tailWord_1407558 prefixEnd_1407558 80305978120145461839085 := by
  unfold tailWord_1407558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604308057333288519154479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34225238556443488408628885 1604308057333288519154479)
  ·
    refine ⟨2406462085999932778731719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1604308057333288519154479 2406462085999932778731719)
    ·
      refine ⟨3609693128999899168097579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2406462085999932778731719 3609693128999899168097579)
      ·
        refine ⟨5414539693499848752146369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3609693128999899168097579 5414539693499848752146369)
        ·
          refine ⟨4060904770124886564109777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5414539693499848752146369 4060904770124886564109777)
          ·
            refine ⟨3045678577593664923082333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4060904770124886564109777 3045678577593664923082333)
            ·
              refine ⟨1142129466597624346155875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3045678577593664923082333 1142129466597624346155875)
              ·
                refine ⟨1713194199896436519233813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142129466597624346155875 1713194199896436519233813)
                ·
                  refine ⟨80305978120145461839085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1713194199896436519233813 80305978120145461839085)
                  ·
                    rfl

theorem cell23_1407558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_1407558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407558 prefixEnd_1407558 := by exact prefixLift 1407558
  have htrace : WordTrace (prefixWord ++ tailWord_1407558) baseStart_1407558 baseEnd_1407558 := by
    simpa [prefixWord, tailWord_1407558, baseEnd_1407558] using wordTrace_append hprefix tailTrace_1407558
  have hstable : (prefixWord ++ tailWord_1407558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407558).length < 2 ^ (prefixWord ++ tailWord_1407558).sum := by decide
  have hdescent : baseEnd_1407558 < baseStart_1407558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407567 : List Nat := [1, 1, 2, 1, 1, 2, 7, 1, 1, 6]
def baseStart_1407567 : Nat := 118140960795 + 1407567 * 2 ^ 59
def prefixEnd_1407567 : Nat := 4983230072969 + 3 ^ 40 * 1407567 * 2
def baseEnd_1407567 : Nat := 240919474802399873779741

theorem tailTrace_1407567 : CollatzResearch.WordTrace tailWord_1407567 prefixEnd_1407567 240919474802399873779741 := by
  unfold tailWord_1407567
  simp only [CollatzResearch.WordTrace]
  refine ⟨51338186091632627150020955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34225457394421751433347303 51338186091632627150020955)
  ·
    refine ⟨77007279137448940725031433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51338186091632627150020955 77007279137448940725031433)
    ·
      refine ⟨57755459353086705543773575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77007279137448940725031433 57755459353086705543773575)
      ·
        refine ⟨86633189029630058315660363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57755459353086705543773575 86633189029630058315660363)
        ·
          refine ⟨129949783544445087473490545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86633189029630058315660363 129949783544445087473490545)
          ·
            refine ⟨97462337658333815605117909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129949783544445087473490545 97462337658333815605117909)
            ·
              refine ⟨2284273538867198803244951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 97462337658333815605117909 2284273538867198803244951)
              ·
                refine ⟨3426410308300798204867427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284273538867198803244951 3426410308300798204867427)
                ·
                  refine ⟨5139615462451197307301141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426410308300798204867427 5139615462451197307301141)
                  ·
                    refine ⟨240919474802399873779741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5139615462451197307301141 240919474802399873779741)
                    ·
                      rfl

theorem cell23_1407567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 6].length) (baseStart_1407567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407567 prefixEnd_1407567 := by exact prefixLift 1407567
  have htrace : WordTrace (prefixWord ++ tailWord_1407567) baseStart_1407567 baseEnd_1407567 := by
    simpa [prefixWord, tailWord_1407567, baseEnd_1407567] using wordTrace_append hprefix tailTrace_1407567
  have hstable : (prefixWord ++ tailWord_1407567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407567).length < 2 ^ (prefixWord ++ tailWord_1407567).sum := by decide
  have hdescent : baseEnd_1407567 < baseStart_1407567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407587 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1407587 : Nat := 118140960795 + 1407587 * 2 ^ 59
def prefixEnd_1407587 : Nat := 4983230072969 + 3 ^ 40 * 1407587 * 2
def baseEnd_1407587 : Nat := 722768694020289543089131

theorem tailTrace_1407587 : CollatzResearch.WordTrace tailWord_1407587 prefixEnd_1407587 722768694020289543089131 := by
  unfold tailWord_1407587
  simp only [CollatzResearch.WordTrace]
  refine ⟨51338915551560170565749015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34225943701040113710499343 51338915551560170565749015)
  ·
    refine ⟨77008373327340255848623523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51338915551560170565749015 77008373327340255848623523)
    ·
      refine ⟨115512559991010383772935285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77008373327340255848623523 115512559991010383772935285)
      ·
        refine ⟨10829302499157223478712683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115512559991010383772935285 10829302499157223478712683)
        ·
          refine ⟨16243953748735835218069025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10829302499157223478712683 16243953748735835218069025)
          ·
            refine ⟨12182965311551876413551769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16243953748735835218069025 12182965311551876413551769)
            ·
              refine ⟨9137223983663907310163827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12182965311551876413551769 9137223983663907310163827)
              ·
                refine ⟨13705835975495860965245741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9137223983663907310163827 13705835975495860965245741)
                ·
                  refine ⟨5139688490810947861967153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13705835975495860965245741 5139688490810947861967153)
                  ·
                    refine ⟨3854766368108210896475365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5139688490810947861967153 3854766368108210896475365)
                    ·
                      refine ⟨722768694020289543089131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3854766368108210896475365 722768694020289543089131)
                      ·
                        rfl

theorem cell23_1407587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1407587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407587 prefixEnd_1407587 := by exact prefixLift 1407587
  have htrace : WordTrace (prefixWord ++ tailWord_1407587) baseStart_1407587 baseEnd_1407587 := by
    simpa [prefixWord, tailWord_1407587, baseEnd_1407587] using wordTrace_append hprefix tailTrace_1407587
  have hstable : (prefixWord ++ tailWord_1407587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407587).length < 2 ^ (prefixWord ++ tailWord_1407587).sum := by decide
  have hdescent : baseEnd_1407587 < baseStart_1407587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407594 : List Nat := [3, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_1407594 : Nat := 118140960795 + 1407594 * 2 ^ 59
def prefixEnd_1407594 : Nat := 4983230072969 + 3 ^ 40 * 1407594 * 2
def baseEnd_1407594 : Nat := 722772288384871015701599

theorem tailTrace_1407594 : CollatzResearch.WordTrace tailWord_1407594 prefixEnd_1407594 722772288384871015701599 := by
  unfold tailWord_1407594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12834792715633702690313459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34226113908356540507502557 12834792715633702690313459)
  ·
    refine ⟨19252189073450554035470189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12834792715633702690313459 19252189073450554035470189)
    ·
      refine ⟨7219570902543957763301321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19252189073450554035470189 7219570902543957763301321)
      ·
        refine ⟨5414678176907968322475991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7219570902543957763301321 5414678176907968322475991)
        ·
          refine ⟨8122017265361952483713987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5414678176907968322475991 8122017265361952483713987)
          ·
            refine ⟨12183025898042928725570981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8122017265361952483713987 12183025898042928725570981)
            ·
              refine ⟨2284317355883049136044559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12183025898042928725570981 2284317355883049136044559)
              ·
                refine ⟨3426476033824573704066839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284317355883049136044559 3426476033824573704066839)
                ·
                  refine ⟨5139714050736860556100259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426476033824573704066839 5139714050736860556100259)
                  ·
                    refine ⟨7709571076105290834150389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5139714050736860556100259 7709571076105290834150389)
                    ·
                      refine ⟨722772288384871015701599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7709571076105290834150389 722772288384871015701599)
                      ·
                        rfl

theorem cell23_1407594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_1407594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407594 prefixEnd_1407594 := by exact prefixLift 1407594
  have htrace : WordTrace (prefixWord ++ tailWord_1407594) baseStart_1407594 baseEnd_1407594 := by
    simpa [prefixWord, tailWord_1407594, baseEnd_1407594] using wordTrace_append hprefix tailTrace_1407594
  have hstable : (prefixWord ++ tailWord_1407594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407594).length < 2 ^ (prefixWord ++ tailWord_1407594).sum := by decide
  have hdescent : baseEnd_1407594 < baseStart_1407594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407597 : List Nat := [1, 5, 1, 1, 3, 1, 11]
def baseStart_1407597 : Nat := 118140960795 + 1407597 * 2 ^ 59
def prefixEnd_1407597 : Nat := 4983230072969 + 3 ^ 40 * 1407597 * 2
def baseEnd_1407597 : Nat := 8923133689220179061285

theorem tailTrace_1407597 : CollatzResearch.WordTrace tailWord_1407597 prefixEnd_1407597 8923133689220179061285 := by
  unfold tailWord_1407597
  simp only [CollatzResearch.WordTrace]
  refine ⟨51339280281523942273613045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34226186854349294849075363 51339280281523942273613045)
  ·
    refine ⟨4813057526392869588151223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51339280281523942273613045 4813057526392869588151223)
    ·
      refine ⟨7219586289589304382226835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4813057526392869588151223 7219586289589304382226835)
      ·
        refine ⟨10829379434383956573340253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7219586289589304382226835 10829379434383956573340253)
        ·
          refine ⟨4061017287893983715002595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10829379434383956573340253 4061017287893983715002595)
          ·
            refine ⟨6091525931840975572503893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4061017287893983715002595 6091525931840975572503893)
            ·
              refine ⟨8923133689220179061285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6091525931840975572503893 8923133689220179061285)
              ·
                rfl

theorem cell23_1407597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 11].length) (baseStart_1407597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407597 prefixEnd_1407597 := by exact prefixLift 1407597
  have htrace : WordTrace (prefixWord ++ tailWord_1407597) baseStart_1407597 baseEnd_1407597 := by
    simpa [prefixWord, tailWord_1407597, baseEnd_1407597] using wordTrace_append hprefix tailTrace_1407597
  have hstable : (prefixWord ++ tailWord_1407597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407597).length < 2 ^ (prefixWord ++ tailWord_1407597).sum := by decide
  have hdescent : baseEnd_1407597 < baseStart_1407597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407617 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1407617 : Nat := 118140960795 + 1407617 * 2 ^ 59
def prefixEnd_1407617 : Nat := 4983230072969 + 3 ^ 40 * 1407617 * 2
def baseEnd_1407617 : Nat := 722784098439924425713993

theorem tailTrace_1407617 : CollatzResearch.WordTrace tailWord_1407617 prefixEnd_1407617 722784098439924425713993 := by
  unfold tailWord_1407617
  simp only [CollatzResearch.WordTrace]
  refine ⟨51340009741451485689341105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34226673160967657126227403 51340009741451485689341105)
  ·
    refine ⟨38505007306088614267005829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51340009741451485689341105 38505007306088614267005829)
    ·
      refine ⟨7219688869891615175063593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38505007306088614267005829 7219688869891615175063593)
      ·
        refine ⟨5414766652418711381297695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7219688869891615175063593 5414766652418711381297695)
        ·
          refine ⟨8122149978628067071946543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5414766652418711381297695 8122149978628067071946543)
          ·
            refine ⟨12183224967942100607919815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8122149978628067071946543 12183224967942100607919815)
            ·
              refine ⟨18274837451913150911879723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12183224967942100607919815 18274837451913150911879723)
              ·
                refine ⟨27412256177869726367819585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18274837451913150911879723 27412256177869726367819585)
                ·
                  refine ⟨20559192133402294775864689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27412256177869726367819585 20559192133402294775864689)
                  ·
                    refine ⟨15419394100051721081898517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20559192133402294775864689 15419394100051721081898517)
                    ·
                      refine ⟨722784098439924425713993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15419394100051721081898517 722784098439924425713993)
                      ·
                        rfl

theorem cell23_1407617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1407617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407617 prefixEnd_1407617 := by exact prefixLift 1407617
  have htrace : WordTrace (prefixWord ++ tailWord_1407617) baseStart_1407617 baseEnd_1407617 := by
    simpa [prefixWord, tailWord_1407617, baseEnd_1407617] using wordTrace_append hprefix tailTrace_1407617
  have hstable : (prefixWord ++ tailWord_1407617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407617).length < 2 ^ (prefixWord ++ tailWord_1407617).sum := by decide
  have hdescent : baseEnd_1407617 < baseStart_1407617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407664 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 5, 4, 2]
def baseStart_1407664 : Nat := 118140960795 + 1407664 * 2 ^ 59
def prefixEnd_1407664 : Nat := 4983230072969 + 3 ^ 40 * 1407664 * 2
def baseEnd_1407664 : Nat := 722808232030685741826277

theorem tailTrace_1407664 : CollatzResearch.WordTrace tailWord_1407664 prefixEnd_1407664 722808232030685741826277 := by
  unfold tailWord_1407664
  simp only [CollatzResearch.WordTrace]
  refine ⟨25670861986140606358151023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34227815981520808477534697 25670861986140606358151023)
  ·
    refine ⟨38506292979210909537226535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25670861986140606358151023 38506292979210909537226535)
    ·
      refine ⟨57759439468816364305839803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38506292979210909537226535 57759439468816364305839803)
      ·
        refine ⟨86639159203224546458759705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57759439468816364305839803 86639159203224546458759705)
        ·
          refine ⟨64979369402418409844069779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86639159203224546458759705 64979369402418409844069779)
          ·
            refine ⟨97469054103627614766104669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64979369402418409844069779 97469054103627614766104669)
            ·
              refine ⟨36550895288860355537289251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97469054103627614766104669 36550895288860355537289251)
              ·
                refine ⟨54826342933290533305933877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36550895288860355537289251 54826342933290533305933877)
                ·
                  refine ⟨5139969649995987497431301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54826342933290533305933877 5139969649995987497431301)
                  ·
                    refine ⟨963744309374247655768369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139969649995987497431301 963744309374247655768369)
                    ·
                      refine ⟨722808232030685741826277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963744309374247655768369 722808232030685741826277)
                      ·
                        rfl

theorem cell23_1407664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 5, 4, 2].length) (baseStart_1407664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407664 prefixEnd_1407664 := by exact prefixLift 1407664
  have htrace : WordTrace (prefixWord ++ tailWord_1407664) baseStart_1407664 baseEnd_1407664 := by
    simpa [prefixWord, tailWord_1407664, baseEnd_1407664] using wordTrace_append hprefix tailTrace_1407664
  have hstable : (prefixWord ++ tailWord_1407664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407664).length < 2 ^ (prefixWord ++ tailWord_1407664).sum := by decide
  have hdescent : baseEnd_1407664 < baseStart_1407664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407715 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 2, 2, 2]
def baseStart_1407715 : Nat := 118140960795 + 1407715 * 2 ^ 59
def prefixEnd_1407715 : Nat := 4983230072969 + 3 ^ 40 * 1407715 * 2
def baseEnd_1407715 : Nat := 722834419544065042288543

theorem tailTrace_1407715 : CollatzResearch.WordTrace tailWord_1407715 prefixEnd_1407715 722834419544065042288543 := by
  unfold tailWord_1407715
  simp only [CollatzResearch.WordTrace]
  refine ⟨51343584095096448426408599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34229056063397632284272399 51343584095096448426408599)
  ·
    refine ⟨77015376142644672639612899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51343584095096448426408599 77015376142644672639612899)
    ·
      refine ⟨115523064213967008959419349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77015376142644672639612899 115523064213967008959419349)
      ·
        refine ⟨2707571817514851772486391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 115523064213967008959419349 2707571817514851772486391)
        ·
          refine ⟨4061357726272277658729587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707571817514851772486391 4061357726272277658729587)
          ·
            refine ⟨6092036589408416488094381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4061357726272277658729587 6092036589408416488094381)
            ·
              refine ⟨2284513721028156183035393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6092036589408416488094381 2284513721028156183035393)
              ·
                refine ⟨1713385290771117137276545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284513721028156183035393 1713385290771117137276545)
                ·
                  refine ⟨1285038968078337852957409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1713385290771117137276545 1285038968078337852957409)
                  ·
                    refine ⟨963779226058753389718057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1285038968078337852957409 963779226058753389718057)
                    ·
                      refine ⟨722834419544065042288543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963779226058753389718057 722834419544065042288543)
                      ·
                        rfl

theorem cell23_1407715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_1407715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407715 prefixEnd_1407715 := by exact prefixLift 1407715
  have htrace : WordTrace (prefixWord ++ tailWord_1407715) baseStart_1407715 baseEnd_1407715 := by
    simpa [prefixWord, tailWord_1407715, baseEnd_1407715] using wordTrace_append hprefix tailTrace_1407715
  have hstable : (prefixWord ++ tailWord_1407715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407715).length < 2 ^ (prefixWord ++ tailWord_1407715).sum := by decide
  have hdescent : baseEnd_1407715 < baseStart_1407715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407734 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_1407734 : Nat := 118140960795 + 1407734 * 2 ^ 59
def prefixEnd_1407734 : Nat := 4983230072969 + 3 ^ 40 * 1407734 * 2
def baseEnd_1407734 : Nat := 240948058558833489316985

theorem tailTrace_1407734 : CollatzResearch.WordTrace tailWord_1407734 prefixEnd_1407734 240948058558833489316985 := by
  unfold tailWord_1407734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3209017317626725916959391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34229518054685076447566837 3209017317626725916959391)
  ·
    refine ⟨4813525976440088875439087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3209017317626725916959391 4813525976440088875439087)
    ·
      refine ⟨7220288964660133313158631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4813525976440088875439087 7220288964660133313158631)
      ·
        refine ⟨10830433446990199969737947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7220288964660133313158631 10830433446990199969737947)
        ·
          refine ⟨16245650170485299954606921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10830433446990199969737947 16245650170485299954606921)
          ·
            refine ⟨12184237627863974965955191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16245650170485299954606921 12184237627863974965955191)
            ·
              refine ⟨18276356441795962448932787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12184237627863974965955191 18276356441795962448932787)
              ·
                refine ⟨27414534662693943673399181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18276356441795962448932787 27414534662693943673399181)
                ·
                  refine ⟨10280450498510228877524693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27414534662693943673399181 10280450498510228877524693)
                  ·
                    refine ⟨240948058558833489316985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10280450498510228877524693 240948058558833489316985)
                    ·
                      rfl

theorem cell23_1407734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_1407734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407734 prefixEnd_1407734 := by exact prefixLift 1407734
  have htrace : WordTrace (prefixWord ++ tailWord_1407734) baseStart_1407734 baseEnd_1407734 := by
    simpa [prefixWord, tailWord_1407734, baseEnd_1407734] using wordTrace_append hprefix tailTrace_1407734
  have hstable : (prefixWord ++ tailWord_1407734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407734).length < 2 ^ (prefixWord ++ tailWord_1407734).sum := by decide
  have hdescent : baseEnd_1407734 < baseStart_1407734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407747 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 1, 10]
def baseStart_1407747 : Nat := 118140960795 + 1407747 * 2 ^ 59
def prefixEnd_1407747 : Nat := 4983230072969 + 3 ^ 40 * 1407747 * 2
def baseEnd_1407747 : Nat := 240950283641669639029465

theorem tailTrace_1407747 : CollatzResearch.WordTrace tailWord_1407747 prefixEnd_1407747 240950283641669639029465 := by
  unfold tailWord_1407747
  simp only [CollatzResearch.WordTrace]
  refine ⟨51344751230980517891573495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34229834153987011927715663 51344751230980517891573495)
  ·
    refine ⟨77017126846470776837360243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51344751230980517891573495 77017126846470776837360243)
    ·
      refine ⟨115525690269706165256040365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77017126846470776837360243 115525690269706165256040365)
      ·
        refine ⟨43322133851139811971015137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115525690269706165256040365 43322133851139811971015137)
        ·
          refine ⟨32491600388354858978261353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43322133851139811971015137 32491600388354858978261353)
          ·
            refine ⟨24368700291266144233696015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32491600388354858978261353 24368700291266144233696015)
            ·
              refine ⟨36553050436899216350544023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24368700291266144233696015 36553050436899216350544023)
              ·
                refine ⟨54829575655348824525816035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36553050436899216350544023 54829575655348824525816035)
                ·
                  refine ⟨82244363483023236788724053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54829575655348824525816035 82244363483023236788724053)
                  ·
                    refine ⟨240950283641669639029465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 82244363483023236788724053 240950283641669639029465)
                    ·
                      rfl

theorem cell23_1407747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 10].length) (baseStart_1407747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407747 prefixEnd_1407747 := by exact prefixLift 1407747
  have htrace : WordTrace (prefixWord ++ tailWord_1407747) baseStart_1407747 baseEnd_1407747 := by
    simpa [prefixWord, tailWord_1407747, baseEnd_1407747] using wordTrace_append hprefix tailTrace_1407747
  have hstable : (prefixWord ++ tailWord_1407747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407747).length < 2 ^ (prefixWord ++ tailWord_1407747).sum := by decide
  have hdescent : baseEnd_1407747 < baseStart_1407747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407754 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1407754 : Nat := 118140960795 + 1407754 * 2 ^ 59
def prefixEnd_1407754 : Nat := 4983230072969 + 3 ^ 40 * 1407754 * 2
def baseEnd_1407754 : Nat := 722854445289590389700863

theorem tailTrace_1407754 : CollatzResearch.WordTrace tailWord_1407754 prefixEnd_1407754 722854445289590389700863 := by
  unfold tailWord_1407754
  simp only [CollatzResearch.WordTrace]
  refine ⟨12836251635488789521769579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34230004361303438724718877 12836251635488789521769579)
  ·
    refine ⟨19254377453233184282654369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12836251635488789521769579 19254377453233184282654369)
    ·
      refine ⟨14440783089924888211990777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19254377453233184282654369 14440783089924888211990777)
      ·
        refine ⟨10830587317443666158993083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14440783089924888211990777 10830587317443666158993083)
        ·
          refine ⟨16245880976165499238489625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10830587317443666158993083 16245880976165499238489625)
          ·
            refine ⟨12184410732124124428867219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16245880976165499238489625 12184410732124124428867219)
            ·
              refine ⟨18276616098186186643300829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12184410732124124428867219 18276616098186186643300829)
              ·
                refine ⟨6853731036819819991237811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18276616098186186643300829 6853731036819819991237811)
                ·
                  refine ⟨10280596555229729986856717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6853731036819819991237811 10280596555229729986856717)
                  ·
                    refine ⟨3855223708211148745071269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10280596555229729986856717 3855223708211148745071269)
                    ·
                      refine ⟨722854445289590389700863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3855223708211148745071269 722854445289590389700863)
                      ·
                        rfl

theorem cell23_1407754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1407754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407754 prefixEnd_1407754 := by exact prefixLift 1407754
  have htrace : WordTrace (prefixWord ++ tailWord_1407754) baseStart_1407754 baseEnd_1407754 := by
    simpa [prefixWord, tailWord_1407754, baseEnd_1407754] using wordTrace_append hprefix tailTrace_1407754
  have hstable : (prefixWord ++ tailWord_1407754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407754).length < 2 ^ (prefixWord ++ tailWord_1407754).sum := by decide
  have hdescent : baseEnd_1407754 < baseStart_1407754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407828 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 6]
def baseStart_1407828 : Nat := 118140960795 + 1407828 * 2 ^ 59
def prefixEnd_1407828 : Nat := 4983230072969 + 3 ^ 40 * 1407828 * 2
def baseEnd_1407828 : Nat := 80321382539780344463947

theorem tailTrace_1407828 : CollatzResearch.WordTrace tailWord_1407828 prefixEnd_1407828 80321382539780344463947 := by
  unfold tailWord_1407828
  simp only [CollatzResearch.WordTrace]
  refine ⟨25673852771843534362636069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34231803695791379150181425 25673852771843534362636069)
  ·
    refine ⟨4813847394720662692994263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25673852771843534362636069 4813847394720662692994263)
    ·
      refine ⟨7220771092080994039491395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4813847394720662692994263 7220771092080994039491395)
      ·
        refine ⟨10831156638121491059237093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7220771092080994039491395 10831156638121491059237093)
        ·
          refine ⟨2030841869647779573606955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10831156638121491059237093 2030841869647779573606955)
          ·
            refine ⟨3046262804471669360410433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030841869647779573606955 3046262804471669360410433)
            ·
              refine ⟨2284697103353752020307825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046262804471669360410433 2284697103353752020307825)
              ·
                refine ⟨1713522827515314015230869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284697103353752020307825 1713522827515314015230869)
                ·
                  refine ⟨80321382539780344463947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1713522827515314015230869 80321382539780344463947)
                  ·
                    rfl

theorem cell23_1407828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_1407828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407828 prefixEnd_1407828 := by exact prefixLift 1407828
  have htrace : WordTrace (prefixWord ++ tailWord_1407828) baseStart_1407828 baseEnd_1407828 := by
    simpa [prefixWord, tailWord_1407828, baseEnd_1407828] using wordTrace_append hprefix tailTrace_1407828
  have hstable : (prefixWord ++ tailWord_1407828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407828).length < 2 ^ (prefixWord ++ tailWord_1407828).sum := by decide
  have hdescent : baseEnd_1407828 < baseStart_1407828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407864 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_1407864 : Nat := 118140960795 + 1407864 * 2 ^ 59
def prefixEnd_1407864 : Nat := 4983230072969 + 3 ^ 40 * 1407864 * 2
def baseEnd_1407864 : Nat := 722910928161584959325357

theorem tailTrace_1407864 : CollatzResearch.WordTrace tailWord_1407864 prefixEnd_1407864 722910928161584959325357 := by
  unfold tailWord_1407864
  simp only [CollatzResearch.WordTrace]
  refine ⟨25674509285778323436791323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34232679047704431249055097 25674509285778323436791323)
  ·
    refine ⟨38511763928667485155186985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25674509285778323436791323 38511763928667485155186985)
    ·
      refine ⟨28883822946500613866390239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38511763928667485155186985 28883822946500613866390239)
      ·
        refine ⟨43325734419750920799585359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28883822946500613866390239 43325734419750920799585359)
        ·
          refine ⟨64988601629626381199378039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43325734419750920799585359 64988601629626381199378039)
          ·
            refine ⟨97482902444439571799067059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64988601629626381199378039 97482902444439571799067059)
            ·
              refine ⟨146224353666659357698600589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97482902444439571799067059 146224353666659357698600589)
              ·
                refine ⟨54834132624997259136975221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146224353666659357698600589 54834132624997259136975221)
                ·
                  refine ⟨5140699933593493044091427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54834132624997259136975221 5140699933593493044091427)
                  ·
                    refine ⟨7711049900390239566137141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5140699933593493044091427 7711049900390239566137141)
                    ·
                      refine ⟨722910928161584959325357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7711049900390239566137141 722910928161584959325357)
                      ·
                        rfl

theorem cell23_1407864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_1407864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407864 prefixEnd_1407864 := by exact prefixLift 1407864
  have htrace : WordTrace (prefixWord ++ tailWord_1407864) baseStart_1407864 baseEnd_1407864 := by
    simpa [prefixWord, tailWord_1407864, baseEnd_1407864] using wordTrace_append hprefix tailTrace_1407864
  have hstable : (prefixWord ++ tailWord_1407864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407864).length < 2 ^ (prefixWord ++ tailWord_1407864).sum := by decide
  have hdescent : baseEnd_1407864 < baseStart_1407864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407865 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 2, 3, 2]
def baseStart_1407865 : Nat := 118140960795 + 1407865 * 2 ^ 59
def prefixEnd_1407865 : Nat := 4983230072969 + 3 ^ 40 * 1407865 * 2
def baseEnd_1407865 : Nat := 722911441642239455412853

theorem tailTrace_1407865 : CollatzResearch.WordTrace tailWord_1407865 prefixEnd_1407865 722911441642239455412853 := by
  unfold tailWord_1407865
  simp only [CollatzResearch.WordTrace]
  refine ⟨51349055044553024044369049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34232703363035349362912699 51349055044553024044369049)
  ·
    refine ⟨38511791283414768033276787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51349055044553024044369049 38511791283414768033276787)
    ·
      refine ⟨57767686925122152049915181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38511791283414768033276787 57767686925122152049915181)
      ·
        refine ⟨21662882596920807018718193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57767686925122152049915181 21662882596920807018718193)
        ·
          refine ⟨16247161947690605264038645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21662882596920807018718193 16247161947690605264038645)
          ·
            refine ⟨1523171432595994243503623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16247161947690605264038645 1523171432595994243503623)
            ·
              refine ⟨2284757148893991365255435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523171432595994243503623 2284757148893991365255435)
              ·
                refine ⟨3427135723340987047883153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284757148893991365255435 3427135723340987047883153)
                ·
                  refine ⟨2570351792505740285912365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3427135723340987047883153 2570351792505740285912365)
                  ·
                    refine ⟨963881922189652607217137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2570351792505740285912365 963881922189652607217137)
                    ·
                      refine ⟨722911441642239455412853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963881922189652607217137 722911441642239455412853)
                      ·
                        rfl

theorem cell23_1407865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_1407865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407865 prefixEnd_1407865 := by exact prefixLift 1407865
  have htrace : WordTrace (prefixWord ++ tailWord_1407865) baseStart_1407865 baseEnd_1407865 := by
    simpa [prefixWord, tailWord_1407865, baseEnd_1407865] using wordTrace_append hprefix tailTrace_1407865
  have hstable : (prefixWord ++ tailWord_1407865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407865).length < 2 ^ (prefixWord ++ tailWord_1407865).sum := by decide
  have hdescent : baseEnd_1407865 < baseStart_1407865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407895 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 3, 2, 2]
def baseStart_1407895 : Nat := 118140960795 + 1407895 * 2 ^ 59
def prefixEnd_1407895 : Nat := 4983230072969 + 3 ^ 40 * 1407895 * 2
def baseEnd_1407895 : Nat := 722926846061874338037715

theorem tailTrace_1407895 : CollatzResearch.WordTrace tailWord_1407895 prefixEnd_1407895 722926846061874338037715 := by
  unfold tailWord_1407895
  simp only [CollatzResearch.WordTrace]
  refine ⟨51350149234444339167961139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34233432822962892778640759 51350149234444339167961139)
  ·
    refine ⟨77025223851666508751941709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51350149234444339167961139 77025223851666508751941709)
    ·
      refine ⟨28884458944374940781978141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77025223851666508751941709 28884458944374940781978141)
      ·
        refine ⟨10831672104140602793241803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28884458944374940781978141 10831672104140602793241803)
        ·
          refine ⟨16247508156210904189862705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10831672104140602793241803 16247508156210904189862705)
          ·
            refine ⟨12185631117158178142397029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16247508156210904189862705 12185631117158178142397029)
            ·
              refine ⟨2284805834467158401699443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12185631117158178142397029 2284805834467158401699443)
              ·
                refine ⟨3427208751700737602549165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284805834467158401699443 3427208751700737602549165)
                ·
                  refine ⟨1285203281887776600955937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3427208751700737602549165 1285203281887776600955937)
                  ·
                    refine ⟨963902461415832450716953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1285203281887776600955937 963902461415832450716953)
                    ·
                      refine ⟨722926846061874338037715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963902461415832450716953 722926846061874338037715)
                      ·
                        rfl

theorem cell23_1407895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_1407895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407895 prefixEnd_1407895 := by exact prefixLift 1407895
  have htrace : WordTrace (prefixWord ++ tailWord_1407895) baseStart_1407895 baseEnd_1407895 := by
    simpa [prefixWord, tailWord_1407895, baseEnd_1407895] using wordTrace_append hprefix tailTrace_1407895
  have hstable : (prefixWord ++ tailWord_1407895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407895).length < 2 ^ (prefixWord ++ tailWord_1407895).sum := by decide
  have hdescent : baseEnd_1407895 < baseStart_1407895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407898 : List Nat := [3, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1407898 : Nat := 118140960795 + 1407898 * 2 ^ 59
def prefixEnd_1407898 : Nat := 4983230072969 + 3 ^ 40 * 1407898 * 2
def baseEnd_1407898 : Nat := 722928386503837826300201

theorem tailTrace_1407898 : CollatzResearch.WordTrace tailWord_1407898 prefixEnd_1407898 722928386503837826300201 := by
  unfold tailWord_1407898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12837564663358367670080087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34233505768955647120213565 12837564663358367670080087)
  ·
    refine ⟨19256346995037551505120131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12837564663358367670080087 19256346995037551505120131)
    ·
      refine ⟨28884520492556327257680197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19256346995037551505120131 28884520492556327257680197)
      ·
        refine ⟨5415847592354311360815037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28884520492556327257680197 5415847592354311360815037)
        ·
          refine ⟨2030942847132866760305639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5415847592354311360815037 2030942847132866760305639)
          ·
            refine ⟨3046414270699300140458459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030942847132866760305639 3046414270699300140458459)
            ·
              refine ⟨4569621406048950210687689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046414270699300140458459 4569621406048950210687689)
              ·
                refine ⟨3427216054536712658015767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4569621406048950210687689 3427216054536712658015767)
                ·
                  refine ⟨5140824081805068987023651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427216054536712658015767 5140824081805068987023651)
                  ·
                    refine ⟨7711236122707603480535477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5140824081805068987023651 7711236122707603480535477)
                    ·
                      refine ⟨722928386503837826300201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7711236122707603480535477 722928386503837826300201)
                      ·
                        rfl

theorem cell23_1407898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1407898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407898 prefixEnd_1407898 := by exact prefixLift 1407898
  have htrace : WordTrace (prefixWord ++ tailWord_1407898) baseStart_1407898 baseEnd_1407898 := by
    simpa [prefixWord, tailWord_1407898, baseEnd_1407898] using wordTrace_append hprefix tailTrace_1407898
  have hstable : (prefixWord ++ tailWord_1407898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407898).length < 2 ^ (prefixWord ++ tailWord_1407898).sum := by decide
  have hdescent : baseEnd_1407898 < baseStart_1407898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407928 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 4, 1, 3]
def baseStart_1407928 : Nat := 118140960795 + 1407928 * 2 ^ 59
def prefixEnd_1407928 : Nat := 4983230072969 + 3 ^ 40 * 1407928 * 2
def baseEnd_1407928 : Nat := 722943790923472708925063

theorem tailTrace_1407928 : CollatzResearch.WordTrace tailWord_1407928 prefixEnd_1407928 722943790923472708925063 := by
  unfold tailWord_1407928
  simp only [CollatzResearch.WordTrace]
  refine ⟨25675676421662392901956219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34234235228883190535941625 25675676421662392901956219)
  ·
    refine ⟨38513514632493589352934329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25675676421662392901956219 38513514632493589352934329)
    ·
      refine ⟨28885135974370192014700747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38513514632493589352934329 28885135974370192014700747)
      ·
        refine ⟨43327703961555288022051121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28885135974370192014700747 43327703961555288022051121)
        ·
          refine ⟨32495777971166466016538341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43327703961555288022051121 32495777971166466016538341)
          ·
            refine ⟨6092958369593712378100939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32495777971166466016538341 6092958369593712378100939)
            ·
              refine ⟨9139437554390568567151409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6092958369593712378100939 9139437554390568567151409)
              ·
                refine ⟨6854578165792926425363557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9139437554390568567151409 6854578165792926425363557)
                ·
                  refine ⟨1285233406086173704755667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6854578165792926425363557 1285233406086173704755667)
                  ·
                    refine ⟨1927850109129260557133501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1285233406086173704755667 1927850109129260557133501)
                    ·
                      refine ⟨722943790923472708925063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1927850109129260557133501 722943790923472708925063)
                      ·
                        rfl

theorem cell23_1407928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_1407928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407928 prefixEnd_1407928 := by exact prefixLift 1407928
  have htrace : WordTrace (prefixWord ++ tailWord_1407928) baseStart_1407928 baseEnd_1407928 := by
    simpa [prefixWord, tailWord_1407928, baseEnd_1407928] using wordTrace_append hprefix tailTrace_1407928
  have hstable : (prefixWord ++ tailWord_1407928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407928).length < 2 ^ (prefixWord ++ tailWord_1407928).sum := by decide
  have hdescent : baseEnd_1407928 < baseStart_1407928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407929 : List Nat := [1, 2, 1, 4, 2, 4, 1, 3, 1, 2, 2]
def baseStart_1407929 : Nat := 118140960795 + 1407929 * 2 ^ 59
def prefixEnd_1407929 : Nat := 4983230072969 + 3 ^ 40 * 1407929 * 2
def baseEnd_1407929 : Nat := 722944304404127205012559

theorem tailTrace_1407929 : CollatzResearch.WordTrace tailWord_1407929 prefixEnd_1407929 722944304404127205012559 := by
  unfold tailWord_1407929
  simp only [CollatzResearch.WordTrace]
  refine ⟨51351389316321162974698841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34234259544214108649799227 51351389316321162974698841)
  ·
    refine ⟨38513541987240872231024131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51351389316321162974698841 38513541987240872231024131)
    ·
      refine ⟨57770312980861308346536197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38513541987240872231024131 57770312980861308346536197)
      ·
        refine ⟨10831933683911495314975537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57770312980861308346536197 10831933683911495314975537)
        ·
          refine ⟨8123950262933621486231653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10831933683911495314975537 8123950262933621486231653)
          ·
            refine ⟨1523240674300054028668435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8123950262933621486231653 1523240674300054028668435)
            ·
              refine ⟨2284861011450081043002653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523240674300054028668435 2284861011450081043002653)
              ·
                refine ⟨856822879293780391125995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2284861011450081043002653 856822879293780391125995)
                ·
                  refine ⟨1285234318940670586688993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 856822879293780391125995 1285234318940670586688993)
                  ·
                    refine ⟨963925739205502940016745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1285234318940670586688993 963925739205502940016745)
                    ·
                      refine ⟨722944304404127205012559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963925739205502940016745 722944304404127205012559)
                      ·
                        rfl

theorem cell23_1407929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_1407929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407929 prefixEnd_1407929 := by exact prefixLift 1407929
  have htrace : WordTrace (prefixWord ++ tailWord_1407929) baseStart_1407929 baseEnd_1407929 := by
    simpa [prefixWord, tailWord_1407929, baseEnd_1407929] using wordTrace_append hprefix tailTrace_1407929
  have hstable : (prefixWord ++ tailWord_1407929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407929).length < 2 ^ (prefixWord ++ tailWord_1407929).sum := by decide
  have hdescent : baseEnd_1407929 < baseStart_1407929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407962 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3]
def baseStart_1407962 : Nat := 118140960795 + 1407962 * 2 ^ 59
def prefixEnd_1407962 : Nat := 4983230072969 + 3 ^ 40 * 1407962 * 2
def baseEnd_1407962 : Nat := 722961249265725575899907

theorem tailTrace_1407962 : CollatzResearch.WordTrace tailWord_1407962 prefixEnd_1407962 722961249265725575899907 := by
  unfold tailWord_1407962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12838148231300402402662535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34235061950134406407100093 12838148231300402402662535)
  ·
    refine ⟨19257222346950603603993803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12838148231300402402662535 19257222346950603603993803)
    ·
      refine ⟨28885833520425905405990705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19257222346950603603993803 28885833520425905405990705)
      ·
        refine ⟨21664375140319429054493029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28885833520425905405990705 21664375140319429054493029)
        ·
          refine ⟨4062070338809892947717443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21664375140319429054493029 4062070338809892947717443)
          ·
            refine ⟨6093105508214839421576165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062070338809892947717443 6093105508214839421576165)
            ·
              refine ⟨1142457282790282391545531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6093105508214839421576165 1142457282790282391545531)
              ·
                refine ⟨1713685924185423587318297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142457282790282391545531 1713685924185423587318297)
                ·
                  refine ⟨1285264443139067690488723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1713685924185423587318297 1285264443139067690488723)
                  ·
                    refine ⟨1927896664708601535733085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1285264443139067690488723 1927896664708601535733085)
                    ·
                      refine ⟨722961249265725575899907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1927896664708601535733085 722961249265725575899907)
                      ·
                        rfl

theorem cell23_1407962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_1407962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407962 prefixEnd_1407962 := by exact prefixLift 1407962
  have htrace : WordTrace (prefixWord ++ tailWord_1407962) baseStart_1407962 baseEnd_1407962 := by
    simpa [prefixWord, tailWord_1407962, baseEnd_1407962] using wordTrace_append hprefix tailTrace_1407962
  have hstable : (prefixWord ++ tailWord_1407962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407962).length < 2 ^ (prefixWord ++ tailWord_1407962).sum := by decide
  have hdescent : baseEnd_1407962 < baseStart_1407962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407971 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 5]
def baseStart_1407971 : Nat := 118140960795 + 1407971 * 2 ^ 59
def prefixEnd_1407971 : Nat := 4983230072969 + 3 ^ 40 * 1407971 * 2
def baseEnd_1407971 : Nat := 722965870591616040687365

theorem tailTrace_1407971 : CollatzResearch.WordTrace tailWord_1407971 prefixEnd_1407971 722965870591616040687365 := by
  unfold tailWord_1407971
  simp only [CollatzResearch.WordTrace]
  refine ⟨51352921182169004147727767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34235280788112669431818511 51352921182169004147727767)
  ·
    refine ⟨77029381773253506221591651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51352921182169004147727767 77029381773253506221591651)
    ·
      refine ⟨115544072659880259332387477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77029381773253506221591651 115544072659880259332387477)
      ·
        refine ⟨5416128405931887156205663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115544072659880259332387477 5416128405931887156205663)
        ·
          refine ⟨8124192608897830734308495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5416128405931887156205663 8124192608897830734308495)
          ·
            refine ⟨12186288913346746101462743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8124192608897830734308495 12186288913346746101462743)
            ·
              refine ⟨18279433370020119152194115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12186288913346746101462743 18279433370020119152194115)
              ·
                refine ⟨27419150055030178728291173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18279433370020119152194115 27419150055030178728291173)
                ·
                  refine ⟨5141090635318158511554595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27419150055030178728291173 5141090635318158511554595)
                  ·
                    refine ⟨7711635952977237767331893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5141090635318158511554595 7711635952977237767331893)
                    ·
                      refine ⟨722965870591616040687365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7711635952977237767331893 722965870591616040687365)
                      ·
                        rfl

theorem cell23_1407971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_1407971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407971 prefixEnd_1407971 := by exact prefixLift 1407971
  have htrace : WordTrace (prefixWord ++ tailWord_1407971) baseStart_1407971 baseEnd_1407971 := by
    simpa [prefixWord, tailWord_1407971, baseEnd_1407971] using wordTrace_append hprefix tailTrace_1407971
  have hstable : (prefixWord ++ tailWord_1407971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407971).length < 2 ^ (prefixWord ++ tailWord_1407971).sum := by decide
  have hdescent : baseEnd_1407971 < baseStart_1407971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1407985 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 1, 4, 2]
def baseStart_1407985 : Nat := 118140960795 + 1407985 * 2 ^ 59
def prefixEnd_1407985 : Nat := 4983230072969 + 3 ^ 40 * 1407985 * 2
def baseEnd_1407985 : Nat := 722973059320778985912301

theorem tailTrace_1407985 : CollatzResearch.WordTrace tailWord_1407985 prefixEnd_1407985 722973059320778985912301 := by
  unfold tailWord_1407985
  simp only [CollatzResearch.WordTrace]
  refine ⟨51353431804118284538737409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34235621202745523025824939 51353431804118284538737409)
  ·
    refine ⟨38515073853088713404053057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51353431804118284538737409 38515073853088713404053057)
    ·
      refine ⟨28886305389816535053039793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38515073853088713404053057 28886305389816535053039793)
      ·
        refine ⟨21664729042362401289779845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28886305389816535053039793 21664729042362401289779845)
        ·
          refine ⟨4062136695442950241833721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21664729042362401289779845 4062136695442950241833721)
          ·
            refine ⟨3046602521582212681375291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4062136695442950241833721 3046602521582212681375291)
            ·
              refine ⟨4569903782373319022062937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046602521582212681375291 4569903782373319022062937)
              ·
                refine ⟨3427427836779989266547203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4569903782373319022062937 3427427836779989266547203)
                ·
                  refine ⟨5141141755169983899820805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427427836779989266547203 5141141755169983899820805)
                  ·
                    refine ⟨963964079094371981216401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141141755169983899820805 963964079094371981216401)
                    ·
                      refine ⟨722973059320778985912301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 963964079094371981216401 722973059320778985912301)
                      ·
                        rfl

theorem cell23_1407985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_1407985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1407985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1407985 prefixEnd_1407985 := by exact prefixLift 1407985
  have htrace : WordTrace (prefixWord ++ tailWord_1407985) baseStart_1407985 baseEnd_1407985 := by
    simpa [prefixWord, tailWord_1407985, baseEnd_1407985] using wordTrace_append hprefix tailTrace_1407985
  have hstable : (prefixWord ++ tailWord_1407985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1407985).length < 2 ^ (prefixWord ++ tailWord_1407985).sum := by decide
  have hdescent : baseEnd_1407985 < baseStart_1407985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1407985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408042 : List Nat := [3, 1, 4, 1, 3, 1, 2, 3, 5]
def baseStart_1408042 : Nat := 118140960795 + 1408042 * 2 ^ 59
def prefixEnd_1408042 : Nat := 4983230072969 + 3 ^ 40 * 1408042 * 2
def baseEnd_1408042 : Nat := 80333591968676140322171

theorem tailTrace_1408042 : CollatzResearch.WordTrace tailWord_1408042 prefixEnd_1408042 80333591968676140322171 := by
  unfold tailWord_1408042
  simp only [CollatzResearch.WordTrace]
  refine ⟨12838877691227945818390595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34237007176607855515708253 12838877691227945818390595)
  ·
    refine ⟨19258316536841918727585893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12838877691227945818390595 19258316536841918727585893)
    ·
      refine ⟨3610934350657859761422355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19258316536841918727585893 3610934350657859761422355)
      ·
        refine ⟨5416401525986789642133533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3610934350657859761422355 5416401525986789642133533)
        ·
          refine ⟨2031150572245046115800075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5416401525986789642133533 2031150572245046115800075)
          ·
            refine ⟨3046725858367569173700113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031150572245046115800075 3046725858367569173700113)
            ·
              refine ⟨2285044393775676880275085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046725858367569173700113 2285044393775676880275085)
              ·
                refine ⟨856891647665878830103157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2285044393775676880275085 856891647665878830103157)
                ·
                  refine ⟨80333591968676140322171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 856891647665878830103157 80333591968676140322171)
                  ·
                    rfl

theorem cell23_1408042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 5].length) (baseStart_1408042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408042 prefixEnd_1408042 := by exact prefixLift 1408042
  have htrace : WordTrace (prefixWord ++ tailWord_1408042) baseStart_1408042 baseEnd_1408042 := by
    simpa [prefixWord, tailWord_1408042, baseEnd_1408042] using wordTrace_append hprefix tailTrace_1408042
  have hstable : (prefixWord ++ tailWord_1408042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408042).length < 2 ^ (prefixWord ++ tailWord_1408042).sum := by decide
  have hdescent : baseEnd_1408042 < baseStart_1408042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408058 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_1408058 : Nat := 118140960795 + 1408058 * 2 ^ 59
def prefixEnd_1408058 : Nat := 4983230072969 + 3 ^ 40 * 1408058 * 2
def baseEnd_1408058 : Nat := 723010543408557200299465

theorem tailTrace_1408058 : CollatzResearch.WordTrace tailWord_1408058 prefixEnd_1408058 723010543408557200299465 := by
  unfold tailWord_1408058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12839023583213454501536207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34237396221902545337429885 12839023583213454501536207)
  ·
    refine ⟨19258535374820181752304311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12839023583213454501536207 19258535374820181752304311)
    ·
      refine ⟨28887803062230272628456467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19258535374820181752304311 28887803062230272628456467)
      ·
        refine ⟨43331704593345408942684701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28887803062230272628456467 43331704593345408942684701)
        ·
          refine ⟨16249389222504528353506763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43331704593345408942684701 16249389222504528353506763)
          ·
            refine ⟨24374083833756792530260145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16249389222504528353506763 24374083833756792530260145)
            ·
              refine ⟨18280562875317594397695109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24374083833756792530260145 18280562875317594397695109)
              ·
                refine ⟨3427605539122048949567833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18280562875317594397695109 3427605539122048949567833)
                ·
                  refine ⟨2570704154341536712175875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3427605539122048949567833 2570704154341536712175875)
                  ·
                    refine ⟨3856056231512305068263813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2570704154341536712175875 3856056231512305068263813)
                    ·
                      refine ⟨723010543408557200299465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3856056231512305068263813 723010543408557200299465)
                      ·
                        rfl

theorem cell23_1408058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_1408058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408058 prefixEnd_1408058 := by exact prefixLift 1408058
  have htrace : WordTrace (prefixWord ++ tailWord_1408058) baseStart_1408058 baseEnd_1408058 := by
    simpa [prefixWord, tailWord_1408058, baseEnd_1408058] using wordTrace_append hprefix tailTrace_1408058
  have hstable : (prefixWord ++ tailWord_1408058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408058).length < 2 ^ (prefixWord ++ tailWord_1408058).sum := by decide
  have hdescent : baseEnd_1408058 < baseStart_1408058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408078 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_1408078 : Nat := 118140960795 + 1408078 * 2 ^ 59
def prefixEnd_1408078 : Nat := 4983230072969 + 3 ^ 40 * 1408078 * 2
def baseEnd_1408078 : Nat := 723020813021647122049373

theorem tailTrace_1408078 : CollatzResearch.WordTrace tailWord_1408078 prefixEnd_1408078 723020813021647122049373 := by
  unfold tailWord_1408078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419602974097670177734111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34237882528520907614581925 6419602974097670177734111)
  ·
    refine ⟨9629404461146505266601167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6419602974097670177734111 9629404461146505266601167)
    ·
      refine ⟨14444106691719757899901751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9629404461146505266601167 14444106691719757899901751)
      ·
        refine ⟨21666160037579636849852627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14444106691719757899901751 21666160037579636849852627)
        ·
          refine ⟨32499240056369455274778941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21666160037579636849852627 32499240056369455274778941)
          ·
            refine ⟨12187215021138545728042103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32499240056369455274778941 12187215021138545728042103)
            ·
              refine ⟨18280822531707818592063155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12187215021138545728042103 18280822531707818592063155)
              ·
                refine ⟨27421233797561727888094733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18280822531707818592063155 27421233797561727888094733)
                ·
                  refine ⟨10282962674085647958035525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27421233797561727888094733 10282962674085647958035525)
                  ·
                    refine ⟨1928055501391058992131661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10282962674085647958035525 1928055501391058992131661)
                    ·
                      refine ⟨723020813021647122049373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1928055501391058992131661 723020813021647122049373)
                      ·
                        rfl

theorem cell23_1408078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_1408078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408078 prefixEnd_1408078 := by exact prefixLift 1408078
  have htrace : WordTrace (prefixWord ++ tailWord_1408078) baseStart_1408078 baseEnd_1408078 := by
    simpa [prefixWord, tailWord_1408078, baseEnd_1408078] using wordTrace_append hprefix tailTrace_1408078
  have hstable : (prefixWord ++ tailWord_1408078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408078).length < 2 ^ (prefixWord ++ tailWord_1408078).sum := by decide
  have hdescent : baseEnd_1408078 < baseStart_1408078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408132 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 6]
def baseStart_1408132 : Nat := 118140960795 + 1408132 * 2 ^ 59
def prefixEnd_1408132 : Nat := 4983230072969 + 3 ^ 40 * 1408132 * 2
def baseEnd_1408132 : Nat := 80338726775221101197125

theorem tailTrace_1408132 : CollatzResearch.WordTrace tailWord_1408132 prefixEnd_1408132 80338726775221101197125 := by
  unfold tailWord_1408132
  simp only [CollatzResearch.WordTrace]
  refine ⟨25679396667292864322169325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34239195556390485762892433 25679396667292864322169325)
  ·
    refine ⟨9629773750234824120813497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25679396667292864322169325 9629773750234824120813497)
    ·
      refine ⟨7222330312676118090610123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9629773750234824120813497 7222330312676118090610123)
      ·
        refine ⟨10833495469014177135915185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7222330312676118090610123 10833495469014177135915185)
        ·
          refine ⟨8125121601760632851936389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10833495469014177135915185 8125121601760632851936389)
          ·
            refine ⟨1523460300330118659738073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8125121601760632851936389 1523460300330118659738073)
            ·
              refine ⟨1142595225247588994803555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523460300330118659738073 1142595225247588994803555)
              ·
                refine ⟨1713892837871383492205333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142595225247588994803555 1713892837871383492205333)
                ·
                  refine ⟨80338726775221101197125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1713892837871383492205333 80338726775221101197125)
                  ·
                    rfl

theorem cell23_1408132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_1408132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408132 prefixEnd_1408132 := by exact prefixLift 1408132
  have htrace : WordTrace (prefixWord ++ tailWord_1408132) baseStart_1408132 baseEnd_1408132 := by
    simpa [prefixWord, tailWord_1408132, baseEnd_1408132] using wordTrace_append hprefix tailTrace_1408132
  have hstable : (prefixWord ++ tailWord_1408132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408132).length < 2 ^ (prefixWord ++ tailWord_1408132).sum := by decide
  have hdescent : baseEnd_1408132 < baseStart_1408132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408135 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_1408135 : Nat := 118140960795 + 1408135 * 2 ^ 59
def prefixEnd_1408135 : Nat := 4983230072969 + 3 ^ 40 * 1408135 * 2
def baseEnd_1408135 : Nat := 723050081418953399036611

theorem tailTrace_1408135 : CollatzResearch.WordTrace tailWord_1408135 prefixEnd_1408135 723050081418953399036611 := by
  unfold tailWord_1408135
  simp only [CollatzResearch.WordTrace]
  refine ⟨51358902753574860156697859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34239268502383240104465239 51358902753574860156697859)
  ·
    refine ⟨77038354130362290235046789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51358902753574860156697859 77038354130362290235046789)
    ·
      refine ⟨14444691399442929419071273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77038354130362290235046789 14444691399442929419071273)
      ·
        refine ⟨10833518549582197064303455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14444691399442929419071273 10833518549582197064303455)
        ·
          refine ⟨16250277824373295596455183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10833518549582197064303455 16250277824373295596455183)
          ·
            refine ⟨24375416736559943394682775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16250277824373295596455183 24375416736559943394682775)
            ·
              refine ⟨36563125104839915092024163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24375416736559943394682775 36563125104839915092024163)
              ·
                refine ⟨54844687657259872638036245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36563125104839915092024163 54844687657259872638036245)
                ·
                  refine ⟨2570844733934056529907949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54844687657259872638036245 2570844733934056529907949)
                  ·
                    refine ⟨964066775225271198715481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2570844733934056529907949 964066775225271198715481)
                    ·
                      refine ⟨723050081418953399036611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964066775225271198715481 723050081418953399036611)
                      ·
                        rfl

theorem cell23_1408135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_1408135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408135 prefixEnd_1408135 := by exact prefixLift 1408135
  have htrace : WordTrace (prefixWord ++ tailWord_1408135) baseStart_1408135 baseEnd_1408135 := by
    simpa [prefixWord, tailWord_1408135, baseEnd_1408135] using wordTrace_append hprefix tailTrace_1408135
  have hstable : (prefixWord ++ tailWord_1408135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408135).length < 2 ^ (prefixWord ++ tailWord_1408135).sum := by decide
  have hdescent : baseEnd_1408135 < baseStart_1408135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408152 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 2, 3, 2]
def baseStart_1408152 : Nat := 118140960795 + 1408152 * 2 ^ 59
def prefixEnd_1408152 : Nat := 4983230072969 + 3 ^ 40 * 1408152 * 2
def baseEnd_1408152 : Nat := 723058810590079832524033

theorem tailTrace_1408152 : CollatzResearch.WordTrace tailWord_1408152 prefixEnd_1408152 723058810590079832524033 := by
  unfold tailWord_1408152
  simp only [CollatzResearch.WordTrace]
  refine ⟨25679761397256636030033355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34239681863008848040044473 25679761397256636030033355)
  ·
    refine ⟨38519642095884954045050033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25679761397256636030033355 38519642095884954045050033)
    ·
      refine ⟨28889731571913715533787525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38519642095884954045050033 28889731571913715533787525)
      ·
        refine ⟨5416824669733821662585161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28889731571913715533787525 5416824669733821662585161)
        ·
          refine ⟨4062618502300366246938871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5416824669733821662585161 4062618502300366246938871)
          ·
            refine ⟨6093927753450549370408307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062618502300366246938871 6093927753450549370408307)
            ·
              refine ⟨9140891630175824055612461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093927753450549370408307 9140891630175824055612461)
              ·
                refine ⟨3427834361315934020854673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9140891630175824055612461 3427834361315934020854673)
                ·
                  refine ⟨2570875770986950515641005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3427834361315934020854673 2570875770986950515641005)
                  ·
                    refine ⟨964078414120106443365377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2570875770986950515641005 964078414120106443365377)
                    ·
                      refine ⟨723058810590079832524033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 964078414120106443365377 723058810590079832524033)
                      ·
                        rfl

theorem cell23_1408152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_1408152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408152 prefixEnd_1408152 := by exact prefixLift 1408152
  have htrace : WordTrace (prefixWord ++ tailWord_1408152) baseStart_1408152 baseEnd_1408152 := by
    simpa [prefixWord, tailWord_1408152, baseEnd_1408152] using wordTrace_append hprefix tailTrace_1408152
  have hstable : (prefixWord ++ tailWord_1408152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408152).length < 2 ^ (prefixWord ++ tailWord_1408152).sum := by decide
  have hdescent : baseEnd_1408152 < baseStart_1408152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408175 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 2, 4]
def baseStart_1408175 : Nat := 118140960795 + 1408175 * 2 ^ 59
def prefixEnd_1408175 : Nat := 4983230072969 + 3 ^ 40 * 1408175 * 2
def baseEnd_1408175 : Nat := 241023540215044414178809

theorem tailTrace_1408175 : CollatzResearch.WordTrace tailWord_1408175 prefixEnd_1408175 241023540215044414178809 := by
  unfold tailWord_1408175
  simp only [CollatzResearch.WordTrace]
  refine ⟨51360361673429946988153979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34240241115619964658769319 51360361673429946988153979)
  ·
    refine ⟨77040542510144920482230969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51360361673429946988153979 77040542510144920482230969)
    ·
      refine ⟨57780406882608690361673227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77040542510144920482230969 57780406882608690361673227)
      ·
        refine ⟨86670610323913035542509841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57780406882608690361673227 86670610323913035542509841)
        ·
          refine ⟨65002957742934776656882381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86670610323913035542509841 65002957742934776656882381)
          ·
            refine ⟨24376109153600541246330893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65002957742934776656882381 24376109153600541246330893)
            ·
              refine ⟨9141040932600202967374085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24376109153600541246330893 9141040932600202967374085)
              ·
                refine ⟨1713945174862538056382641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9141040932600202967374085 1713945174862538056382641)
                ·
                  refine ⟨1285458881146903542286981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1713945174862538056382641 1285458881146903542286981)
                  ·
                    refine ⟨241023540215044414178809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1285458881146903542286981 241023540215044414178809)
                    ·
                      rfl

theorem cell23_1408175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 4].length) (baseStart_1408175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408175 prefixEnd_1408175 := by exact prefixLift 1408175
  have htrace : WordTrace (prefixWord ++ tailWord_1408175) baseStart_1408175 baseEnd_1408175 := by
    simpa [prefixWord, tailWord_1408175, baseEnd_1408175] using wordTrace_append hprefix tailTrace_1408175
  have hstable : (prefixWord ++ tailWord_1408175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408175).length < 2 ^ (prefixWord ++ tailWord_1408175).sum := by decide
  have hdescent : baseEnd_1408175 < baseStart_1408175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408185 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1408185 : Nat := 118140960795 + 1408185 * 2 ^ 59
def prefixEnd_1408185 : Nat := 4983230072969 + 3 ^ 40 * 1408185 * 2
def baseEnd_1408185 : Nat := 723075755451678203411381

theorem tailTrace_1408185 : CollatzResearch.WordTrace tailWord_1408185 prefixEnd_1408185 723075755451678203411381 := by
  unfold tailWord_1408185
  simp only [CollatzResearch.WordTrace]
  refine ⟨51360726403393718696018009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34240484268929145797345339 51360726403393718696018009)
  ·
    refine ⟨38520544802545289022013507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51360726403393718696018009 38520544802545289022013507)
    ·
      refine ⟨57780817203817933533020261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38520544802545289022013507 57780817203817933533020261)
      ·
        refine ⟨10833903225715862537441299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57780817203817933533020261 10833903225715862537441299)
        ·
          refine ⟨16250854838573793806161949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10833903225715862537441299 16250854838573793806161949)
          ·
            refine ⟨6094070564465172677310731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16250854838573793806161949 6094070564465172677310731)
            ·
              refine ⟨9141105846697759015966097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6094070564465172677310731 9141105846697759015966097)
              ·
                refine ⟨6855829385023319261974573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9141105846697759015966097 6855829385023319261974573)
                ·
                  refine ⟨2570936019383744723240465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6855829385023319261974573 2570936019383744723240465)
                  ·
                    refine ⟨1928202014537808542430349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2570936019383744723240465 1928202014537808542430349)
                    ·
                      refine ⟨723075755451678203411381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1928202014537808542430349 723075755451678203411381)
                      ·
                        rfl

theorem cell23_1408185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1408185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408185 prefixEnd_1408185 := by exact prefixLift 1408185
  have htrace : WordTrace (prefixWord ++ tailWord_1408185) baseStart_1408185 baseEnd_1408185 := by
    simpa [prefixWord, tailWord_1408185, baseEnd_1408185] using wordTrace_append hprefix tailTrace_1408185
  have hstable : (prefixWord ++ tailWord_1408185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408185).length < 2 ^ (prefixWord ++ tailWord_1408185).sum := by decide
  have hdescent : baseEnd_1408185 < baseStart_1408185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408215 : List Nat := [1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_1408215 : Nat := 118140960795 + 1408215 * 2 ^ 59
def prefixEnd_1408215 : Nat := 4983230072969 + 3 ^ 40 * 1408215 * 2
def baseEnd_1408215 : Nat := 723091159871313086036243

theorem tailTrace_1408215 : CollatzResearch.WordTrace tailWord_1408215 prefixEnd_1408215 723091159871313086036243 := by
  unfold tailWord_1408215
  simp only [CollatzResearch.WordTrace]
  refine ⟨51361820593285033819610099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34241213728856689213073399 51361820593285033819610099)
  ·
    refine ⟨77042730889927550729415149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51361820593285033819610099 77042730889927550729415149)
    ·
      refine ⟨28891024083722831523530681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77042730889927550729415149 28891024083722831523530681)
      ·
        refine ⟨21668268062792123642648011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28891024083722831523530681 21668268062792123642648011)
        ·
          refine ⟨32502402094188185463972017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21668268062792123642648011 32502402094188185463972017)
          ·
            refine ⟨24376801570641139097979013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32502402094188185463972017 24376801570641139097979013)
            ·
              refine ⟨4570650294495213580871065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24376801570641139097979013 4570650294495213580871065)
              ·
                refine ⟨3427987720871410185653299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570650294495213580871065 3427987720871410185653299)
                ·
                  refine ⟨5141981581307115278479949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427987720871410185653299 5141981581307115278479949)
                  ·
                    refine ⟨1928243092990168229429981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5141981581307115278479949 1928243092990168229429981)
                    ·
                      refine ⟨723091159871313086036243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1928243092990168229429981 723091159871313086036243)
                      ·
                        rfl

theorem cell23_1408215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_1408215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408215 prefixEnd_1408215 := by exact prefixLift 1408215
  have htrace : WordTrace (prefixWord ++ tailWord_1408215) baseStart_1408215 baseEnd_1408215 := by
    simpa [prefixWord, tailWord_1408215, baseEnd_1408215] using wordTrace_append hprefix tailTrace_1408215
  have hstable : (prefixWord ++ tailWord_1408215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408215).length < 2 ^ (prefixWord ++ tailWord_1408215).sum := by decide
  have hdescent : baseEnd_1408215 < baseStart_1408215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1408216 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 1, 1, 4]
def baseStart_1408216 : Nat := 118140960795 + 1408216 * 2 ^ 59
def prefixEnd_1408216 : Nat := 4983230072969 + 3 ^ 40 * 1408216 * 2
def baseEnd_1408216 : Nat := 723091673351967582123739

theorem tailTrace_1408216 : CollatzResearch.WordTrace tailWord_1408216 prefixEnd_1408216 723091673351967582123739 := by
  unfold tailWord_1408216
  simp only [CollatzResearch.WordTrace]
  refine ⟨25680928533140705495198251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34241238044187607326931001 25680928533140705495198251)
  ·
    refine ⟨38521392799711058242797377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25680928533140705495198251 38521392799711058242797377)
    ·
      refine ⟨28891044599783293682098033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38521392799711058242797377 28891044599783293682098033)
      ·
        refine ⟨21668283449837470261573525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28891044599783293682098033 21668283449837470261573525)
        ·
          refine ⟨1015700786711131418511259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21668283449837470261573525 1015700786711131418511259)
          ·
            refine ⟨1523551180066697127766889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015700786711131418511259 1523551180066697127766889)
            ·
              refine ⟨1142663385050022845825167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1523551180066697127766889 1142663385050022845825167)
              ·
                refine ⟨1713995077575034268737751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142663385050022845825167 1713995077575034268737751)
                ·
                  refine ⟨2570992616362551403106627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713995077575034268737751 2570992616362551403106627)
                  ·
                    refine ⟨3856488924543827104659941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2570992616362551403106627 3856488924543827104659941)
                    ·
                      refine ⟨723091673351967582123739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3856488924543827104659941 723091673351967582123739)
                      ·
                        rfl

theorem cell23_1408216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_1408216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1408216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1408216 prefixEnd_1408216 := by exact prefixLift 1408216
  have htrace : WordTrace (prefixWord ++ tailWord_1408216) baseStart_1408216 baseEnd_1408216 := by
    simpa [prefixWord, tailWord_1408216, baseEnd_1408216] using wordTrace_append hprefix tailTrace_1408216
  have hstable : (prefixWord ++ tailWord_1408216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1408216).length < 2 ^ (prefixWord ++ tailWord_1408216).sum := by decide
  have hdescent : baseEnd_1408216 < baseStart_1408216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1408216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
