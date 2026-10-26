import V185TrunkScan19Chunk045

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_461468 : List Nat := [2, 2, 3, 2, 2, 2, 3, 3]
def baseStart_461468 : Nat := 118140960795 + 461468 * 2 ^ 59
def prefixEnd_461468 : Nat := 4983230072969 + 3 ^ 40 * 461468 * 2
def baseEnd_461468 : Nat := 140417712989099696609039

theorem tailTrace_461468 : CollatzResearch.WordTrace tailWord_461468 prefixEnd_461468 140417712989099696609039 := by
  unfold tailWord_461468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8415560346093861652464529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11220747128125148869952705 8415560346093861652464529)
  ·
    refine ⟨6311670259570396239348397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8415560346093861652464529 6311670259570396239348397)
    ·
      refine ⟨2366876347338898589755649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6311670259570396239348397 2366876347338898589755649)
      ·
        refine ⟨1775157260504173942316737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2366876347338898589755649 1775157260504173942316737)
        ·
          refine ⟨1331367945378130456737553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1775157260504173942316737 1331367945378130456737553)
          ·
            refine ⟨998525959033597842553165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1331367945378130456737553 998525959033597842553165)
            ·
              refine ⟨374447234637599190957437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998525959033597842553165 374447234637599190957437)
              ·
                refine ⟨140417712989099696609039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374447234637599190957437 140417712989099696609039)
                ·
                  rfl

theorem cell19_461468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_461468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461468 prefixEnd_461468 := by exact prefixLift 461468
  have htrace : WordTrace (prefixWord ++ tailWord_461468) baseStart_461468 baseEnd_461468 := by
    simpa [prefixWord, tailWord_461468, baseEnd_461468] using wordTrace_append hprefix tailTrace_461468
  have hstable : (prefixWord ++ tailWord_461468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461468).length < 2 ^ (prefixWord ++ tailWord_461468).sum := by decide
  have hdescent : baseEnd_461468 < baseStart_461468 := by decide
  rcases family_descends (prefixWord ++ tailWord_461468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461491 : List Nat := [1, 1, 1, 2, 3, 5, 6]
def baseStart_461491 : Nat := 118140960795 + 461491 * 2 ^ 59
def prefixEnd_461491 : Nat := 4983230072969 + 3 ^ 40 * 461491 * 2
def baseEnd_461491 : Nat := 46808237180080819365955

theorem tailTrace_461491 : CollatzResearch.WordTrace tailWord_461491 prefixEnd_461491 46808237180080819365955 := by
  unfold tailWord_461491
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831959571104398233016327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11221306380736265488677551 16831959571104398233016327)
  ·
    refine ⟨25247939356656597349524491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16831959571104398233016327 25247939356656597349524491)
    ·
      refine ⟨37871909034984896024286737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25247939356656597349524491 37871909034984896024286737)
      ·
        refine ⟨28403931776238672018215053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37871909034984896024286737 28403931776238672018215053)
        ·
          refine ⟨10651474416089502006830645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28403931776238672018215053 10651474416089502006830645)
          ·
            refine ⟨998575726508390813140373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10651474416089502006830645 998575726508390813140373)
            ·
              refine ⟨46808237180080819365955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 998575726508390813140373 46808237180080819365955)
              ·
                rfl

theorem cell19_461491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_461491 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461491 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461491 prefixEnd_461491 := by exact prefixLift 461491
  have htrace : WordTrace (prefixWord ++ tailWord_461491) baseStart_461491 baseEnd_461491 := by
    simpa [prefixWord, tailWord_461491, baseEnd_461491] using wordTrace_append hprefix tailTrace_461491
  have hstable : (prefixWord ++ tailWord_461491).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461491).length < 2 ^ (prefixWord ++ tailWord_461491).sum := by decide
  have hdescent : baseEnd_461491 < baseStart_461491 := by decide
  rcases family_descends (prefixWord ++ tailWord_461491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461525 : List Nat := [1, 3, 2, 5, 1, 1, 1, 5]
def baseStart_461525 : Nat := 118140960795 + 461525 * 2 ^ 59
def prefixEnd_461525 : Nat := 4983230072969 + 3 ^ 40 * 461525 * 2
def baseEnd_461525 : Nat := 140435057224540453342217

theorem tailTrace_461525 : CollatzResearch.WordTrace tailWord_461525 prefixEnd_461525 140435057224540453342217 := by
  unfold tailWord_461525
  simp only [CollatzResearch.WordTrace]
  refine ⟨16833199652981222039754029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11222133101987481359836019 16833199652981222039754029)
  ·
    refine ⟨6312449869867958264907761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16833199652981222039754029 6312449869867958264907761)
    ·
      refine ⟨4734337402400968698680821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6312449869867958264907761 4734337402400968698680821)
      ·
        refine ⟨443844131475090815501327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4734337402400968698680821 443844131475090815501327)
        ·
          refine ⟨665766197212636223251991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443844131475090815501327 665766197212636223251991)
          ·
            refine ⟨998649295818954334877987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665766197212636223251991 998649295818954334877987)
            ·
              refine ⟨1497973943728431502316981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 998649295818954334877987 1497973943728431502316981)
              ·
                refine ⟨140435057224540453342217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1497973943728431502316981 140435057224540453342217)
                ·
                  rfl

theorem cell19_461525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_461525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461525 prefixEnd_461525 := by exact prefixLift 461525
  have htrace : WordTrace (prefixWord ++ tailWord_461525) baseStart_461525 baseEnd_461525 := by
    simpa [prefixWord, tailWord_461525, baseEnd_461525] using wordTrace_append hprefix tailTrace_461525
  have hstable : (prefixWord ++ tailWord_461525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461525).length < 2 ^ (prefixWord ++ tailWord_461525).sum := by decide
  have hdescent : baseEnd_461525 < baseStart_461525 := by decide
  rcases family_descends (prefixWord ++ tailWord_461525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461527 : List Nat := [1, 1, 3, 2, 1, 4, 4, 3]
def baseStart_461527 : Nat := 118140960795 + 461527 * 2 ^ 59
def prefixEnd_461527 : Nat := 4983230072969 + 3 ^ 40 * 461527 * 2
def baseEnd_461527 : Nat := 140435665794205041297767

theorem tailTrace_461527 : CollatzResearch.WordTrace tailWord_461527 prefixEnd_461527 140435665794205041297767 := by
  unfold tailWord_461527
  simp only [CollatzResearch.WordTrace]
  refine ⟨16833272598973976381326835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11222181732649317587551223 16833272598973976381326835)
  ·
    refine ⟨25249908898460964571990253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16833272598973976381326835 25249908898460964571990253)
    ·
      refine ⟨9468715836922861714496345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25249908898460964571990253 9468715836922861714496345)
      ·
        refine ⟨7101536877692146285872259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9468715836922861714496345 7101536877692146285872259)
        ·
          refine ⟨10652305316538219428808389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7101536877692146285872259 10652305316538219428808389)
          ·
            refine ⟨1997307246850916142901573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10652305316538219428808389 1997307246850916142901573)
            ·
              refine ⟨374495108784546776794045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1997307246850916142901573 374495108784546776794045)
              ·
                refine ⟨140435665794205041297767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374495108784546776794045 140435665794205041297767)
                ·
                  rfl

theorem cell19_461527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_461527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461527 prefixEnd_461527 := by exact prefixLift 461527
  have htrace : WordTrace (prefixWord ++ tailWord_461527) baseStart_461527 baseEnd_461527 := by
    simpa [prefixWord, tailWord_461527, baseEnd_461527] using wordTrace_append hprefix tailTrace_461527
  have hstable : (prefixWord ++ tailWord_461527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461527).length < 2 ^ (prefixWord ++ tailWord_461527).sum := by decide
  have hdescent : baseEnd_461527 < baseStart_461527 := by decide
  rcases family_descends (prefixWord ++ tailWord_461527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461529 : List Nat := [1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_461529 : Nat := 118140960795 + 461529 * 2 ^ 59
def prefixEnd_461529 : Nat := 4983230072969 + 3 ^ 40 * 461529 * 2
def baseEnd_461529 : Nat := 140436274363869629253317

theorem tailTrace_461529 : CollatzResearch.WordTrace tailWord_461529 prefixEnd_461529 140436274363869629253317 := by
  unfold tailWord_461529
  simp only [CollatzResearch.WordTrace]
  refine ⟨16833345544966730722899641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11222230363311153815266427 16833345544966730722899641)
  ·
    refine ⟨12625009158725048042174731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16833345544966730722899641 12625009158725048042174731)
    ·
      refine ⟨18937513738087572063262097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12625009158725048042174731 18937513738087572063262097)
      ·
        refine ⟨14203135303565679047446573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18937513738087572063262097 14203135303565679047446573)
        ·
          refine ⟨5326175738837129642792465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14203135303565679047446573 5326175738837129642792465)
          ·
            refine ⟨3994631804127847232094349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5326175738837129642792465 3994631804127847232094349)
            ·
              refine ⟨1497986926547942712035381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3994631804127847232094349 1497986926547942712035381)
              ·
                refine ⟨140436274363869629253317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1497986926547942712035381 140436274363869629253317)
                ·
                  rfl

theorem cell19_461529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_461529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461529 prefixEnd_461529 := by exact prefixLift 461529
  have htrace : WordTrace (prefixWord ++ tailWord_461529) baseStart_461529 baseEnd_461529 := by
    simpa [prefixWord, tailWord_461529, baseEnd_461529] using wordTrace_append hprefix tailTrace_461529
  have hstable : (prefixWord ++ tailWord_461529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461529).length < 2 ^ (prefixWord ++ tailWord_461529).sum := by decide
  have hdescent : baseEnd_461529 < baseStart_461529 := by decide
  rcases family_descends (prefixWord ++ tailWord_461529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461544 : List Nat := [2, 1, 4, 1, 5, 1, 5]
def baseStart_461544 : Nat := 118140960795 + 461544 * 2 ^ 59
def prefixEnd_461544 : Nat := 4983230072969 + 3 ^ 40 * 461544 * 2
def baseEnd_461544 : Nat := 46813612878784679639981

theorem tailTrace_461544 : CollatzResearch.WordTrace tailWord_461544 prefixEnd_461544 46813612878784679639981 := by
  unfold tailWord_461544
  simp only [CollatzResearch.WordTrace]
  refine ⟨8416946319956194142347843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11222595093274925523130457 8416946319956194142347843)
  ·
    refine ⟨12625419479934291213521765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8416946319956194142347843 12625419479934291213521765)
    ·
      refine ⟨2367266152487679602535331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12625419479934291213521765 2367266152487679602535331)
      ·
        refine ⟨3550899228731519403802997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2367266152487679602535331 3550899228731519403802997)
        ·
          refine ⟨332896802693579944106531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3550899228731519403802997 332896802693579944106531)
          ·
            refine ⟨499345204040369916159797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332896802693579944106531 499345204040369916159797)
            ·
              refine ⟨46813612878784679639981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 499345204040369916159797 46813612878784679639981)
              ·
                rfl

theorem cell19_461544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 5].length) (baseStart_461544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461544 prefixEnd_461544 := by exact prefixLift 461544
  have htrace : WordTrace (prefixWord ++ tailWord_461544) baseStart_461544 baseEnd_461544 := by
    simpa [prefixWord, tailWord_461544, baseEnd_461544] using wordTrace_append hprefix tailTrace_461544
  have hstable : (prefixWord ++ tailWord_461544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461544).length < 2 ^ (prefixWord ++ tailWord_461544).sum := by decide
  have hdescent : baseEnd_461544 < baseStart_461544 := by decide
  rcases family_descends (prefixWord ++ tailWord_461544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461641 : List Nat := [1, 2, 1, 1, 2, 6, 3, 3]
def baseStart_461641 : Nat := 118140960795 + 461641 * 2 ^ 59
def prefixEnd_461641 : Nat := 4983230072969 + 3 ^ 40 * 461641 * 2
def baseEnd_461641 : Nat := 140470354265086554764123

theorem tailTrace_461641 : CollatzResearch.WordTrace tailWord_461641 prefixEnd_461641 140470354265086554764123 := by
  unfold tailWord_461641
  simp only [CollatzResearch.WordTrace]
  refine ⟨16837430520560973850976777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11224953680373982567317851 16837430520560973850976777)
  ·
    refine ⟨12628072890420730388232583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16837430520560973850976777 12628072890420730388232583)
    ·
      refine ⟨18942109335631095582348875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12628072890420730388232583 18942109335631095582348875)
      ·
        refine ⟨28413164003446643373523313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18942109335631095582348875 28413164003446643373523313)
        ·
          refine ⟨21309873002584982530142485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28413164003446643373523313 21309873002584982530142485)
          ·
            refine ⟨998900296996171056100429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21309873002584982530142485 998900296996171056100429)
            ·
              refine ⟨374587611373564146037661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998900296996171056100429 374587611373564146037661)
              ·
                refine ⟨140470354265086554764123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374587611373564146037661 140470354265086554764123)
                ·
                  rfl

theorem cell19_461641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_461641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461641 prefixEnd_461641 := by exact prefixLift 461641
  have htrace : WordTrace (prefixWord ++ tailWord_461641) baseStart_461641 baseEnd_461641 := by
    simpa [prefixWord, tailWord_461641, baseEnd_461641] using wordTrace_append hprefix tailTrace_461641
  have hstable : (prefixWord ++ tailWord_461641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461641).length < 2 ^ (prefixWord ++ tailWord_461641).sum := by decide
  have hdescent : baseEnd_461641 < baseStart_461641 := by decide
  rcases family_descends (prefixWord ++ tailWord_461641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461660 : List Nat := [2, 2, 4, 2, 1, 2, 6]
def baseStart_461660 : Nat := 118140960795 + 461660 * 2 ^ 59
def prefixEnd_461660 : Nat := 4983230072969 + 3 ^ 40 * 461660 * 2
def baseEnd_461660 : Nat := 46825378558966713447283

theorem tailTrace_461660 : CollatzResearch.WordTrace tailWord_461660 prefixEnd_461660 46825378558966713447283 := by
  unfold tailWord_461660
  simp only [CollatzResearch.WordTrace]
  refine ⟨8419061753746070047959217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11225415671661426730612289 8419061753746070047959217)
  ·
    refine ⟨6314296315309552535969413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8419061753746070047959217 6314296315309552535969413)
    ·
      refine ⟨1183930559120541100494265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6314296315309552535969413 1183930559120541100494265)
      ·
        refine ⟨887947919340405825370699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1183930559120541100494265 887947919340405825370699)
        ·
          refine ⟨1331921879010608738056049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887947919340405825370699 1331921879010608738056049)
          ·
            refine ⟨998941409257956553542037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1331921879010608738056049 998941409257956553542037)
            ·
              refine ⟨46825378558966713447283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 998941409257956553542037 46825378558966713447283)
              ·
                rfl

theorem cell19_461660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_461660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461660 prefixEnd_461660 := by exact prefixLift 461660
  have htrace : WordTrace (prefixWord ++ tailWord_461660) baseStart_461660 baseEnd_461660 := by
    simpa [prefixWord, tailWord_461660, baseEnd_461660] using wordTrace_append hprefix tailTrace_461660
  have hstable : (prefixWord ++ tailWord_461660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461660).length < 2 ^ (prefixWord ++ tailWord_461660).sum := by decide
  have hdescent : baseEnd_461660 < baseStart_461660 := by decide
  rcases family_descends (prefixWord ++ tailWord_461660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461791 : List Nat := [1, 1, 2, 3, 6, 1, 1, 4]
def baseStart_461791 : Nat := 118140960795 + 461791 * 2 ^ 59
def prefixEnd_461791 : Nat := 4983230072969 + 3 ^ 40 * 461791 * 2
def baseEnd_461791 : Nat := 140515996989930651430381

theorem tailTrace_461791 : CollatzResearch.WordTrace tailWord_461791 prefixEnd_461791 140515996989930651430381 := by
  unfold tailWord_461791
  simp only [CollatzResearch.WordTrace]
  refine ⟨16842901470017549468937227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11228600980011699645958151 16842901470017549468937227)
  ·
    refine ⟨25264352205026324203405841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16842901470017549468937227 25264352205026324203405841)
    ·
      refine ⟨18948264153769743152554381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25264352205026324203405841 18948264153769743152554381)
      ·
        refine ⟨7105599057663653682207893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18948264153769743152554381 7105599057663653682207893)
        ·
          refine ⟨333074955827983766353495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7105599057663653682207893 333074955827983766353495)
          ·
            refine ⟨499612433741975649530243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333074955827983766353495 499612433741975649530243)
            ·
              refine ⟨749418650612963474295365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499612433741975649530243 749418650612963474295365)
              ·
                refine ⟨140515996989930651430381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749418650612963474295365 140515996989930651430381)
                ·
                  rfl

theorem cell19_461791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 4].length) (baseStart_461791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461791 prefixEnd_461791 := by exact prefixLift 461791
  have htrace : WordTrace (prefixWord ++ tailWord_461791) baseStart_461791 baseEnd_461791 := by
    simpa [prefixWord, tailWord_461791, baseEnd_461791] using wordTrace_append hprefix tailTrace_461791
  have hstable : (prefixWord ++ tailWord_461791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461791).length < 2 ^ (prefixWord ++ tailWord_461791).sum := by decide
  have hdescent : baseEnd_461791 < baseStart_461791 := by decide
  rcases family_descends (prefixWord ++ tailWord_461791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461909 : List Nat := [1, 3, 2, 2, 1, 2, 4, 4]
def baseStart_461909 : Nat := 118140960795 + 461909 * 2 ^ 59
def prefixEnd_461909 : Nat := 4983230072969 + 3 ^ 40 * 461909 * 2
def baseEnd_461909 : Nat := 140551902600141340807837

theorem tailTrace_461909 : CollatzResearch.WordTrace tailWord_461909 prefixEnd_461909 140551902600141340807837 := by
  unfold tailWord_461909
  simp only [CollatzResearch.WordTrace]
  refine ⟨16847205283590055621732781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11231470189060037081155187 16847205283590055621732781)
  ·
    refine ⟨6317701981346270858149793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16847205283590055621732781 6317701981346270858149793)
    ·
      refine ⟨4738276486009703143612345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6317701981346270858149793 4738276486009703143612345)
      ·
        refine ⟨3553707364507277357709259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4738276486009703143612345 3553707364507277357709259)
        ·
          refine ⟨5330561046760916036563889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553707364507277357709259 5330561046760916036563889)
          ·
            refine ⟨3997920785070687027422917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5330561046760916036563889 3997920785070687027422917)
            ·
              refine ⟨749610147200753817641797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3997920785070687027422917 749610147200753817641797)
              ·
                refine ⟨140551902600141340807837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749610147200753817641797 140551902600141340807837)
                ·
                  rfl

theorem cell19_461909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_461909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461909 prefixEnd_461909 := by exact prefixLift 461909
  have htrace : WordTrace (prefixWord ++ tailWord_461909) baseStart_461909 baseEnd_461909 := by
    simpa [prefixWord, tailWord_461909, baseEnd_461909] using wordTrace_append hprefix tailTrace_461909
  have hstable : (prefixWord ++ tailWord_461909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461909).length < 2 ^ (prefixWord ++ tailWord_461909).sum := by decide
  have hdescent : baseEnd_461909 < baseStart_461909 := by decide
  rcases family_descends (prefixWord ++ tailWord_461909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461968 : List Nat := [2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_461968 : Nat := 118140960795 + 461968 * 2 ^ 59
def prefixEnd_461968 : Nat := 4983230072969 + 3 ^ 40 * 461968 * 2
def baseEnd_461968 : Nat := 140569855405246685496565

theorem tailTrace_461968 : CollatzResearch.WordTrace tailWord_461968 prefixEnd_461968 140569855405246685496565 := by
  unfold tailWord_461968
  simp only [CollatzResearch.WordTrace]
  refine ⟨8424678595188154349065279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11232904793584205798753705 8424678595188154349065279)
  ·
    refine ⟨12637017892782231523597919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8424678595188154349065279 12637017892782231523597919)
    ·
      refine ⟨18955526839173347285396879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12637017892782231523597919 18955526839173347285396879)
      ·
        refine ⟨28433290258760020928095319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18955526839173347285396879 28433290258760020928095319)
        ·
          refine ⟨42649935388140031392142979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28433290258760020928095319 42649935388140031392142979)
          ·
            refine ⟨63974903082210047088214469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42649935388140031392142979 63974903082210047088214469)
            ·
              refine ⟨11995294327914383829040213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63974903082210047088214469 11995294327914383829040213)
              ·
                refine ⟨140569855405246685496565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11995294327914383829040213 140569855405246685496565)
                ·
                  rfl

theorem cell19_461968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_461968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461968 prefixEnd_461968 := by exact prefixLift 461968
  have htrace : WordTrace (prefixWord ++ tailWord_461968) baseStart_461968 baseEnd_461968 := by
    simpa [prefixWord, tailWord_461968, baseEnd_461968] using wordTrace_append hprefix tailTrace_461968
  have hstable : (prefixWord ++ tailWord_461968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461968).length < 2 ^ (prefixWord ++ tailWord_461968).sum := by decide
  have hdescent : baseEnd_461968 < baseStart_461968 := by decide
  rcases family_descends (prefixWord ++ tailWord_461968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461987 : List Nat := [1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_461987 : Nat := 118140960795 + 461987 * 2 ^ 59
def prefixEnd_461987 : Nat := 4983230072969 + 3 ^ 40 * 461987 * 2
def baseEnd_461987 : Nat := 140575636817060271074291

theorem tailTrace_461987 : CollatzResearch.WordTrace tailWord_461987 prefixEnd_461987 140575636817060271074291 := by
  unfold tailWord_461987
  simp only [CollatzResearch.WordTrace]
  refine ⟨16850050177307474943072215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11233366784871649962048143 16850050177307474943072215)
  ·
    refine ⟨25275075265961212414608323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16850050177307474943072215 25275075265961212414608323)
    ·
      refine ⟨37912612898941818621912485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25275075265961212414608323 37912612898941818621912485)
      ·
        refine ⟨7108614918551590991608591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37912612898941818621912485 7108614918551590991608591)
        ·
          refine ⟨10662922377827386487412887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7108614918551590991608591 10662922377827386487412887)
          ·
            refine ⟨15994383566741079731119331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10662922377827386487412887 15994383566741079731119331)
            ·
              refine ⟨23991575350111619596678997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15994383566741079731119331 23991575350111619596678997)
              ·
                refine ⟨140575636817060271074291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23991575350111619596678997 140575636817060271074291)
                ·
                  rfl

theorem cell19_461987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_461987 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461987 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461987 prefixEnd_461987 := by exact prefixLift 461987
  have htrace : WordTrace (prefixWord ++ tailWord_461987) baseStart_461987 baseEnd_461987 := by
    simpa [prefixWord, tailWord_461987, baseEnd_461987] using wordTrace_append hprefix tailTrace_461987
  have hstable : (prefixWord ++ tailWord_461987).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461987).length < 2 ^ (prefixWord ++ tailWord_461987).sum := by decide
  have hdescent : baseEnd_461987 < baseStart_461987 := by decide
  rcases family_descends (prefixWord ++ tailWord_461987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462036 : List Nat := [2, 4, 1, 4, 1, 2, 2, 3]
def baseStart_462036 : Nat := 118140960795 + 462036 * 2 ^ 59
def prefixEnd_462036 : Nat := 4983230072969 + 3 ^ 40 * 462036 * 2
def baseEnd_462036 : Nat := 140590546773842675985269

theorem tailTrace_462036 : CollatzResearch.WordTrace tailWord_462036 prefixEnd_462036 140590546773842675985269 := by
  unfold tailWord_462036
  simp only [CollatzResearch.WordTrace]
  refine ⟨8425918677064978155802981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11234558236086637541070641 8425918677064978155802981)
  ·
    refine ⟨1579859751949683404213059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8425918677064978155802981 1579859751949683404213059)
    ·
      refine ⟨2369789627924525106319589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579859751949683404213059 2369789627924525106319589)
      ·
        refine ⟨444335555235848457434923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2369789627924525106319589 444335555235848457434923)
        ·
          refine ⟨666503332853772686152385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444335555235848457434923 666503332853772686152385)
          ·
            refine ⟨499877499640329514614289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666503332853772686152385 499877499640329514614289)
            ·
              refine ⟨374908124730247135960717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499877499640329514614289 374908124730247135960717)
              ·
                refine ⟨140590546773842675985269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374908124730247135960717 140590546773842675985269)
                ·
                  rfl

theorem cell19_462036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_462036 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462036 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462036 prefixEnd_462036 := by exact prefixLift 462036
  have htrace : WordTrace (prefixWord ++ tailWord_462036) baseStart_462036 baseEnd_462036 := by
    simpa [prefixWord, tailWord_462036, baseEnd_462036] using wordTrace_append hprefix tailTrace_462036
  have hstable : (prefixWord ++ tailWord_462036).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462036).length < 2 ^ (prefixWord ++ tailWord_462036).sum := by decide
  have hdescent : baseEnd_462036 < baseStart_462036 := by decide
  rcases family_descends (prefixWord ++ tailWord_462036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462038 : List Nat := [5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_462038 : Nat := 118140960795 + 462038 * 2 ^ 59
def prefixEnd_462038 : Nat := 4983230072969 + 3 ^ 40 * 462038 * 2
def baseEnd_462038 : Nat := 140591155343507263940819

theorem tailTrace_462038 : CollatzResearch.WordTrace tailWord_462038 prefixEnd_462038 140591155343507263940819 := by
  unfold tailWord_462038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1053244393757669415823673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11234606866748473768785845 1053244393757669415823673)
  ·
    refine ⟨789933295318252061867755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1053244393757669415823673 789933295318252061867755)
    ·
      refine ⟨1184899942977378092801633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789933295318252061867755 1184899942977378092801633)
      ·
        refine ⟨888674957233033569601225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1184899942977378092801633 888674957233033569601225)
        ·
          refine ⟨666506217924775177200919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888674957233033569601225 666506217924775177200919)
          ·
            refine ⟨999759326887162765801379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666506217924775177200919 999759326887162765801379)
            ·
              refine ⟨1499638990330744148702069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999759326887162765801379 1499638990330744148702069)
              ·
                refine ⟨140591155343507263940819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1499638990330744148702069 140591155343507263940819)
                ·
                  rfl

theorem cell19_462038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_462038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462038 prefixEnd_462038 := by exact prefixLift 462038
  have htrace : WordTrace (prefixWord ++ tailWord_462038) baseStart_462038 baseEnd_462038 := by
    simpa [prefixWord, tailWord_462038, baseEnd_462038] using wordTrace_append hprefix tailTrace_462038
  have hstable : (prefixWord ++ tailWord_462038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462038).length < 2 ^ (prefixWord ++ tailWord_462038).sum := by decide
  have hdescent : baseEnd_462038 < baseStart_462038 := by decide
  rcases family_descends (prefixWord ++ tailWord_462038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462061 : List Nat := [1, 5, 1, 2, 2, 1, 7]
def baseStart_462061 : Nat := 118140960795 + 462061 * 2 ^ 59
def prefixEnd_462061 : Nat := 4983230072969 + 3 ^ 40 * 462061 * 2
def baseEnd_462061 : Nat := 46866051298216675143215

theorem tailTrace_462061 : CollatzResearch.WordTrace tailWord_462061 prefixEnd_462061 46866051298216675143215 := by
  unfold tailWord_462061
  simp only [CollatzResearch.WordTrace]
  refine ⟨16852749179039385581266037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11235166119359590387510691 16852749179039385581266037)
  ·
    refine ⟨1579945235534942398243691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16852749179039385581266037 1579945235534942398243691)
    ·
      refine ⟨2369917853302413597365537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579945235534942398243691 2369917853302413597365537)
      ·
        refine ⟨1777438389976810198024153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2369917853302413597365537 1777438389976810198024153)
        ·
          refine ⟨1333078792482607648518115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1777438389976810198024153 1333078792482607648518115)
          ·
            refine ⟨1999618188723911472777173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333078792482607648518115 1999618188723911472777173)
            ·
              refine ⟨46866051298216675143215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1999618188723911472777173 46866051298216675143215)
              ·
                rfl

theorem cell19_462061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_462061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462061 prefixEnd_462061 := by exact prefixLift 462061
  have htrace : WordTrace (prefixWord ++ tailWord_462061) baseStart_462061 baseEnd_462061 := by
    simpa [prefixWord, tailWord_462061, baseEnd_462061] using wordTrace_append hprefix tailTrace_462061
  have hstable : (prefixWord ++ tailWord_462061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462061).length < 2 ^ (prefixWord ++ tailWord_462061).sum := by decide
  have hdescent : baseEnd_462061 < baseStart_462061 := by decide
  rcases family_descends (prefixWord ++ tailWord_462061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462078 : List Nat := [4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_462078 : Nat := 118140960795 + 462078 * 2 ^ 59
def prefixEnd_462078 : Nat := 4983230072969 + 3 ^ 40 * 462078 * 2
def baseEnd_462078 : Nat := 140603326736799023051821

theorem tailTrace_462078 : CollatzResearch.WordTrace tailWord_462078 prefixEnd_462078 140603326736799023051821 := by
  unfold tailWord_462078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106671152497224685579361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11235579479985198323089925 2106671152497224685579361)
  ·
    refine ⟨1580003364372918514184521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2106671152497224685579361 1580003364372918514184521)
    ·
      refine ⟨1185002523279688885638391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1580003364372918514184521 1185002523279688885638391)
      ·
        refine ⟨1777503784919533328457587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185002523279688885638391 1777503784919533328457587)
        ·
          refine ⟨2666255677379299992686381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777503784919533328457587 2666255677379299992686381)
          ·
            refine ⟨999845879017237497257393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2666255677379299992686381 999845879017237497257393)
            ·
              refine ⟨749884409262928122943045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999845879017237497257393 749884409262928122943045)
              ·
                refine ⟨140603326736799023051821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749884409262928122943045 140603326736799023051821)
                ·
                  rfl

theorem cell19_462078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_462078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462078 prefixEnd_462078 := by exact prefixLift 462078
  have htrace : WordTrace (prefixWord ++ tailWord_462078) baseStart_462078 baseEnd_462078 := by
    simpa [prefixWord, tailWord_462078, baseEnd_462078] using wordTrace_append hprefix tailTrace_462078
  have hstable : (prefixWord ++ tailWord_462078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462078).length < 2 ^ (prefixWord ++ tailWord_462078).sum := by decide
  have hdescent : baseEnd_462078 < baseStart_462078 := by decide
  rcases family_descends (prefixWord ++ tailWord_462078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462209 : List Nat := [1, 2, 4, 3, 2, 2, 2, 3]
def baseStart_462209 : Nat := 118140960795 + 462209 * 2 ^ 59
def prefixEnd_462209 : Nat := 4983230072969 + 3 ^ 40 * 462209 * 2
def baseEnd_462209 : Nat := 140643188049829534140353

theorem tailTrace_462209 : CollatzResearch.WordTrace tailWord_462209 prefixEnd_462209 140643188049829534140353 := by
  unfold tailWord_462209
  simp only [CollatzResearch.WordTrace]
  refine ⟨16858147182503206857653681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11238764788335471238435787 16858147182503206857653681)
  ·
    refine ⟨12643610386877405143240261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16858147182503206857653681 12643610386877405143240261)
    ·
      refine ⟨2370676947539513464357549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12643610386877405143240261 2370676947539513464357549)
      ·
        refine ⟨889003855327317549134081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2370676947539513464357549 889003855327317549134081)
        ·
          refine ⟨666752891495488161850561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889003855327317549134081 666752891495488161850561)
          ·
            refine ⟨500064668621616121387921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 666752891495488161850561 500064668621616121387921)
            ·
              refine ⟨375048501466212091040941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500064668621616121387921 375048501466212091040941)
              ·
                refine ⟨140643188049829534140353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375048501466212091040941 140643188049829534140353)
                ·
                  rfl

theorem cell19_462209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_462209 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462209 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462209 prefixEnd_462209 := by exact prefixLift 462209
  have htrace : WordTrace (prefixWord ++ tailWord_462209) baseStart_462209 baseEnd_462209 := by
    simpa [prefixWord, tailWord_462209, baseEnd_462209] using wordTrace_append hprefix tailTrace_462209
  have hstable : (prefixWord ++ tailWord_462209).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462209).length < 2 ^ (prefixWord ++ tailWord_462209).sum := by decide
  have hdescent : baseEnd_462209 < baseStart_462209 := by decide
  rcases family_descends (prefixWord ++ tailWord_462209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462211 : List Nat := [1, 1, 1, 3, 5, 3, 2, 3]
def baseStart_462211 : Nat := 118140960795 + 462211 * 2 ^ 59
def prefixEnd_462211 : Nat := 4983230072969 + 3 ^ 40 * 462211 * 2
def baseEnd_462211 : Nat := 140643796619494122095903

theorem tailTrace_462211 : CollatzResearch.WordTrace tailWord_462211 prefixEnd_462211 140643796619494122095903 := by
  unfold tailWord_462211
  simp only [CollatzResearch.WordTrace]
  refine ⟨16858220128495961199226487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11238813418997307466150991 16858220128495961199226487)
  ·
    refine ⟨25287330192743941798839731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16858220128495961199226487 25287330192743941798839731)
    ·
      refine ⟨37930995289115912698259597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25287330192743941798839731 37930995289115912698259597)
      ·
        refine ⟨14224123233418467261847349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37930995289115912698259597 14224123233418467261847349)
        ·
          refine ⟨1333511553132981305798189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14224123233418467261847349 1333511553132981305798189)
          ·
            refine ⟨500066832424867989674321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1333511553132981305798189 500066832424867989674321)
            ·
              refine ⟨375050124318650992255741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500066832424867989674321 375050124318650992255741)
              ·
                refine ⟨140643796619494122095903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375050124318650992255741 140643796619494122095903)
                ·
                  rfl

theorem cell19_462211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_462211 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462211 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462211 prefixEnd_462211 := by exact prefixLift 462211
  have htrace : WordTrace (prefixWord ++ tailWord_462211) baseStart_462211 baseEnd_462211 := by
    simpa [prefixWord, tailWord_462211, baseEnd_462211] using wordTrace_append hprefix tailTrace_462211
  have hstable : (prefixWord ++ tailWord_462211).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462211).length < 2 ^ (prefixWord ++ tailWord_462211).sum := by decide
  have hdescent : baseEnd_462211 < baseStart_462211 := by decide
  rcases family_descends (prefixWord ++ tailWord_462211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462213 : List Nat := [1, 3, 1, 1, 3, 1, 6, 3]
def baseStart_462213 : Nat := 118140960795 + 462213 * 2 ^ 59
def prefixEnd_462213 : Nat := 4983230072969 + 3 ^ 40 * 462213 * 2
def baseEnd_462213 : Nat := 140644405189158710051453

theorem tailTrace_462213 : CollatzResearch.WordTrace tailWord_462213 prefixEnd_462213 140644405189158710051453 := by
  unfold tailWord_462213
  simp only [CollatzResearch.WordTrace]
  refine ⟨16858293074488715540799293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11238862049659143693866195 16858293074488715540799293)
  ·
    refine ⟨6321859902933268327799735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16858293074488715540799293 6321859902933268327799735)
    ·
      refine ⟨9482789854399902491699603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6321859902933268327799735 9482789854399902491699603)
      ·
        refine ⟨14224184781599853737549405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9482789854399902491699603 14224184781599853737549405)
        ·
          refine ⟨5334069293099945151581027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14224184781599853737549405 5334069293099945151581027)
          ·
            refine ⟨8001103939649917727371541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334069293099945151581027 8001103939649917727371541)
            ·
              refine ⟨375051747171089893470541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8001103939649917727371541 375051747171089893470541)
              ·
                refine ⟨140644405189158710051453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375051747171089893470541 140644405189158710051453)
                ·
                  rfl

theorem cell19_462213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_462213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462213 prefixEnd_462213 := by exact prefixLift 462213
  have htrace : WordTrace (prefixWord ++ tailWord_462213) baseStart_462213 baseEnd_462213 := by
    simpa [prefixWord, tailWord_462213, baseEnd_462213] using wordTrace_append hprefix tailTrace_462213
  have hstable : (prefixWord ++ tailWord_462213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462213).length < 2 ^ (prefixWord ++ tailWord_462213).sum := by decide
  have hdescent : baseEnd_462213 < baseStart_462213 := by decide
  rcases family_descends (prefixWord ++ tailWord_462213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462272 : List Nat := [2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_462272 : Nat := 118140960795 + 462272 * 2 ^ 59
def prefixEnd_462272 : Nat := 4983230072969 + 3 ^ 40 * 462272 * 2
def baseEnd_462272 : Nat := 140662357994264054740181

theorem tailTrace_462272 : CollatzResearch.WordTrace tailWord_462272 prefixEnd_462272 140662357994264054740181 := by
  unfold tailWord_462272
  simp only [CollatzResearch.WordTrace]
  refine ⟨8430222490637484308598535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11240296654183312411464713 8430222490637484308598535)
  ·
    refine ⟨12645333735956226462897803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8430222490637484308598535 12645333735956226462897803)
    ·
      refine ⟨18968000603934339694346705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12645333735956226462897803 18968000603934339694346705)
      ·
        refine ⟨14226000452950754770760029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18968000603934339694346705 14226000452950754770760029)
        ·
          refine ⟨5334750169856533039035011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14226000452950754770760029 5334750169856533039035011)
          ·
            refine ⟨8002125254784799558552517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334750169856533039035011 8002125254784799558552517)
            ·
              refine ⟨1500398485272149917228597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8002125254784799558552517 1500398485272149917228597)
              ·
                refine ⟨140662357994264054740181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1500398485272149917228597 140662357994264054740181)
                ·
                  rfl

theorem cell19_462272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_462272 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462272 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462272 prefixEnd_462272 := by exact prefixLift 462272
  have htrace : WordTrace (prefixWord ++ tailWord_462272) baseStart_462272 baseEnd_462272 := by
    simpa [prefixWord, tailWord_462272, baseEnd_462272] using wordTrace_append hprefix tailTrace_462272
  have hstable : (prefixWord ++ tailWord_462272).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462272).length < 2 ^ (prefixWord ++ tailWord_462272).sum := by decide
  have hdescent : baseEnd_462272 < baseStart_462272 := by decide
  rcases family_descends (prefixWord ++ tailWord_462272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462382 : List Nat := [4, 1, 3, 1, 2, 1, 4, 3]
def baseStart_462382 : Nat := 118140960795 + 462382 * 2 ^ 59
def prefixEnd_462382 : Nat := 4983230072969 + 3 ^ 40 * 462382 * 2
def baseEnd_462382 : Nat := 140695829325816392295437

theorem tailTrace_462382 : CollatzResearch.WordTrace tailWord_462382 prefixEnd_462382 140695829325816392295437 := by
  unfold tailWord_462382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108057126359557175462675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11242971340584304935800933 2108057126359557175462675)
  ·
    refine ⟨3162085689539335763194013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2108057126359557175462675 3162085689539335763194013)
    ·
      refine ⟨1185782133577250911197755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3162085689539335763194013 1185782133577250911197755)
      ·
        refine ⟨1778673200365876366796633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185782133577250911197755 1778673200365876366796633)
        ·
          refine ⟨1334004900274407275097475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1778673200365876366796633 1334004900274407275097475)
          ·
            refine ⟨2001007350411610912646213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334004900274407275097475 2001007350411610912646213)
            ·
              refine ⟨375188878202177046121165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2001007350411610912646213 375188878202177046121165)
              ·
                refine ⟨140695829325816392295437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375188878202177046121165 140695829325816392295437)
                ·
                  rfl

theorem cell19_462382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_462382 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462382 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462382 prefixEnd_462382 := by exact prefixLift 462382
  have htrace : WordTrace (prefixWord ++ tailWord_462382) baseStart_462382 baseEnd_462382 := by
    simpa [prefixWord, tailWord_462382, baseEnd_462382] using wordTrace_append hprefix tailTrace_462382
  have hstable : (prefixWord ++ tailWord_462382).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462382).length < 2 ^ (prefixWord ++ tailWord_462382).sum := by decide
  have hdescent : baseEnd_462382 < baseStart_462382 := by decide
  rcases family_descends (prefixWord ++ tailWord_462382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462517 : List Nat := [1, 3, 3, 3, 2, 1, 6]
def baseStart_462517 : Nat := 118140960795 + 462517 * 2 ^ 59
def prefixEnd_462517 : Nat := 4983230072969 + 3 ^ 40 * 462517 * 2
def baseEnd_462517 : Nat := 46912302592725359765023

theorem tailTrace_462517 : CollatzResearch.WordTrace tailWord_462517 prefixEnd_462517 46912302592725359765023 := by
  unfold tailWord_462517
  simp only [CollatzResearch.WordTrace]
  refine ⟨16869380865387375459865805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11246253910258250306577203 16869380865387375459865805)
  ·
    refine ⟨6326017824520265797449677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16869380865387375459865805 6326017824520265797449677)
    ·
      refine ⟨2372256684195099674043629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6326017824520265797449677 2372256684195099674043629)
      ·
        refine ⟨889596256573162377766361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2372256684195099674043629 889596256573162377766361)
        ·
          refine ⟨667197192429871783324771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889596256573162377766361 667197192429871783324771)
          ·
            refine ⟨1000795788644807674987157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667197192429871783324771 1000795788644807674987157)
            ·
              refine ⟨46912302592725359765023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1000795788644807674987157 46912302592725359765023)
              ·
                rfl

theorem cell19_462517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_462517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462517 prefixEnd_462517 := by exact prefixLift 462517
  have htrace : WordTrace (prefixWord ++ tailWord_462517) baseStart_462517 baseEnd_462517 := by
    simpa [prefixWord, tailWord_462517, baseEnd_462517] using wordTrace_append hprefix tailTrace_462517
  have hstable : (prefixWord ++ tailWord_462517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462517).length < 2 ^ (prefixWord ++ tailWord_462517).sum := by decide
  have hdescent : baseEnd_462517 < baseStart_462517 := by decide
  rcases family_descends (prefixWord ++ tailWord_462517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462519 : List Nat := [1, 1, 3, 1, 5, 2, 6]
def baseStart_462519 : Nat := 118140960795 + 462519 * 2 ^ 59
def prefixEnd_462519 : Nat := 4983230072969 + 3 ^ 40 * 462519 * 2
def baseEnd_462519 : Nat := 46912505449280222416873

theorem tailTrace_462519 : CollatzResearch.WordTrace tailWord_462519 prefixEnd_462519 46912505449280222416873 := by
  unfold tailWord_462519
  simp only [CollatzResearch.WordTrace]
  refine ⟨16869453811380129801438611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11246302540920086534292407 16869453811380129801438611)
  ·
    refine ⟨25304180717070194702157917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16869453811380129801438611 25304180717070194702157917)
    ·
      refine ⟨9489067768901323013309219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25304180717070194702157917 9489067768901323013309219)
      ·
        refine ⟨14233601653351984519963829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489067768901323013309219 14233601653351984519963829)
        ·
          refine ⟨1334400155001748548746609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14233601653351984519963829 1334400155001748548746609)
          ·
            refine ⟨1000800116251311411559957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1334400155001748548746609 1000800116251311411559957)
            ·
              refine ⟨46912505449280222416873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1000800116251311411559957 46912505449280222416873)
              ·
                rfl

theorem cell19_462519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_462519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462519 prefixEnd_462519 := by exact prefixLift 462519
  have htrace : WordTrace (prefixWord ++ tailWord_462519) baseStart_462519 baseEnd_462519 := by
    simpa [prefixWord, tailWord_462519, baseEnd_462519] using wordTrace_append hprefix tailTrace_462519
  have hstable : (prefixWord ++ tailWord_462519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462519).length < 2 ^ (prefixWord ++ tailWord_462519).sum := by decide
  have hdescent : baseEnd_462519 < baseStart_462519 := by decide
  rcases family_descends (prefixWord ++ tailWord_462519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462650 : List Nat := [3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_462650 : Nat := 118140960795 + 462650 * 2 ^ 59
def prefixEnd_462650 : Nat := 4983230072969 + 3 ^ 40 * 462650 * 2
def baseEnd_462650 : Nat := 140777377660871178339151

theorem tailTrace_462650 : CollatzResearch.WordTrace tailWord_462650 prefixEnd_462650 140777377660871178339151 := by
  unfold tailWord_462650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218557943476384793614351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11249487849270359449638269 4218557943476384793614351)
  ·
    refine ⟨6327836915214577190421527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4218557943476384793614351 6327836915214577190421527)
    ·
      refine ⟨9491755372821865785632291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6327836915214577190421527 9491755372821865785632291)
      ·
        refine ⟨14237633059232798678448437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9491755372821865785632291 14237633059232798678448437)
        ·
          refine ⟨1334778099303074876104541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14237633059232798678448437 1334778099303074876104541)
          ·
            refine ⟨500541787238653078539203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1334778099303074876104541 500541787238653078539203)
            ·
              refine ⟨750812680857979617808805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500541787238653078539203 750812680857979617808805)
              ·
                refine ⟨140777377660871178339151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 750812680857979617808805 140777377660871178339151)
                ·
                  rfl

theorem cell19_462650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_462650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462650 prefixEnd_462650 := by exact prefixLift 462650
  have htrace : WordTrace (prefixWord ++ tailWord_462650) baseStart_462650 baseEnd_462650 := by
    simpa [prefixWord, tailWord_462650, baseEnd_462650] using wordTrace_append hprefix tailTrace_462650
  have hstable : (prefixWord ++ tailWord_462650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462650).length < 2 ^ (prefixWord ++ tailWord_462650).sum := by decide
  have hdescent : baseEnd_462650 < baseStart_462650 := by decide
  rcases family_descends (prefixWord ++ tailWord_462650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462652 : List Nat := [2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_462652 : Nat := 118140960795 + 462652 * 2 ^ 59
def prefixEnd_462652 : Nat := 4983230072969 + 3 ^ 40 * 462652 * 2
def baseEnd_462652 : Nat := 140777986230535766294701

theorem tailTrace_462652 : CollatzResearch.WordTrace tailWord_462652 prefixEnd_462652 140777986230535766294701 := by
  unfold tailWord_462652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8437152359949146758015105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11249536479932195677353473 8437152359949146758015105)
  ·
    refine ⟨6327864269961860068511329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8437152359949146758015105 6327864269961860068511329)
    ·
      refine ⟨4745898202471395051383497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6327864269961860068511329 4745898202471395051383497)
      ·
        refine ⟨3559423651853546288537623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4745898202471395051383497 3559423651853546288537623)
        ·
          refine ⟨5339135477780319432806435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3559423651853546288537623 5339135477780319432806435)
          ·
            refine ⟨8008703216670479149209653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339135477780319432806435 8008703216670479149209653)
            ·
              refine ⟨750815926562857420238405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8008703216670479149209653 750815926562857420238405)
              ·
                refine ⟨140777986230535766294701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 750815926562857420238405 140777986230535766294701)
                ·
                  rfl

theorem cell19_462652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_462652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462652 prefixEnd_462652 := by exact prefixLift 462652
  have htrace : WordTrace (prefixWord ++ tailWord_462652) baseStart_462652 baseEnd_462652 := by
    simpa [prefixWord, tailWord_462652, baseEnd_462652] using wordTrace_append hprefix tailTrace_462652
  have hstable : (prefixWord ++ tailWord_462652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462652).length < 2 ^ (prefixWord ++ tailWord_462652).sum := by decide
  have hdescent : baseEnd_462652 < baseStart_462652 := by decide
  rcases family_descends (prefixWord ++ tailWord_462652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462709 : List Nat := [1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_462709 : Nat := 118140960795 + 462709 * 2 ^ 59
def prefixEnd_462709 : Nat := 4983230072969 + 3 ^ 40 * 462709 * 2
def baseEnd_462709 : Nat := 140795330465976523027879

theorem tailTrace_462709 : CollatzResearch.WordTrace tailWord_462709 prefixEnd_462709 140795330465976523027879 := by
  unfold tailWord_462709
  simp only [CollatzResearch.WordTrace]
  refine ⟨16876383680691792250855181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11250922453794528167236787 16876383680691792250855181)
  ·
    refine ⟨6328643880259422094070693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16876383680691792250855181 6328643880259422094070693)
    ·
      refine ⟨1186620727548641642638255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6328643880259422094070693 1186620727548641642638255)
      ·
        refine ⟨1779931091322962463957383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1186620727548641642638255 1779931091322962463957383)
        ·
          refine ⟨2669896636984443695936075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1779931091322962463957383 2669896636984443695936075)
          ·
            refine ⟨4004844955476665543904113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2669896636984443695936075 4004844955476665543904113)
            ·
              refine ⟨3003633716607499157928085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4004844955476665543904113 3003633716607499157928085)
              ·
                refine ⟨140795330465976523027879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3003633716607499157928085 140795330465976523027879)
                ·
                  rfl

theorem cell19_462709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_462709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462709 prefixEnd_462709 := by exact prefixLift 462709
  have htrace : WordTrace (prefixWord ++ tailWord_462709) baseStart_462709 baseEnd_462709 := by
    simpa [prefixWord, tailWord_462709, baseEnd_462709] using wordTrace_append hprefix tailTrace_462709
  have hstable : (prefixWord ++ tailWord_462709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462709).length < 2 ^ (prefixWord ++ tailWord_462709).sum := by decide
  have hdescent : baseEnd_462709 < baseStart_462709 := by decide
  rcases family_descends (prefixWord ++ tailWord_462709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462802 : List Nat := [3, 2, 2, 3, 3, 6]
def baseStart_462802 : Nat := 118140960795 + 462802 * 2 ^ 59
def prefixEnd_462802 : Nat := 4983230072969 + 3 ^ 40 * 462802 * 2
def baseEnd_462802 : Nat := 15647069883931095884551

theorem tailTrace_462802 : CollatzResearch.WordTrace tailWord_462802 prefixEnd_462802 15647069883931095884551 := by
  unfold tailWord_462802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219943917338717283497665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11253183779569912755993773 4219943917338717283497665)
  ·
    refine ⟨3164957938004037962623249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4219943917338717283497665 3164957938004037962623249)
    ·
      refine ⟨2373718453503028471967437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3164957938004037962623249 2373718453503028471967437)
      ·
        refine ⟨890144420063635676987789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2373718453503028471967437 890144420063635676987789)
        ·
          refine ⟨333804157523863378870421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890144420063635676987789 333804157523863378870421)
          ·
            refine ⟨15647069883931095884551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 333804157523863378870421 15647069883931095884551)
            ·
              rfl

theorem cell19_462802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 6].length) (baseStart_462802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462802 prefixEnd_462802 := by exact prefixLift 462802
  have htrace : WordTrace (prefixWord ++ tailWord_462802) baseStart_462802 baseEnd_462802 := by
    simpa [prefixWord, tailWord_462802, baseEnd_462802] using wordTrace_append hprefix tailTrace_462802
  have hstable : (prefixWord ++ tailWord_462802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462802).length < 2 ^ (prefixWord ++ tailWord_462802).sum := by decide
  have hdescent : baseEnd_462802 < baseStart_462802 := by decide
  rcases family_descends (prefixWord ++ tailWord_462802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462838 : List Nat := [5, 1, 1, 1, 4, 1, 3, 3]
def baseStart_462838 : Nat := 118140960795 + 462838 * 2 ^ 59
def prefixEnd_462838 : Nat := 4983230072969 + 3 ^ 40 * 462838 * 2
def baseEnd_462838 : Nat := 140834583209342446160861

theorem tailTrace_462838 : CollatzResearch.WordTrace tailWord_462838 prefixEnd_462838 140834583209342446160861 := by
  unfold tailWord_462838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055068043576527955143823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11254059131482964854867445 1055068043576527955143823)
  ·
    refine ⟨1582602065364791932715735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1055068043576527955143823 1582602065364791932715735)
    ·
      refine ⟨2373903098047187899073603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582602065364791932715735 2373903098047187899073603)
      ·
        refine ⟨3560854647070781848610405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2373903098047187899073603 3560854647070781848610405)
        ·
          refine ⟨667660246325771596614451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3560854647070781848610405 667660246325771596614451)
          ·
            refine ⟨1001490369488657394921677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667660246325771596614451 1001490369488657394921677)
            ·
              refine ⟨375558888558246523095629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1001490369488657394921677 375558888558246523095629)
              ·
                refine ⟨140834583209342446160861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375558888558246523095629 140834583209342446160861)
                ·
                  rfl

theorem cell19_462838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_462838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462838 prefixEnd_462838 := by exact prefixLift 462838
  have htrace : WordTrace (prefixWord ++ tailWord_462838) baseStart_462838 baseEnd_462838 := by
    simpa [prefixWord, tailWord_462838, baseEnd_462838] using wordTrace_append hprefix tailTrace_462838
  have hstable : (prefixWord ++ tailWord_462838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462838).length < 2 ^ (prefixWord ++ tailWord_462838).sum := by decide
  have hdescent : baseEnd_462838 < baseStart_462838 := by decide
  rcases family_descends (prefixWord ++ tailWord_462838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462897 : List Nat := [1, 2, 2, 3, 1, 5, 2, 3]
def baseStart_462897 : Nat := 118140960795 + 462897 * 2 ^ 59
def prefixEnd_462897 : Nat := 4983230072969 + 3 ^ 40 * 462897 * 2
def baseEnd_462897 : Nat := 140852536014447790849589

theorem tailTrace_462897 : CollatzResearch.WordTrace tailWord_462897 prefixEnd_462897 140852536014447790849589 := by
  unfold tailWord_462897
  simp only [CollatzResearch.WordTrace]
  refine ⟨16883240604010700358698945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11255493736007133572465963 16883240604010700358698945)
  ·
    refine ⟨12662430453008025269024209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16883240604010700358698945 12662430453008025269024209)
    ·
      refine ⟨9496822839756018951768157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12662430453008025269024209 9496822839756018951768157)
      ·
        refine ⟨3561308564908507106913059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9496822839756018951768157 3561308564908507106913059)
        ·
          refine ⟨5341962847362760660369589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3561308564908507106913059 5341962847362760660369589)
          ·
            refine ⟨500809016940258811909649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5341962847362760660369589 500809016940258811909649)
            ·
              refine ⟨375606762705194108932237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 500809016940258811909649 375606762705194108932237)
              ·
                refine ⟨140852536014447790849589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375606762705194108932237 140852536014447790849589)
                ·
                  rfl

theorem cell19_462897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_462897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462897 prefixEnd_462897 := by exact prefixLift 462897
  have htrace : WordTrace (prefixWord ++ tailWord_462897) baseStart_462897 baseEnd_462897 := by
    simpa [prefixWord, tailWord_462897, baseEnd_462897] using wordTrace_append hprefix tailTrace_462897
  have hstable : (prefixWord ++ tailWord_462897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462897).length < 2 ^ (prefixWord ++ tailWord_462897).sum := by decide
  have hdescent : baseEnd_462897 < baseStart_462897 := by decide
  rcases family_descends (prefixWord ++ tailWord_462897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462899 : List Nat := [1, 1, 1, 2, 4, 1, 6, 3]
def baseStart_462899 : Nat := 118140960795 + 462899 * 2 ^ 59
def prefixEnd_462899 : Nat := 4983230072969 + 3 ^ 40 * 462899 * 2
def baseEnd_462899 : Nat := 140853144584112378805139

theorem tailTrace_462899 : CollatzResearch.WordTrace tailWord_462899 prefixEnd_462899 140853144584112378805139 := by
  unfold tailWord_462899
  simp only [CollatzResearch.WordTrace]
  refine ⟨16883313550003454700271751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11255542366668969800181167 16883313550003454700271751)
  ·
    refine ⟨25324970325005182050407627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16883313550003454700271751 25324970325005182050407627)
    ·
      refine ⟨37987455487507773075611441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25324970325005182050407627 37987455487507773075611441)
      ·
        refine ⟨28490591615630829806708581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37987455487507773075611441 28490591615630829806708581)
        ·
          refine ⟨5341985927930780588757859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28490591615630829806708581 5341985927930780588757859)
          ·
            refine ⟨8012978891896170883136789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5341985927930780588757859 8012978891896170883136789)
            ·
              refine ⟨375608385557633010147037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8012978891896170883136789 375608385557633010147037)
              ·
                refine ⟨140853144584112378805139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375608385557633010147037 140853144584112378805139)
                ·
                  rfl

theorem cell19_462899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_462899 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462899 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462899 prefixEnd_462899 := by exact prefixLift 462899
  have htrace : WordTrace (prefixWord ++ tailWord_462899) baseStart_462899 baseEnd_462899 := by
    simpa [prefixWord, tailWord_462899, baseEnd_462899] using wordTrace_append hprefix tailTrace_462899
  have hstable : (prefixWord ++ tailWord_462899).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462899).length < 2 ^ (prefixWord ++ tailWord_462899).sum := by decide
  have hdescent : baseEnd_462899 < baseStart_462899 := by decide
  rcases family_descends (prefixWord ++ tailWord_462899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462977 : List Nat := [1, 2, 4, 2, 10]
def baseStart_462977 : Nat := 118140960795 + 462977 * 2 ^ 59
def prefixEnd_462977 : Nat := 4983230072969 + 3 ^ 40 * 462977 * 2
def baseEnd_462977 : Nat := 5217662177815974410059

theorem tailTrace_462977 : CollatzResearch.WordTrace tailWord_462977 prefixEnd_462977 5217662177815974410059 := by
  unfold tailWord_462977
  simp only [CollatzResearch.WordTrace]
  refine ⟨16886158443720874021611185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11257438962480582681074123 16886158443720874021611185)
  ·
    refine ⟨12664618832790655516208389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16886158443720874021611185 12664618832790655516208389)
    ·
      refine ⟨2374616031148247909289073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12664618832790655516208389 2374616031148247909289073)
      ·
        refine ⟨1780962023361185931966805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2374616031148247909289073 1780962023361185931966805)
        ·
          refine ⟨5217662177815974410059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1780962023361185931966805 5217662177815974410059)
          ·
            rfl

theorem cell19_462977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 10].length) (baseStart_462977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462977 prefixEnd_462977 := by exact prefixLift 462977
  have htrace : WordTrace (prefixWord ++ tailWord_462977) baseStart_462977 baseEnd_462977 := by
    simpa [prefixWord, tailWord_462977, baseEnd_462977] using wordTrace_append hprefix tailTrace_462977
  have hstable : (prefixWord ++ tailWord_462977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462977).length < 2 ^ (prefixWord ++ tailWord_462977).sum := by decide
  have hdescent : baseEnd_462977 < baseStart_462977 := by decide
  rcases family_descends (prefixWord ++ tailWord_462977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_462990 : List Nat := [4, 1, 1, 3, 4, 1, 1, 4]
def baseStart_462990 : Nat := 118140960795 + 462990 * 2 ^ 59
def prefixEnd_462990 : Nat := 4983230072969 + 3 ^ 40 * 462990 * 2
def baseEnd_462990 : Nat := 140880834503851130782669

theorem tailTrace_462990 : CollatzResearch.WordTrace tailWord_462990 prefixEnd_462990 140880834503851130782669 := by
  unfold tailWord_462990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110829074084222155229303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11257755061782518161222949 2110829074084222155229303)
  ·
    refine ⟨3166243611126333232843955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110829074084222155229303 3166243611126333232843955)
    ·
      refine ⟨4749365416689499849265933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166243611126333232843955 4749365416689499849265933)
      ·
        refine ⟨1781012031258562443474725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4749365416689499849265933 1781012031258562443474725)
        ·
          refine ⟨333939755860980458151511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1781012031258562443474725 333939755860980458151511)
          ·
            refine ⟨500909633791470687227267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333939755860980458151511 500909633791470687227267)
            ·
              refine ⟨751364450687206030840901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500909633791470687227267 751364450687206030840901)
              ·
                refine ⟨140880834503851130782669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 751364450687206030840901 140880834503851130782669)
                ·
                  rfl

theorem cell19_462990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_462990 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_462990 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_462990 prefixEnd_462990 := by exact prefixLift 462990
  have htrace : WordTrace (prefixWord ++ tailWord_462990) baseStart_462990 baseEnd_462990 := by
    simpa [prefixWord, tailWord_462990, baseEnd_462990] using wordTrace_append hprefix tailTrace_462990
  have hstable : (prefixWord ++ tailWord_462990).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_462990).length < 2 ^ (prefixWord ++ tailWord_462990).sum := by decide
  have hdescent : baseEnd_462990 < baseStart_462990 := by decide
  rcases family_descends (prefixWord ++ tailWord_462990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463013 : List Nat := [1, 3, 1, 2, 1, 3, 5, 3]
def baseStart_463013 : Nat := 118140960795 + 463013 * 2 ^ 59
def prefixEnd_463013 : Nat := 4983230072969 + 3 ^ 40 * 463013 * 2
def baseEnd_463013 : Nat := 140887833054993892271495

theorem tailTrace_463013 : CollatzResearch.WordTrace tailWord_463013 prefixEnd_463013 140887833054993892271495 := by
  unfold tailWord_463013
  simp only [CollatzResearch.WordTrace]
  refine ⟨16887471471590452169921693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11258314314393634779947795 16887471471590452169921693)
  ·
    refine ⟨6332801801846419563720635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16887471471590452169921693 6332801801846419563720635)
    ·
      refine ⟨9499202702769629345580953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6332801801846419563720635 9499202702769629345580953)
      ·
        refine ⟨7124402027077222009185715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9499202702769629345580953 7124402027077222009185715)
        ·
          refine ⟨10686603040615833013778573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7124402027077222009185715 10686603040615833013778573)
          ·
            refine ⟨4007476140230937380166965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10686603040615833013778573 4007476140230937380166965)
            ·
              refine ⟨375700888146650379390653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4007476140230937380166965 375700888146650379390653)
              ·
                refine ⟨140887833054993892271495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375700888146650379390653 140887833054993892271495)
                ·
                  rfl

theorem cell19_463013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_463013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463013 prefixEnd_463013 := by exact prefixLift 463013
  have htrace : WordTrace (prefixWord ++ tailWord_463013) baseStart_463013 baseEnd_463013 := by
    simpa [prefixWord, tailWord_463013, baseEnd_463013] using wordTrace_append hprefix tailTrace_463013
  have hstable : (prefixWord ++ tailWord_463013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463013).length < 2 ^ (prefixWord ++ tailWord_463013).sum := by decide
  have hdescent : baseEnd_463013 < baseStart_463013 := by decide
  rcases family_descends (prefixWord ++ tailWord_463013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463072 : List Nat := [2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_463072 : Nat := 118140960795 + 463072 * 2 ^ 59
def prefixEnd_463072 : Nat := 4983230072969 + 3 ^ 40 * 463072 * 2
def baseEnd_463072 : Nat := 140905785860099236960223

theorem tailTrace_463072 : CollatzResearch.WordTrace tailWord_463072 prefixEnd_463072 140905785860099236960223 := by
  unfold tailWord_463072
  simp only [CollatzResearch.WordTrace]
  refine ⟨8444811689188352623159735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11259748918917803497546313 8444811689188352623159735)
  ·
    refine ⟨12667217533782528934739603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8444811689188352623159735 12667217533782528934739603)
    ·
      refine ⟨19000826300673793402109405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12667217533782528934739603 19000826300673793402109405)
      ·
        refine ⟨7125309862752672525791027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19000826300673793402109405 7125309862752672525791027)
        ·
          refine ⟨10687964794129008788686541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7125309862752672525791027 10687964794129008788686541)
          ·
            refine ⟨4007986797798378295757453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10687964794129008788686541 4007986797798378295757453)
            ·
              refine ⟨1502995049174391860909045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4007986797798378295757453 1502995049174391860909045)
              ·
                refine ⟨140905785860099236960223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1502995049174391860909045 140905785860099236960223)
                ·
                  rfl

theorem cell19_463072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_463072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463072 prefixEnd_463072 := by exact prefixLift 463072
  have htrace : WordTrace (prefixWord ++ tailWord_463072) baseStart_463072 baseEnd_463072 := by
    simpa [prefixWord, tailWord_463072, baseEnd_463072] using wordTrace_append hprefix tailTrace_463072
  have hstable : (prefixWord ++ tailWord_463072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463072).length < 2 ^ (prefixWord ++ tailWord_463072).sum := by decide
  have hdescent : baseEnd_463072 < baseStart_463072 := by decide
  rcases family_descends (prefixWord ++ tailWord_463072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463106 : List Nat := [3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_463106 : Nat := 118140960795 + 463106 * 2 ^ 59
def prefixEnd_463106 : Nat := 4983230072969 + 3 ^ 40 * 463106 * 2
def baseEnd_463106 : Nat := 140916131544397232204575

theorem tailTrace_463106 : CollatzResearch.WordTrace tailWord_463106 prefixEnd_463106 140916131544397232204575 := by
  unfold tailWord_463106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4222715865063382263264293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11260575640169019368704781 4222715865063382263264293)
  ·
    refine ⟨791759224699384174362055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4222715865063382263264293 791759224699384174362055)
    ·
      refine ⟨1187638837049076261543083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791759224699384174362055 1187638837049076261543083)
      ·
        refine ⟨1781458255573614392314625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187638837049076261543083 1781458255573614392314625)
        ·
          refine ⟨1336093691680210794235969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1781458255573614392314625 1336093691680210794235969)
          ·
            refine ⟨1002070268760158095676977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1336093691680210794235969 1002070268760158095676977)
            ·
              refine ⟨751552701570118571757733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002070268760158095676977 751552701570118571757733)
              ·
                refine ⟨140916131544397232204575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 751552701570118571757733 140916131544397232204575)
                ·
                  rfl

theorem cell19_463106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_463106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463106 prefixEnd_463106 := by exact prefixLift 463106
  have htrace : WordTrace (prefixWord ++ tailWord_463106) baseStart_463106 baseEnd_463106 := by
    simpa [prefixWord, tailWord_463106, baseEnd_463106] using wordTrace_append hprefix tailTrace_463106
  have hstable : (prefixWord ++ tailWord_463106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463106).length < 2 ^ (prefixWord ++ tailWord_463106).sum := by decide
  have hdescent : baseEnd_463106 < baseStart_463106 := by decide
  rcases family_descends (prefixWord ++ tailWord_463106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463146 : List Nat := [3, 1, 4, 2, 2, 7]
def baseStart_463146 : Nat := 118140960795 + 463146 * 2 ^ 59
def prefixEnd_463146 : Nat := 4983230072969 + 3 ^ 40 * 463146 * 2
def baseEnd_463146 : Nat := 15658700326409887923953

theorem tailTrace_463146 : CollatzResearch.WordTrace tailWord_463146 prefixEnd_463146 15658700326409887923953 := by
  unfold tailWord_463146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223080595027153971128323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11261548253405743923008861 4223080595027153971128323)
  ·
    refine ⟨6334620892540730956692485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4223080595027153971128323 6334620892540730956692485)
    ·
      refine ⟨1187741417351387054379841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6334620892540730956692485 1187741417351387054379841)
      ·
        refine ⟨890806063013540290784881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1187741417351387054379841 890806063013540290784881)
        ·
          refine ⟨668104547260155218088661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890806063013540290784881 668104547260155218088661)
          ·
            refine ⟨15658700326409887923953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 668104547260155218088661 15658700326409887923953)
            ·
              rfl

theorem cell19_463146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 7].length) (baseStart_463146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463146 prefixEnd_463146 := by exact prefixLift 463146
  have htrace : WordTrace (prefixWord ++ tailWord_463146) baseStart_463146 baseEnd_463146 := by
    simpa [prefixWord, tailWord_463146, baseEnd_463146] using wordTrace_append hprefix tailTrace_463146
  have hstable : (prefixWord ++ tailWord_463146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463146).length < 2 ^ (prefixWord ++ tailWord_463146).sum := by decide
  have hdescent : baseEnd_463146 < baseStart_463146 := by decide
  rcases family_descends (prefixWord ++ tailWord_463146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463184 : List Nat := [2, 1, 1, 1, 1, 7, 3, 3]
def baseStart_463184 : Nat := 118140960795 + 463184 * 2 ^ 59
def prefixEnd_463184 : Nat := 4983230072969 + 3 ^ 40 * 463184 * 2
def baseEnd_463184 : Nat := 140939865761316162471029

theorem tailTrace_463184 : CollatzResearch.WordTrace tailWord_463184 prefixEnd_463184 140939865761316162471029 := by
  unfold tailWord_463184
  simp only [CollatzResearch.WordTrace]
  refine ⟨8446854176985474187198303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11262472235980632249597737 8446854176985474187198303)
  ·
    refine ⟨12670281265478211280797455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8446854176985474187198303 12670281265478211280797455)
    ·
      refine ⟨19005421898217316921196183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12670281265478211280797455 19005421898217316921196183)
      ·
        refine ⟨28508132847325975381794275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19005421898217316921196183 28508132847325975381794275)
        ·
          refine ⟨42762199270988963072691413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28508132847325975381794275 42762199270988963072691413)
          ·
            refine ⟨1002239045413803822016205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 42762199270988963072691413 1002239045413803822016205)
            ·
              refine ⟨375839642030176433256077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1002239045413803822016205 375839642030176433256077)
              ·
                refine ⟨140939865761316162471029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375839642030176433256077 140939865761316162471029)
                ·
                  rfl

theorem cell19_463184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_463184 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463184 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463184 prefixEnd_463184 := by exact prefixLift 463184
  have htrace : WordTrace (prefixWord ++ tailWord_463184) baseStart_463184 baseEnd_463184 := by
    simpa [prefixWord, tailWord_463184, baseEnd_463184] using wordTrace_append hprefix tailTrace_463184
  have hstable : (prefixWord ++ tailWord_463184).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463184).length < 2 ^ (prefixWord ++ tailWord_463184).sum := by decide
  have hdescent : baseEnd_463184 < baseStart_463184 := by decide
  rcases family_descends (prefixWord ++ tailWord_463184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463186 : List Nat := [3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_463186 : Nat := 118140960795 + 463186 * 2 ^ 59
def prefixEnd_463186 : Nat := 4983230072969 + 3 ^ 40 * 463186 * 2
def baseEnd_463186 : Nat := 140940474330980750426579

theorem tailTrace_463186 : CollatzResearch.WordTrace tailWord_463186 prefixEnd_463186 140940474330980750426579 := by
  unfold tailWord_463186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223445324990925678992353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11262520866642468477312941 4223445324990925678992353)
  ·
    refine ⟨3167583993743194259244265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4223445324990925678992353 3167583993743194259244265)
    ·
      refine ⟨2375687995307395694433199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3167583993743194259244265 2375687995307395694433199)
      ·
        refine ⟨3563531992961093541649799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375687995307395694433199 3563531992961093541649799)
        ·
          refine ⟨5345297989441640312474699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563531992961093541649799 5345297989441640312474699)
          ·
            refine ⟨8017946984162460468712049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345297989441640312474699 8017946984162460468712049)
            ·
              refine ⟨6013460238121845351534037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8017946984162460468712049 6013460238121845351534037)
              ·
                refine ⟨140940474330980750426579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6013460238121845351534037 140940474330980750426579)
                ·
                  rfl

theorem cell19_463186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_463186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463186 prefixEnd_463186 := by exact prefixLift 463186
  have htrace : WordTrace (prefixWord ++ tailWord_463186) baseStart_463186 baseEnd_463186 := by
    simpa [prefixWord, tailWord_463186, baseEnd_463186] using wordTrace_append hprefix tailTrace_463186
  have hstable : (prefixWord ++ tailWord_463186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463186).length < 2 ^ (prefixWord ++ tailWord_463186).sum := by decide
  have hdescent : baseEnd_463186 < baseStart_463186 := by decide
  rcases family_descends (prefixWord ++ tailWord_463186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463205 : List Nat := [1, 3, 1, 3, 1, 4, 6]
def baseStart_463205 : Nat := 118140960795 + 463205 * 2 ^ 59
def prefixEnd_463205 : Nat := 4983230072969 + 3 ^ 40 * 463205 * 2
def baseEnd_463205 : Nat := 46982085247598112001435

theorem tailTrace_463205 : CollatzResearch.WordTrace tailWord_463205 prefixEnd_463205 46982085247598112001435 := by
  unfold tailWord_463205
  simp only [CollatzResearch.WordTrace]
  refine ⟨16894474286894868960911069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11262982857929912640607379 16894474286894868960911069)
  ·
    refine ⟨6335427857585575860341651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16894474286894868960911069 6335427857585575860341651)
    ·
      refine ⟨9503141786378363790512477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6335427857585575860341651 9503141786378363790512477)
      ·
        refine ⟨3563678169891886421442179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9503141786378363790512477 3563678169891886421442179)
        ·
          refine ⟨5345517254837829632163269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563678169891886421442179 5345517254837829632163269)
          ·
            refine ⟨1002284485282093056030613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5345517254837829632163269 1002284485282093056030613)
            ·
              refine ⟨46982085247598112001435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1002284485282093056030613 46982085247598112001435)
              ·
                rfl

theorem cell19_463205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_463205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463205 prefixEnd_463205 := by exact prefixLift 463205
  have htrace : WordTrace (prefixWord ++ tailWord_463205) baseStart_463205 baseEnd_463205 := by
    simpa [prefixWord, tailWord_463205, baseEnd_463205] using wordTrace_append hprefix tailTrace_463205
  have hstable : (prefixWord ++ tailWord_463205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463205).length < 2 ^ (prefixWord ++ tailWord_463205).sum := by decide
  have hdescent : baseEnd_463205 < baseStart_463205 := by decide
  rcases family_descends (prefixWord ++ tailWord_463205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463241 : List Nat := [1, 2, 1, 1, 6, 1, 4, 3]
def baseStart_463241 : Nat := 118140960795 + 463241 * 2 ^ 59
def prefixEnd_463241 : Nat := 4983230072969 + 3 ^ 40 * 463241 * 2
def baseEnd_463241 : Nat := 140957209996756919204207

theorem tailTrace_463241 : CollatzResearch.WordTrace tailWord_463241 prefixEnd_463241 140957209996756919204207 := by
  unfold tailWord_463241
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895787314764447109221577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11263858209842964739481051 16895787314764447109221577)
  ·
    refine ⟨12671840486073335331916183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16895787314764447109221577 12671840486073335331916183)
    ·
      refine ⟨19007760729110002997874275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12671840486073335331916183 19007760729110002997874275)
      ·
        refine ⟨28511641093665004496811413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19007760729110002997874275 28511641093665004496811413)
        ·
          refine ⟨1336483176265547085788035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28511641093665004496811413 1336483176265547085788035)
          ·
            refine ⟨2004724764398320628682053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336483176265547085788035 2004724764398320628682053)
            ·
              refine ⟨375885893324685117877885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2004724764398320628682053 375885893324685117877885)
              ·
                refine ⟨140957209996756919204207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375885893324685117877885 140957209996756919204207)
                ·
                  rfl

theorem cell19_463241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_463241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463241 prefixEnd_463241 := by exact prefixLift 463241
  have htrace : WordTrace (prefixWord ++ tailWord_463241) baseStart_463241 baseEnd_463241 := by
    simpa [prefixWord, tailWord_463241, baseEnd_463241] using wordTrace_append hprefix tailTrace_463241
  have hstable : (prefixWord ++ tailWord_463241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463241).length < 2 ^ (prefixWord ++ tailWord_463241).sum := by decide
  have hdescent : baseEnd_463241 < baseStart_463241 := by decide
  rcases family_descends (prefixWord ++ tailWord_463241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463243 : List Nat := [1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_463243 : Nat := 118140960795 + 463243 * 2 ^ 59
def prefixEnd_463243 : Nat := 4983230072969 + 3 ^ 40 * 463243 * 2
def baseEnd_463243 : Nat := 140957818566421507159757

theorem tailTrace_463243 : CollatzResearch.WordTrace tailWord_463243 prefixEnd_463243 140957818566421507159757 := by
  unfold tailWord_463243
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895860260757201450794383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11263906840504800967196255 16895860260757201450794383)
  ·
    refine ⟨25343790391135802176191575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16895860260757201450794383 25343790391135802176191575)
    ·
      refine ⟨38015685586703703264287363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25343790391135802176191575 38015685586703703264287363)
      ·
        refine ⟨57023528380055554896431045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38015685586703703264287363 57023528380055554896431045)
        ·
          refine ⟨10691911571260416543080821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57023528380055554896431045 10691911571260416543080821)
          ·
            refine ⟨1002366709805664050913827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10691911571260416543080821 1002366709805664050913827)
            ·
              refine ⟨1503550064708496076370741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002366709805664050913827 1503550064708496076370741)
              ·
                refine ⟨140957818566421507159757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1503550064708496076370741 140957818566421507159757)
                ·
                  rfl

theorem cell19_463243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_463243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463243 prefixEnd_463243 := by exact prefixLift 463243
  have htrace : WordTrace (prefixWord ++ tailWord_463243) baseStart_463243 baseEnd_463243 := by
    simpa [prefixWord, tailWord_463243, baseEnd_463243] using wordTrace_append hprefix tailTrace_463243
  have hstable : (prefixWord ++ tailWord_463243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463243).length < 2 ^ (prefixWord ++ tailWord_463243).sum := by decide
  have hdescent : baseEnd_463243 < baseStart_463243 := by decide
  rcases family_descends (prefixWord ++ tailWord_463243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463254 : List Nat := [5, 3, 1, 2, 1, 2, 5]
def baseStart_463254 : Nat := 118140960795 + 463254 * 2 ^ 59
def prefixEnd_463254 : Nat := 4983230072969 + 3 ^ 40 * 463254 * 2
def baseEnd_463254 : Nat := 46987055233192246971761

theorem tailTrace_463254 : CollatzResearch.WordTrace tailWord_463254 prefixEnd_463254 46987055233192246971761 := by
  unfold tailWord_463254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1056016341482334395590301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11264174309144900219629877 1056016341482334395590301)
  ·
    refine ⟨396006128055875398346363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1056016341482334395590301 396006128055875398346363)
    ·
      refine ⟨594009192083813097519545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396006128055875398346363 594009192083813097519545)
      ·
        refine ⟨445506894062859823139659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594009192083813097519545 445506894062859823139659)
        ·
          refine ⟨668260341094289734709489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445506894062859823139659 668260341094289734709489)
          ·
            refine ⟨501195255820717301032117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668260341094289734709489 501195255820717301032117)
            ·
              refine ⟨46987055233192246971761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 501195255820717301032117 46987055233192246971761)
              ·
                rfl

theorem cell19_463254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_463254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463254 prefixEnd_463254 := by exact prefixLift 463254
  have htrace : WordTrace (prefixWord ++ tailWord_463254) baseStart_463254 baseEnd_463254 := by
    simpa [prefixWord, tailWord_463254, baseEnd_463254] using wordTrace_append hprefix tailTrace_463254
  have hstable : (prefixWord ++ tailWord_463254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463254).length < 2 ^ (prefixWord ++ tailWord_463254).sum := by decide
  have hdescent : baseEnd_463254 < baseStart_463254 := by decide
  rcases family_descends (prefixWord ++ tailWord_463254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463277 : List Nat := [1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_463277 : Nat := 118140960795 + 463277 * 2 ^ 59
def prefixEnd_463277 : Nat := 4983230072969 + 3 ^ 40 * 463277 * 2
def baseEnd_463277 : Nat := 140968164250719502404109

theorem tailTrace_463277 : CollatzResearch.WordTrace tailWord_463277 prefixEnd_463277 140968164250719502404109 := by
  unfold tailWord_463277
  simp only [CollatzResearch.WordTrace]
  refine ⟨16897100342634025257532085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11264733561756016838354723 16897100342634025257532085)
  ·
    refine ⟨1584103157121939867893633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16897100342634025257532085 1584103157121939867893633)
    ·
      refine ⟨1188077367841454900920225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1584103157121939867893633 1188077367841454900920225)
      ·
        refine ⟨891058025881091175690169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1188077367841454900920225 891058025881091175690169)
        ·
          refine ⟨668293519410818381767627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 891058025881091175690169 668293519410818381767627)
          ·
            refine ⟨1002440279116227572651441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668293519410818381767627 1002440279116227572651441)
            ·
              refine ⟨751830209337170679488581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002440279116227572651441 751830209337170679488581)
              ·
                refine ⟨140968164250719502404109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 751830209337170679488581 140968164250719502404109)
                ·
                  rfl

theorem cell19_463277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_463277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463277 prefixEnd_463277 := by exact prefixLift 463277
  have htrace : WordTrace (prefixWord ++ tailWord_463277) baseStart_463277 baseEnd_463277 := by
    simpa [prefixWord, tailWord_463277, baseEnd_463277] using wordTrace_append hprefix tailTrace_463277
  have hstable : (prefixWord ++ tailWord_463277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463277).length < 2 ^ (prefixWord ++ tailWord_463277).sum := by decide
  have hdescent : baseEnd_463277 < baseStart_463277 := by decide
  rcases family_descends (prefixWord ++ tailWord_463277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463281 : List Nat := [1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_463281 : Nat := 118140960795 + 463281 * 2 ^ 59
def prefixEnd_463281 : Nat := 4983230072969 + 3 ^ 40 * 463281 * 2
def baseEnd_463281 : Nat := 140969381390048678315209

theorem tailTrace_463281 : CollatzResearch.WordTrace tailWord_463281 prefixEnd_463281 140969381390048678315209 := by
  unfold tailWord_463281
  simp only [CollatzResearch.WordTrace]
  refine ⟨16897246234619533940677697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11264830823079689293785131 16897246234619533940677697)
  ·
    refine ⟨12672934675964650455508273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16897246234619533940677697 12672934675964650455508273)
    ·
      refine ⟨9504701006973487841631205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12672934675964650455508273 9504701006973487841631205)
      ·
        refine ⟨1782131438807528970305851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9504701006973487841631205 1782131438807528970305851)
        ·
          refine ⟨2673197158211293455458777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782131438807528970305851 2673197158211293455458777)
          ·
            refine ⟨2004897868658470091594083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2673197158211293455458777 2004897868658470091594083)
            ·
              refine ⟨3007346802987705137391125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004897868658470091594083 3007346802987705137391125)
              ·
                refine ⟨140969381390048678315209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3007346802987705137391125 140969381390048678315209)
                ·
                  rfl

theorem cell19_463281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_463281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463281 prefixEnd_463281 := by exact prefixLift 463281
  have htrace : WordTrace (prefixWord ++ tailWord_463281) baseStart_463281 baseEnd_463281 := by
    simpa [prefixWord, tailWord_463281, baseEnd_463281] using wordTrace_append hprefix tailTrace_463281
  have hstable : (prefixWord ++ tailWord_463281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463281).length < 2 ^ (prefixWord ++ tailWord_463281).sum := by decide
  have hdescent : baseEnd_463281 < baseStart_463281 := by decide
  rcases family_descends (prefixWord ++ tailWord_463281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463330 : List Nat := [3, 3, 3, 2, 2, 1, 1, 4]
def baseStart_463330 : Nat := 118140960795 + 463330 * 2 ^ 59
def prefixEnd_463330 : Nat := 4983230072969 + 3 ^ 40 * 463330 * 2
def baseEnd_463330 : Nat := 140984291346831083226187

theorem tailTrace_463330 : CollatzResearch.WordTrace tailWord_463330 prefixEnd_463330 140984291346831083226187 := by
  unfold tailWord_463330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4224758352860503827302861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11266022274294676872807629 4224758352860503827302861)
  ·
    refine ⟨1584284382322688935238573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4224758352860503827302861 1584284382322688935238573)
    ·
      refine ⟨594106643371008350714465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1584284382322688935238573 594106643371008350714465)
      ·
        refine ⟨445579982528256263035849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594106643371008350714465 445579982528256263035849)
        ·
          refine ⟨334184986896192197276887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445579982528256263035849 334184986896192197276887)
          ·
            refine ⟨501277480344288295915331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334184986896192197276887 501277480344288295915331)
            ·
              refine ⟨751916220516432443872997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501277480344288295915331 751916220516432443872997)
              ·
                refine ⟨140984291346831083226187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 751916220516432443872997 140984291346831083226187)
                ·
                  rfl

theorem cell19_463330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_463330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463330 prefixEnd_463330 := by exact prefixLift 463330
  have htrace : WordTrace (prefixWord ++ tailWord_463330) baseStart_463330 baseEnd_463330 := by
    simpa [prefixWord, tailWord_463330, baseEnd_463330] using wordTrace_append hprefix tailTrace_463330
  have hstable : (prefixWord ++ tailWord_463330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463330).length < 2 ^ (prefixWord ++ tailWord_463330).sum := by decide
  have hdescent : baseEnd_463330 < baseStart_463330 := by decide
  rcases family_descends (prefixWord ++ tailWord_463330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463336 : List Nat := [2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_463336 : Nat := 118140960795 + 463336 * 2 ^ 59
def prefixEnd_463336 : Nat := 4983230072969 + 3 ^ 40 * 463336 * 2
def baseEnd_463336 : Nat := 140986117055824847092837

theorem tailTrace_463336 : CollatzResearch.WordTrace tailWord_463336 prefixEnd_463336 140986117055824847092837 := by
  unfold tailWord_463336
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449626124710139166964931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11266168166280185555953241 8449626124710139166964931)
  ·
    refine ⟨12674439187065208750447397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8449626124710139166964931 12674439187065208750447397)
    ·
      refine ⟨2376457347574726640708887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12674439187065208750447397 2376457347574726640708887)
      ·
        refine ⟨3564686021362089961063331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376457347574726640708887 3564686021362089961063331)
        ·
          refine ⟨5347029032043134941594997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564686021362089961063331 5347029032043134941594997)
          ·
            refine ⟨501283971754043900774531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5347029032043134941594997 501283971754043900774531)
            ·
              refine ⟨751925957631065851161797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501283971754043900774531 751925957631065851161797)
              ·
                refine ⟨140986117055824847092837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 751925957631065851161797 140986117055824847092837)
                ·
                  rfl

theorem cell19_463336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_463336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463336 prefixEnd_463336 := by exact prefixLift 463336
  have htrace : WordTrace (prefixWord ++ tailWord_463336) baseStart_463336 baseEnd_463336 := by
    simpa [prefixWord, tailWord_463336, baseEnd_463336] using wordTrace_append hprefix tailTrace_463336
  have hstable : (prefixWord ++ tailWord_463336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463336).length < 2 ^ (prefixWord ++ tailWord_463336).sum := by decide
  have hdescent : baseEnd_463336 < baseStart_463336 := by decide
  rcases family_descends (prefixWord ++ tailWord_463336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463435 : List Nat := [1, 1, 1, 1, 3, 1, 11]
def baseStart_463435 : Nat := 118140960795 + 463435 * 2 ^ 59
def prefixEnd_463435 : Nat := 4983230072969 + 3 ^ 40 * 463435 * 2
def baseEnd_463435 : Nat := 47005413751407316964189

theorem tailTrace_463435 : CollatzResearch.WordTrace tailWord_463435 prefixEnd_463435 47005413751407316964189 := by
  unfold tailWord_463435
  simp only [CollatzResearch.WordTrace]
  refine ⟨16902863076061618241783759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11268575384041078827855839 16902863076061618241783759)
  ·
    refine ⟨25354294614092427362675639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16902863076061618241783759 25354294614092427362675639)
    ·
      refine ⟨38031441921138641044013459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25354294614092427362675639 38031441921138641044013459)
      ·
        refine ⟨57047162881707961566020189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38031441921138641044013459 57047162881707961566020189)
        ·
          refine ⟨21392686080640485587257571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57047162881707961566020189 21392686080640485587257571)
          ·
            refine ⟨32089029120960728380886357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21392686080640485587257571 32089029120960728380886357)
            ·
              refine ⟨47005413751407316964189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32089029120960728380886357 47005413751407316964189)
              ·
                rfl

theorem cell19_463435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_463435 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463435 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463435 prefixEnd_463435 := by exact prefixLift 463435
  have htrace : WordTrace (prefixWord ++ tailWord_463435) baseStart_463435 baseEnd_463435 := by
    simpa [prefixWord, tailWord_463435, baseEnd_463435] using wordTrace_append hprefix tailTrace_463435
  have hstable : (prefixWord ++ tailWord_463435).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463435).length < 2 ^ (prefixWord ++ tailWord_463435).sum := by decide
  have hdescent : baseEnd_463435 < baseStart_463435 := by decide
  rcases family_descends (prefixWord ++ tailWord_463435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463583 : List Nat := [1, 1, 2, 3, 2, 5, 2, 3]
def baseStart_463583 : Nat := 118140960795 + 463583 * 2 ^ 59
def prefixEnd_463583 : Nat := 4983230072969 + 3 ^ 40 * 463583 * 2
def baseEnd_463583 : Nat := 141061275409401459603275

theorem tailTrace_463583 : CollatzResearch.WordTrace tailWord_463583 prefixEnd_463583 141061275409401459603275 := by
  unfold tailWord_463583
  simp only [CollatzResearch.WordTrace]
  refine ⟨16908261079525439518171403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11272174053016959678780935 16908261079525439518171403)
  ·
    refine ⟨25362391619288159277257105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16908261079525439518171403 25362391619288159277257105)
    ·
      refine ⟨19021793714466119457942829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25362391619288159277257105 19021793714466119457942829)
      ·
        refine ⟨7133172642924794796728561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19021793714466119457942829 7133172642924794796728561)
        ·
          refine ⟨5349879482193596097546421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7133172642924794796728561 5349879482193596097546421)
          ·
            refine ⟨501551201455649634144977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5349879482193596097546421 501551201455649634144977)
            ·
              refine ⟨376163401091737225608733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501551201455649634144977 376163401091737225608733)
              ·
                refine ⟨141061275409401459603275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376163401091737225608733 141061275409401459603275)
                ·
                  rfl

theorem cell19_463583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_463583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463583 prefixEnd_463583 := by exact prefixLift 463583
  have htrace : WordTrace (prefixWord ++ tailWord_463583) baseStart_463583 baseEnd_463583 := by
    simpa [prefixWord, tailWord_463583, baseEnd_463583] using wordTrace_append hprefix tailTrace_463583
  have hstable : (prefixWord ++ tailWord_463583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463583).length < 2 ^ (prefixWord ++ tailWord_463583).sum := by decide
  have hdescent : baseEnd_463583 < baseStart_463583 := by decide
  rcases family_descends (prefixWord ++ tailWord_463583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463585 : List Nat := [1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_463585 : Nat := 118140960795 + 463585 * 2 ^ 59
def prefixEnd_463585 : Nat := 4983230072969 + 3 ^ 40 * 463585 * 2
def baseEnd_463585 : Nat := 141061883979066047558825

theorem tailTrace_463585 : CollatzResearch.WordTrace tailWord_463585 prefixEnd_463585 141061883979066047558825 := by
  unfold tailWord_463585
  simp only [CollatzResearch.WordTrace]
  refine ⟨16908334025518193859744209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11272222683678795906496139 16908334025518193859744209)
  ·
    refine ⟨12681250519138645394808157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16908334025518193859744209 12681250519138645394808157)
    ·
      refine ⟨4755468944676992023053059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12681250519138645394808157 4755468944676992023053059)
      ·
        refine ⟨7133203417015488034579589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4755468944676992023053059 7133203417015488034579589)
        ·
          refine ⟨1337475640690404006483673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7133203417015488034579589 1337475640690404006483673)
          ·
            refine ⟨1003106730517803004862755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1337475640690404006483673 1003106730517803004862755)
            ·
              refine ⟨1504660095776704507294133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003106730517803004862755 1504660095776704507294133)
              ·
                refine ⟨141061883979066047558825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1504660095776704507294133 141061883979066047558825)
                ·
                  rfl

theorem cell19_463585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_463585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463585 prefixEnd_463585 := by exact prefixLift 463585
  have htrace : WordTrace (prefixWord ++ tailWord_463585) baseStart_463585 baseEnd_463585 := by
    simpa [prefixWord, tailWord_463585, baseEnd_463585] using wordTrace_append hprefix tailTrace_463585
  have hstable : (prefixWord ++ tailWord_463585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463585).length < 2 ^ (prefixWord ++ tailWord_463585).sum := by decide
  have hdescent : baseEnd_463585 < baseStart_463585 := by decide
  rcases family_descends (prefixWord ++ tailWord_463585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463623 : List Nat := [1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_463623 : Nat := 118140960795 + 463623 * 2 ^ 59
def prefixEnd_463623 : Nat := 4983230072969 + 3 ^ 40 * 463623 * 2
def baseEnd_463623 : Nat := 141073446802693218714277

theorem tailTrace_463623 : CollatzResearch.WordTrace tailWord_463623 prefixEnd_463623 141073446802693218714277 := by
  unfold tailWord_463623
  simp only [CollatzResearch.WordTrace]
  refine ⟨16909719999380526349627523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11273146666253684233085015 16909719999380526349627523)
  ·
    refine ⟨25364579999070789524441285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16909719999380526349627523 25364579999070789524441285)
    ·
      refine ⟨4755858749825773035832741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25364579999070789524441285 4755858749825773035832741)
      ·
        refine ⟨891723515592332444218639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4755858749825773035832741 891723515592332444218639)
        ·
          refine ⟨1337585273388498666327959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891723515592332444218639 1337585273388498666327959)
          ·
            refine ⟨2006377910082747999491939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337585273388498666327959 2006377910082747999491939)
            ·
              refine ⟨3009566865124121999237909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006377910082747999491939 3009566865124121999237909)
              ·
                refine ⟨141073446802693218714277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3009566865124121999237909 141073446802693218714277)
                ·
                  rfl

theorem cell19_463623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_463623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463623 prefixEnd_463623 := by exact prefixLift 463623
  have htrace : WordTrace (prefixWord ++ tailWord_463623) baseStart_463623 baseEnd_463623 := by
    simpa [prefixWord, tailWord_463623, baseEnd_463623] using wordTrace_append hprefix tailTrace_463623
  have hstable : (prefixWord ++ tailWord_463623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463623).length < 2 ^ (prefixWord ++ tailWord_463623).sum := by decide
  have hdescent : baseEnd_463623 < baseStart_463623 := by decide
  rcases family_descends (prefixWord ++ tailWord_463623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463625 : List Nat := [1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_463625 : Nat := 118140960795 + 463625 * 2 ^ 59
def prefixEnd_463625 : Nat := 4983230072969 + 3 ^ 40 * 463625 * 2
def baseEnd_463625 : Nat := 141074055372357806669827

theorem tailTrace_463625 : CollatzResearch.WordTrace tailWord_463625 prefixEnd_463625 141074055372357806669827 := by
  unfold tailWord_463625
  simp only [CollatzResearch.WordTrace]
  refine ⟨16909792945373280691200329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11273195296915520460800219 16909792945373280691200329)
  ·
    refine ⟨12682344709029960518400247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16909792945373280691200329 12682344709029960518400247)
    ·
      refine ⟨19023517063544940777600371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12682344709029960518400247 19023517063544940777600371)
      ·
        refine ⟨28535275595317411166400557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19023517063544940777600371 28535275595317411166400557)
        ·
          refine ⟨10700728348244029187400209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28535275595317411166400557 10700728348244029187400209)
          ·
            refine ⟨8025546261183021890550157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10700728348244029187400209 8025546261183021890550157)
            ·
              refine ⟨3009579847943633208956309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8025546261183021890550157 3009579847943633208956309)
              ·
                refine ⟨141074055372357806669827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3009579847943633208956309 141074055372357806669827)
                ·
                  rfl

theorem cell19_463625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_463625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463625 prefixEnd_463625 := by exact prefixLift 463625
  have htrace : WordTrace (prefixWord ++ tailWord_463625) baseStart_463625 baseEnd_463625 := by
    simpa [prefixWord, tailWord_463625, baseEnd_463625] using wordTrace_append hprefix tailTrace_463625
  have hstable : (prefixWord ++ tailWord_463625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463625).length < 2 ^ (prefixWord ++ tailWord_463625).sum := by decide
  have hdescent : baseEnd_463625 < baseStart_463625 := by decide
  rcases family_descends (prefixWord ++ tailWord_463625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463697 : List Nat := [1, 2, 2, 1, 6, 1, 3, 3]
def baseStart_463697 : Nat := 118140960795 + 463697 * 2 ^ 59
def prefixEnd_463697 : Nat := 4983230072969 + 3 ^ 40 * 463697 * 2
def baseEnd_463697 : Nat := 141095963880282973069631

theorem tailTrace_463697 : CollatzResearch.WordTrace tailWord_463697 prefixEnd_463697 141095963880282973069631 := by
  unfold tailWord_463697
  simp only [CollatzResearch.WordTrace]
  refine ⟨16912419001112436987821345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11274946000741624658547563 16912419001112436987821345)
  ·
    refine ⟨12684314250834327740866009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16912419001112436987821345 12684314250834327740866009)
    ·
      refine ⟨9513235688125745805649507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12684314250834327740866009 9513235688125745805649507)
      ·
        refine ⟨14269853532188618708474261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9513235688125745805649507 14269853532188618708474261)
        ·
          refine ⟨668899384321341501959731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14269853532188618708474261 668899384321341501959731)
          ·
            refine ⟨1003349076482012252939597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668899384321341501959731 1003349076482012252939597)
            ·
              refine ⟨376255903680754594852349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1003349076482012252939597 376255903680754594852349)
              ·
                refine ⟨141095963880282973069631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376255903680754594852349 141095963880282973069631)
                ·
                  rfl

theorem cell19_463697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_463697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463697 prefixEnd_463697 := by exact prefixLift 463697
  have htrace : WordTrace (prefixWord ++ tailWord_463697) baseStart_463697 baseEnd_463697 := by
    simpa [prefixWord, tailWord_463697, baseEnd_463697] using wordTrace_append hprefix tailTrace_463697
  have hstable : (prefixWord ++ tailWord_463697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463697).length < 2 ^ (prefixWord ++ tailWord_463697).sum := by decide
  have hdescent : baseEnd_463697 < baseStart_463697 := by decide
  rcases family_descends (prefixWord ++ tailWord_463697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463754 : List Nat := [3, 1, 2, 4, 1, 1, 4, 3]
def baseStart_463754 : Nat := 118140960795 + 463754 * 2 ^ 59
def prefixEnd_463754 : Nat := 4983230072969 + 3 ^ 40 * 463754 * 2
def baseEnd_463754 : Nat := 141113308115723729802809

theorem tailTrace_463754 : CollatzResearch.WordTrace tailWord_463754 prefixEnd_463754 141113308115723729802809 := by
  unfold tailWord_463754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228624490476483930661579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11276331974603957148430877 4228624490476483930661579)
  ·
    refine ⟨6342936735714725895992369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4228624490476483930661579 6342936735714725895992369)
    ·
      refine ⟨4757202551786044421994277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6342936735714725895992369 4757202551786044421994277)
      ·
        refine ⟨891975478459883329123927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4757202551786044421994277 891975478459883329123927)
        ·
          refine ⟨1337963217689824993685891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891975478459883329123927 1337963217689824993685891)
          ·
            refine ⟨2006944826534737490528837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337963217689824993685891 2006944826534737490528837)
            ·
              refine ⟨376302154975263279474157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2006944826534737490528837 376302154975263279474157)
              ·
                refine ⟨141113308115723729802809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376302154975263279474157 141113308115723729802809)
                ·
                  rfl

theorem cell19_463754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_463754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463754 prefixEnd_463754 := by exact prefixLift 463754
  have htrace : WordTrace (prefixWord ++ tailWord_463754) baseStart_463754 baseEnd_463754 := by
    simpa [prefixWord, tailWord_463754, baseEnd_463754] using wordTrace_append hprefix tailTrace_463754
  have hstable : (prefixWord ++ tailWord_463754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463754).length < 2 ^ (prefixWord ++ tailWord_463754).sum := by decide
  have hdescent : baseEnd_463754 < baseStart_463754 := by decide
  rcases family_descends (prefixWord ++ tailWord_463754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463756 : List Nat := [2, 2, 1, 2, 1, 2, 6, 3]
def baseStart_463756 : Nat := 118140960795 + 463756 * 2 ^ 59
def prefixEnd_463756 : Nat := 4983230072969 + 3 ^ 40 * 463756 * 2
def baseEnd_463756 : Nat := 141113916685388317758359

theorem tailTrace_463756 : CollatzResearch.WordTrace tailWord_463756 prefixEnd_463756 141113916685388317758359 := by
  unfold tailWord_463756
  simp only [CollatzResearch.WordTrace]
  refine ⟨8457285453949345032109561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11276380605265793376146081 8457285453949345032109561)
  ·
    refine ⟨6342964090462008774082171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8457285453949345032109561 6342964090462008774082171)
    ·
      refine ⟨9514446135693013161123257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6342964090462008774082171 9514446135693013161123257)
      ·
        refine ⟨7135834601769759870842443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9514446135693013161123257 7135834601769759870842443)
        ·
          refine ⟨10703751902654639806263665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135834601769759870842443 10703751902654639806263665)
          ·
            refine ⟨8027813926990979854697749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10703751902654639806263665 8027813926990979854697749)
            ·
              refine ⟨376303777827702180688957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8027813926990979854697749 376303777827702180688957)
              ·
                refine ⟨141113916685388317758359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376303777827702180688957 141113916685388317758359)
                ·
                  rfl

theorem cell19_463756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_463756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463756 prefixEnd_463756 := by exact prefixLift 463756
  have htrace : WordTrace (prefixWord ++ tailWord_463756) baseStart_463756 baseEnd_463756 := by
    simpa [prefixWord, tailWord_463756, baseEnd_463756] using wordTrace_append hprefix tailTrace_463756
  have hstable : (prefixWord ++ tailWord_463756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463756).length < 2 ^ (prefixWord ++ tailWord_463756).sum := by decide
  have hdescent : baseEnd_463756 < baseStart_463756 := by decide
  rcases family_descends (prefixWord ++ tailWord_463756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463775 : List Nat := [1, 1, 2, 5, 2, 3, 5]
def baseStart_463775 : Nat := 118140960795 + 463775 * 2 ^ 59
def prefixEnd_463775 : Nat := 4983230072969 + 3 ^ 40 * 463775 * 2
def baseEnd_463775 : Nat := 47039899365733967778695

theorem tailTrace_463775 : CollatzResearch.WordTrace tailWord_463775 prefixEnd_463775 47039899365733967778695 := by
  unfold tailWord_463775
  simp only [CollatzResearch.WordTrace]
  refine ⟨16915263894829856309160779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11276842596553237539440519 16915263894829856309160779)
  ·
    refine ⟨25372895842244784463741169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16915263894829856309160779 25372895842244784463741169)
    ·
      refine ⟨19029671881683588347805877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25372895842244784463741169 19029671881683588347805877)
      ·
        refine ⟨1784031738907836407606801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19029671881683588347805877 1784031738907836407606801)
        ·
          refine ⟨1338023804180877305705101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1784031738907836407606801 1338023804180877305705101)
          ·
            refine ⟨501758926567828989639413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1338023804180877305705101 501758926567828989639413)
            ·
              refine ⟨47039899365733967778695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 501758926567828989639413 47039899365733967778695)
              ·
                rfl

theorem cell19_463775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_463775 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463775 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463775 prefixEnd_463775 := by exact prefixLift 463775
  have htrace : WordTrace (prefixWord ++ tailWord_463775) baseStart_463775 baseEnd_463775 := by
    simpa [prefixWord, tailWord_463775, baseEnd_463775] using wordTrace_append hprefix tailTrace_463775
  have hstable : (prefixWord ++ tailWord_463775).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463775).length < 2 ^ (prefixWord ++ tailWord_463775).sum := by decide
  have hdescent : baseEnd_463775 < baseStart_463775 := by decide
  rcases family_descends (prefixWord ++ tailWord_463775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463815 : List Nat := [1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_463815 : Nat := 118140960795 + 463815 * 2 ^ 59
def prefixEnd_463815 : Nat := 4983230072969 + 3 ^ 40 * 463815 * 2
def baseEnd_463815 : Nat := 141131869490493662447087

theorem tailTrace_463815 : CollatzResearch.WordTrace tailWord_463815 prefixEnd_463815 141131869490493662447087 := by
  unfold tailWord_463815
  simp only [CollatzResearch.WordTrace]
  refine ⟨16916722814684943140616899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11277815209789962093744599 16916722814684943140616899)
  ·
    refine ⟨25375084222027414710925349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16916722814684943140616899 25375084222027414710925349)
    ·
      refine ⟨4757828291630140258298503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25375084222027414710925349 4757828291630140258298503)
      ·
        refine ⟨7136742437445210387447755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757828291630140258298503 7136742437445210387447755)
        ·
          refine ⟨10705113656167815581171633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7136742437445210387447755 10705113656167815581171633)
          ·
            refine ⟨8028835242125861685878725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10705113656167815581171633 8028835242125861685878725)
            ·
              refine ⟨1505406607898599066102261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8028835242125861685878725 1505406607898599066102261)
              ·
                refine ⟨141131869490493662447087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1505406607898599066102261 141131869490493662447087)
                ·
                  rfl

theorem cell19_463815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_463815 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463815 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463815 prefixEnd_463815 := by exact prefixLift 463815
  have htrace : WordTrace (prefixWord ++ tailWord_463815) baseStart_463815 baseEnd_463815 := by
    simpa [prefixWord, tailWord_463815, baseEnd_463815] using wordTrace_append hprefix tailTrace_463815
  have hstable : (prefixWord ++ tailWord_463815).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463815).length < 2 ^ (prefixWord ++ tailWord_463815).sum := by decide
  have hdescent : baseEnd_463815 < baseStart_463815 := by decide
  rcases family_descends (prefixWord ++ tailWord_463815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463834 : List Nat := [3, 1, 1, 2, 4, 8]
def baseStart_463834 : Nat := 118140960795 + 463834 * 2 ^ 59
def prefixEnd_463834 : Nat := 4983230072969 + 3 ^ 40 * 463834 * 2
def baseEnd_463834 : Nat := 15681961211367472002757

theorem tailTrace_463834 : CollatzResearch.WordTrace tailWord_463834 prefixEnd_463834 15681961211367472002757 := by
  unfold tailWord_463834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229353950404027346389639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11278277201077406257039037 4229353950404027346389639)
  ·
    refine ⟨6344030925606041019584459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4229353950404027346389639 6344030925606041019584459)
    ·
      refine ⟨9516046388409061529376689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6344030925606041019584459 9516046388409061529376689)
      ·
        refine ⟨7137034791306796147032517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9516046388409061529376689 7137034791306796147032517)
        ·
          refine ⟨1338194023370024277568597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7137034791306796147032517 1338194023370024277568597)
          ·
            refine ⟨15681961211367472002757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1338194023370024277568597 15681961211367472002757)
            ·
              rfl

theorem cell19_463834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 8].length) (baseStart_463834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463834 prefixEnd_463834 := by exact prefixLift 463834
  have htrace : WordTrace (prefixWord ++ tailWord_463834) baseStart_463834 baseEnd_463834 := by
    simpa [prefixWord, tailWord_463834, baseEnd_463834] using wordTrace_append hprefix tailTrace_463834
  have hstable : (prefixWord ++ tailWord_463834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463834).length < 2 ^ (prefixWord ++ tailWord_463834).sum := by decide
  have hdescent : baseEnd_463834 < baseStart_463834 := by decide
  rcases family_descends (prefixWord ++ tailWord_463834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463967 : List Nat := [1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_463967 : Nat := 118140960795 + 463967 * 2 ^ 59
def prefixEnd_463967 : Nat := 4983230072969 + 3 ^ 40 * 463967 * 2
def baseEnd_463967 : Nat := 141178120785002347068895

theorem tailTrace_463967 : CollatzResearch.WordTrace tailWord_463967 prefixEnd_463967 141178120785002347068895 := by
  unfold tailWord_463967
  simp only [CollatzResearch.WordTrace]
  refine ⟨16922266710134273100150155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11281511140089515400100103 16922266710134273100150155)
  ·
    refine ⟨25383400065201409650225233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16922266710134273100150155 25383400065201409650225233)
    ·
      refine ⟨19037550048901057237668925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25383400065201409650225233 19037550048901057237668925)
      ·
        refine ⟨7139081268337896464125847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19037550048901057237668925 7139081268337896464125847)
        ·
          refine ⟨10708621902506844696188771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139081268337896464125847 10708621902506844696188771)
          ·
            refine ⟨16062932853760267044283157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10708621902506844696188771 16062932853760267044283157)
            ·
              refine ⟨752949977520012517700773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16062932853760267044283157 752949977520012517700773)
              ·
                refine ⟨141178120785002347068895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 752949977520012517700773 141178120785002347068895)
                ·
                  rfl

theorem cell19_463967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_463967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463967 prefixEnd_463967 := by exact prefixLift 463967
  have htrace : WordTrace (prefixWord ++ tailWord_463967) baseStart_463967 baseEnd_463967 := by
    simpa [prefixWord, tailWord_463967, baseEnd_463967] using wordTrace_append hprefix tailTrace_463967
  have hstable : (prefixWord ++ tailWord_463967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463967).length < 2 ^ (prefixWord ++ tailWord_463967).sum := by decide
  have hdescent : baseEnd_463967 < baseStart_463967 := by decide
  rcases family_descends (prefixWord ++ tailWord_463967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_463986 : List Nat := [3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_463986 : Nat := 118140960795 + 463986 * 2 ^ 59
def prefixEnd_463986 : Nat := 4983230072969 + 3 ^ 40 * 463986 * 2
def baseEnd_463986 : Nat := 141183902196815932646621

theorem tailTrace_463986 : CollatzResearch.WordTrace tailWord_463986 prefixEnd_463986 141183902196815932646621 := by
  unfold tailWord_463986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230739924266359836272953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11281973131376959563394541 4230739924266359836272953)
  ·
    refine ⟨3173054943199769877204715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4230739924266359836272953 3173054943199769877204715)
    ·
      refine ⟨4759582414799654815807073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3173054943199769877204715 4759582414799654815807073)
      ·
        refine ⟨3569686811099741111855305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4759582414799654815807073 3569686811099741111855305)
        ·
          refine ⟨2677265108324805833891479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3569686811099741111855305 2677265108324805833891479)
          ·
            refine ⟨4015897662487208750837219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677265108324805833891479 4015897662487208750837219)
            ·
              refine ⟨6023846493730813126255829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015897662487208750837219 6023846493730813126255829)
              ·
                refine ⟨141183902196815932646621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6023846493730813126255829 141183902196815932646621)
                ·
                  rfl

theorem cell19_463986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_463986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_463986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_463986 prefixEnd_463986 := by exact prefixLift 463986
  have htrace : WordTrace (prefixWord ++ tailWord_463986) baseStart_463986 baseEnd_463986 := by
    simpa [prefixWord, tailWord_463986, baseEnd_463986] using wordTrace_append hprefix tailTrace_463986
  have hstable : (prefixWord ++ tailWord_463986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_463986).length < 2 ^ (prefixWord ++ tailWord_463986).sum := by decide
  have hdescent : baseEnd_463986 < baseStart_463986 := by decide
  rcases family_descends (prefixWord ++ tailWord_463986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464005 : List Nat := [1, 3, 1, 1, 6, 7]
def baseStart_464005 : Nat := 118140960795 + 464005 * 2 ^ 59
def prefixEnd_464005 : Nat := 4983230072969 + 3 ^ 40 * 464005 * 2
def baseEnd_464005 : Nat := 15687742623181057580483

theorem tailTrace_464005 : CollatzResearch.WordTrace tailWord_464005 prefixEnd_464005 15687742623181057580483 := by
  unfold tailWord_464005
  simp only [CollatzResearch.WordTrace]
  refine ⟨16923652683996605590033469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11282435122664403726688979 16923652683996605590033469)
  ·
    refine ⟨6346369756498727096262551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16923652683996605590033469 6346369756498727096262551)
    ·
      refine ⟨9519554634748090644393827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6346369756498727096262551 9519554634748090644393827)
      ·
        refine ⟨14279331952122135966590741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9519554634748090644393827 14279331952122135966590741)
        ·
          refine ⟨669343685255725123433941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14279331952122135966590741 669343685255725123433941)
          ·
            refine ⟨15687742623181057580483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 669343685255725123433941 15687742623181057580483)
            ·
              rfl

theorem cell19_464005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 7].length) (baseStart_464005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464005 prefixEnd_464005 := by exact prefixLift 464005
  have htrace : WordTrace (prefixWord ++ tailWord_464005) baseStart_464005 baseEnd_464005 := by
    simpa [prefixWord, tailWord_464005, baseEnd_464005] using wordTrace_append hprefix tailTrace_464005
  have hstable : (prefixWord ++ tailWord_464005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464005).length < 2 ^ (prefixWord ++ tailWord_464005).sum := by decide
  have hdescent : baseEnd_464005 < baseStart_464005 := by decide
  rcases family_descends (prefixWord ++ tailWord_464005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464039 : List Nat := [1, 1, 6, 2, 1, 2, 3, 3]
def baseStart_464039 : Nat := 118140960795 + 464039 * 2 ^ 59
def prefixEnd_464039 : Nat := 4983230072969 + 3 ^ 40 * 464039 * 2
def baseEnd_464039 : Nat := 141200029292927513468699

theorem tailTrace_464039 : CollatzResearch.WordTrace tailWord_464039 prefixEnd_464039 141200029292927513468699 := by
  unfold tailWord_464039
  simp only [CollatzResearch.WordTrace]
  refine ⟨16924892765873429396771171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11283261843915619597847447 16924892765873429396771171)
  ·
    refine ⟨25387339148810144095156757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16924892765873429396771171 25387339148810144095156757)
    ·
      refine ⟨1190031522600475504460473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25387339148810144095156757 1190031522600475504460473)
      ·
        refine ⟨892523641950356628345355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190031522600475504460473 892523641950356628345355)
        ·
          refine ⟨1338785462925534942518033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892523641950356628345355 1338785462925534942518033)
          ·
            refine ⟨1004089097194151206888525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338785462925534942518033 1004089097194151206888525)
            ·
              refine ⟨376533411447806702583197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1004089097194151206888525 376533411447806702583197)
              ·
                refine ⟨141200029292927513468699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376533411447806702583197 141200029292927513468699)
                ·
                  rfl

theorem cell19_464039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_464039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464039 prefixEnd_464039 := by exact prefixLift 464039
  have htrace : WordTrace (prefixWord ++ tailWord_464039) baseStart_464039 baseEnd_464039 := by
    simpa [prefixWord, tailWord_464039, baseEnd_464039] using wordTrace_append hprefix tailTrace_464039
  have hstable : (prefixWord ++ tailWord_464039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464039).length < 2 ^ (prefixWord ++ tailWord_464039).sum := by decide
  have hdescent : baseEnd_464039 < baseStart_464039 := by decide
  rcases family_descends (prefixWord ++ tailWord_464039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464136 : List Nat := [2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_464136 : Nat := 118140960795 + 464136 * 2 ^ 59
def prefixEnd_464136 : Nat := 4983230072969 + 3 ^ 40 * 464136 * 2
def baseEnd_464136 : Nat := 141229544921660029312879

theorem tailTrace_464136 : CollatzResearch.WordTrace tailWord_464136 prefixEnd_464136 141229544921660029312879 := by
  unfold tailWord_464136
  simp only [CollatzResearch.WordTrace]
  refine ⟨8464215323261007481526131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11285620431014676642034841 8464215323261007481526131)
  ·
    refine ⟨12696322984891511222289197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8464215323261007481526131 12696322984891511222289197)
    ·
      refine ⟨4761121119334316708358449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12696322984891511222289197 4761121119334316708358449)
      ·
        refine ⟨3570840839500737531268837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4761121119334316708358449 3570840839500737531268837)
        ·
          refine ⟨669532657406388287112907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3570840839500737531268837 669532657406388287112907)
          ·
            refine ⟨1004298986109582430669361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669532657406388287112907 1004298986109582430669361)
            ·
              refine ⟨753224239582186823002021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004298986109582430669361 753224239582186823002021)
              ·
                refine ⟨141229544921660029312879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 753224239582186823002021 141229544921660029312879)
                ·
                  rfl

theorem cell19_464136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_464136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464136 prefixEnd_464136 := by exact prefixLift 464136
  have htrace : WordTrace (prefixWord ++ tailWord_464136) baseStart_464136 baseEnd_464136 := by
    simpa [prefixWord, tailWord_464136, baseEnd_464136] using wordTrace_append hprefix tailTrace_464136
  have hstable : (prefixWord ++ tailWord_464136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464136).length < 2 ^ (prefixWord ++ tailWord_464136).sum := by decide
  have hdescent : baseEnd_464136 < baseStart_464136 := by decide
  rcases family_descends (prefixWord ++ tailWord_464136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464189 : List Nat := [1, 4, 1, 5, 2, 1, 1, 4]
def baseStart_464189 : Nat := 118140960795 + 464189 * 2 ^ 59
def prefixEnd_464189 : Nat := 4983230072969 + 3 ^ 40 * 464189 * 2
def baseEnd_464189 : Nat := 141245672017771610134957

theorem tailTrace_464189 : CollatzResearch.WordTrace tailWord_464189 prefixEnd_464189 141245672017771610134957 := by
  unfold tailWord_464189
  simp only [CollatzResearch.WordTrace]
  refine ⟨16930363715330005014731621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11286909143553336676487747 16930363715330005014731621)
  ·
    refine ⟨3174443196624375940262179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16930363715330005014731621 3174443196624375940262179)
    ·
      refine ⟨4761664794936563910393269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174443196624375940262179 4761664794936563910393269)
      ·
        refine ⟨446406074525302866599369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4761664794936563910393269 446406074525302866599369)
        ·
          refine ⟨334804555893977149949527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446406074525302866599369 334804555893977149949527)
          ·
            refine ⟨502206833840965724924291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334804555893977149949527 502206833840965724924291)
            ·
              refine ⟨753310250761448587386437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502206833840965724924291 753310250761448587386437)
              ·
                refine ⟨141245672017771610134957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 753310250761448587386437 141245672017771610134957)
                ·
                  rfl

theorem cell19_464189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 4].length) (baseStart_464189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464189 prefixEnd_464189 := by exact prefixLift 464189
  have htrace : WordTrace (prefixWord ++ tailWord_464189) baseStart_464189 baseEnd_464189 := by
    simpa [prefixWord, tailWord_464189, baseEnd_464189] using wordTrace_append hprefix tailTrace_464189
  have hstable : (prefixWord ++ tailWord_464189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464189).length < 2 ^ (prefixWord ++ tailWord_464189).sum := by decide
  have hdescent : baseEnd_464189 < baseStart_464189 := by decide
  rcases family_descends (prefixWord ++ tailWord_464189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464193 : List Nat := [1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_464193 : Nat := 118140960795 + 464193 * 2 ^ 59
def prefixEnd_464193 : Nat := 4983230072969 + 3 ^ 40 * 464193 * 2
def baseEnd_464193 : Nat := 141246889157100786046057

theorem tailTrace_464193 : CollatzResearch.WordTrace tailWord_464193 prefixEnd_464193 141246889157100786046057 := by
  unfold tailWord_464193
  simp only [CollatzResearch.WordTrace]
  refine ⟨16930509607315513697877233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11287006404877009131918155 16930509607315513697877233)
  ·
    refine ⟨12697882205486635273407925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16930509607315513697877233 12697882205486635273407925)
    ·
      refine ⟨1190426456764372056881993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12697882205486635273407925 1190426456764372056881993)
      ·
        refine ⟨892819842573279042661495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190426456764372056881993 892819842573279042661495)
        ·
          refine ⟨1339229763859918563992243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892819842573279042661495 1339229763859918563992243)
          ·
            refine ⟨2008844645789877845988365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339229763859918563992243 2008844645789877845988365)
            ·
              refine ⟨753316742171204192245637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2008844645789877845988365 753316742171204192245637)
              ·
                refine ⟨141246889157100786046057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 753316742171204192245637 141246889157100786046057)
                ·
                  rfl

theorem cell19_464193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_464193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464193 prefixEnd_464193 := by exact prefixLift 464193
  have htrace : WordTrace (prefixWord ++ tailWord_464193) baseStart_464193 baseEnd_464193 := by
    simpa [prefixWord, tailWord_464193, baseEnd_464193] using wordTrace_append hprefix tailTrace_464193
  have hstable : (prefixWord ++ tailWord_464193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464193).length < 2 ^ (prefixWord ++ tailWord_464193).sum := by decide
  have hdescent : baseEnd_464193 < baseStart_464193 := by decide
  rcases family_descends (prefixWord ++ tailWord_464193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464212 : List Nat := [2, 4, 1, 1, 2, 1, 5, 3]
def baseStart_464212 : Nat := 118140960795 + 464212 * 2 ^ 59
def prefixEnd_464212 : Nat := 4983230072969 + 3 ^ 40 * 464212 * 2
def baseEnd_464212 : Nat := 141252670568914371623783

theorem tailTrace_464212 : CollatzResearch.WordTrace tailWord_464212 prefixEnd_464212 141252670568914371623783 := by
  unfold tailWord_464212
  simp only [CollatzResearch.WordTrace]
  refine ⟨8465601297123339971409445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11287468396164453295212593 8465601297123339971409445)
  ·
    refine ⟨1587300243210626244639271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8465601297123339971409445 1587300243210626244639271)
    ·
      refine ⟨2380950364815939366958907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1587300243210626244639271 2380950364815939366958907)
      ·
        refine ⟨3571425547223909050438361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380950364815939366958907 3571425547223909050438361)
        ·
          refine ⟨2678569160417931787828771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3571425547223909050438361 2678569160417931787828771)
          ·
            refine ⟨4017853740626897681743157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678569160417931787828771 4017853740626897681743157)
            ·
              refine ⟨376673788183771657663421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4017853740626897681743157 376673788183771657663421)
              ·
                refine ⟨141252670568914371623783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376673788183771657663421 141252670568914371623783)
                ·
                  rfl

theorem cell19_464212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_464212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464212 prefixEnd_464212 := by exact prefixLift 464212
  have htrace : WordTrace (prefixWord ++ tailWord_464212) baseStart_464212 baseEnd_464212 := by
    simpa [prefixWord, tailWord_464212, baseEnd_464212] using wordTrace_append hprefix tailTrace_464212
  have hstable : (prefixWord ++ tailWord_464212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464212).length < 2 ^ (prefixWord ++ tailWord_464212).sum := by decide
  have hdescent : baseEnd_464212 < baseStart_464212 := by decide
  rcases family_descends (prefixWord ++ tailWord_464212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464273 : List Nat := [1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_464273 : Nat := 118140960795 + 464273 * 2 ^ 59
def prefixEnd_464273 : Nat := 4983230072969 + 3 ^ 40 * 464273 * 2
def baseEnd_464273 : Nat := 141271231943684304268061

theorem tailTrace_464273 : CollatzResearch.WordTrace tailWord_464273 prefixEnd_464273 141271231943684304268061 := by
  unfold tailWord_464273
  simp only [CollatzResearch.WordTrace]
  refine ⟨16933427447025687360789473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11288951631350458240526315 16933427447025687360789473)
  ·
    refine ⟨12700070585269265520592105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16933427447025687360789473 12700070585269265520592105)
    ·
      refine ⟨9525052938951949140444079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12700070585269265520592105 9525052938951949140444079)
      ·
        refine ⟨14287579408427923710666119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9525052938951949140444079 14287579408427923710666119)
        ·
          refine ⟨21431369112641885565999179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14287579408427923710666119 21431369112641885565999179)
          ·
            refine ⟨32147053668962828348998769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21431369112641885565999179 32147053668962828348998769)
            ·
              refine ⟨24110290251722121261749077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32147053668962828348998769 24110290251722121261749077)
              ·
                refine ⟨141271231943684304268061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24110290251722121261749077 141271231943684304268061)
                ·
                  rfl

theorem cell19_464273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_464273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464273 prefixEnd_464273 := by exact prefixLift 464273
  have htrace : WordTrace (prefixWord ++ tailWord_464273) baseStart_464273 baseEnd_464273 := by
    simpa [prefixWord, tailWord_464273, baseEnd_464273] using wordTrace_append hprefix tailTrace_464273
  have hstable : (prefixWord ++ tailWord_464273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464273).length < 2 ^ (prefixWord ++ tailWord_464273).sum := by decide
  have hdescent : baseEnd_464273 < baseStart_464273 := by decide
  rcases family_descends (prefixWord ++ tailWord_464273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464286 : List Nat := [4, 3, 1, 2, 2, 2, 5]
def baseStart_464286 : Nat := 118140960795 + 464286 * 2 ^ 59
def prefixEnd_464286 : Nat := 4983230072969 + 3 ^ 40 * 464286 * 2
def baseEnd_464286 : Nat := 47091729215501375326379

theorem tailTrace_464286 : CollatzResearch.WordTrace tailWord_464286 prefixEnd_464286 47091729215501375326379 := by
  unfold tailWord_464286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116737699497323822626589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11289267730652393720675141 2116737699497323822626589)
  ·
    refine ⟨793776637311496433484971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2116737699497323822626589 793776637311496433484971)
    ·
      refine ⟨1190664955967244650227457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 793776637311496433484971 1190664955967244650227457)
      ·
        refine ⟨892998716975433487670593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190664955967244650227457 892998716975433487670593)
        ·
          refine ⟨669749037731575115752945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 892998716975433487670593 669749037731575115752945)
          ·
            refine ⟨502311778298681336814709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669749037731575115752945 502311778298681336814709)
            ·
              refine ⟨47091729215501375326379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 502311778298681336814709 47091729215501375326379)
              ·
                rfl

theorem cell19_464286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_464286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464286 prefixEnd_464286 := by exact prefixLift 464286
  have htrace : WordTrace (prefixWord ++ tailWord_464286) baseStart_464286 baseEnd_464286 := by
    simpa [prefixWord, tailWord_464286, baseEnd_464286] using wordTrace_append hprefix tailTrace_464286
  have hstable : (prefixWord ++ tailWord_464286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464286).length < 2 ^ (prefixWord ++ tailWord_464286).sum := by decide
  have hdescent : baseEnd_464286 < baseStart_464286 := by decide
  rcases family_descends (prefixWord ++ tailWord_464286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464290 : List Nat := [3, 3, 1, 2, 1, 2, 7]
def baseStart_464290 : Nat := 118140960795 + 464290 * 2 ^ 59
def prefixEnd_464290 : Nat := 4983230072969 + 3 ^ 40 * 464290 * 2
def baseEnd_464290 : Nat := 47092134928611100630079

theorem tailTrace_464290 : CollatzResearch.WordTrace tailWord_464290 prefixEnd_464290 47092134928611100630079 := by
  unfold tailWord_464290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4233511871991024816039581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11289364991976066176105549 4233511871991024816039581)
  ·
    refine ⟨1587566951996634306014843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4233511871991024816039581 1587566951996634306014843)
    ·
      refine ⟨2381350427994951459022265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1587566951996634306014843 2381350427994951459022265)
      ·
        refine ⟨1786012820996213594266699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2381350427994951459022265 1786012820996213594266699)
        ·
          refine ⟨2679019231494320391400049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786012820996213594266699 2679019231494320391400049)
          ·
            refine ⟨2009264423620740293550037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679019231494320391400049 2009264423620740293550037)
            ·
              refine ⟨47092134928611100630079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2009264423620740293550037 47092134928611100630079)
              ·
                rfl

theorem cell19_464290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_464290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464290 prefixEnd_464290 := by exact prefixLift 464290
  have htrace : WordTrace (prefixWord ++ tailWord_464290) baseStart_464290 baseEnd_464290 := by
    simpa [prefixWord, tailWord_464290, baseEnd_464290] using wordTrace_append hprefix tailTrace_464290
  have hstable : (prefixWord ++ tailWord_464290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464290).length < 2 ^ (prefixWord ++ tailWord_464290).sum := by decide
  have hdescent : baseEnd_464290 < baseStart_464290 := by decide
  rcases family_descends (prefixWord ++ tailWord_464290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464309 : List Nat := [1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_464309 : Nat := 118140960795 + 464309 * 2 ^ 59
def prefixEnd_464309 : Nat := 4983230072969 + 3 ^ 40 * 464309 * 2
def baseEnd_464309 : Nat := 141282186197646887467963

theorem tailTrace_464309 : CollatzResearch.WordTrace tailWord_464309 prefixEnd_464309 141282186197646887467963 := by
  unfold tailWord_464309
  simp only [CollatzResearch.WordTrace]
  refine ⟨16934740474895265509099981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11289826983263510339399987 16934740474895265509099981)
  ·
    refine ⟨6350527678085724565912493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16934740474895265509099981 6350527678085724565912493)
    ·
      refine ⟨2381447879282146712217185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6350527678085724565912493 2381447879282146712217185)
      ·
        refine ⟨1786085909461610034162889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2381447879282146712217185 1786085909461610034162889)
        ·
          refine ⟨1339564432096207525622167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1786085909461610034162889 1339564432096207525622167)
          ·
            refine ⟨2009346648144311288433251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339564432096207525622167 2009346648144311288433251)
            ·
              refine ⟨3014019972216466932649877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009346648144311288433251 3014019972216466932649877)
              ·
                refine ⟨141282186197646887467963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3014019972216466932649877 141282186197646887467963)
                ·
                  rfl

theorem cell19_464309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_464309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464309 prefixEnd_464309 := by exact prefixLift 464309
  have htrace : WordTrace (prefixWord ++ tailWord_464309) baseStart_464309 baseEnd_464309 := by
    simpa [prefixWord, tailWord_464309, baseEnd_464309] using wordTrace_append hprefix tailTrace_464309
  have hstable : (prefixWord ++ tailWord_464309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464309).length < 2 ^ (prefixWord ++ tailWord_464309).sum := by decide
  have hdescent : baseEnd_464309 < baseStart_464309 := by decide
  rcases family_descends (prefixWord ++ tailWord_464309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464362 : List Nat := [3, 1, 3, 1, 5, 1, 1, 4]
def baseStart_464362 : Nat := 118140960795 + 464362 * 2 ^ 59
def prefixEnd_464362 : Nat := 4983230072969 + 3 ^ 40 * 464362 * 2
def baseEnd_464362 : Nat := 141298313293758468290041

theorem tailTrace_464362 : CollatzResearch.WordTrace tailWord_464362 prefixEnd_464362 141298313293758468290041 := by
  unfold tailWord_464362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234168385925813890194835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11291115695802170373852893 4234168385925813890194835)
  ·
    refine ⟨6351252578888720835292253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4234168385925813890194835 6351252578888720835292253)
    ·
      refine ⟨2381719717083270313234595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6351252578888720835292253 2381719717083270313234595)
      ·
        refine ⟨3572579575624905469851893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381719717083270313234595 3572579575624905469851893)
        ·
          refine ⟨334929335214834887798615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3572579575624905469851893 334929335214834887798615)
          ·
            refine ⟨502394002822252331697923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334929335214834887798615 502394002822252331697923)
            ·
              refine ⟨753591004233378497546885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502394002822252331697923 753591004233378497546885)
              ·
                refine ⟨141298313293758468290041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 753591004233378497546885 141298313293758468290041)
                ·
                  rfl

theorem cell19_464362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_464362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464362 prefixEnd_464362 := by exact prefixLift 464362
  have htrace : WordTrace (prefixWord ++ tailWord_464362) baseStart_464362 baseEnd_464362 := by
    simpa [prefixWord, tailWord_464362, baseEnd_464362] using wordTrace_append hprefix tailTrace_464362
  have hstable : (prefixWord ++ tailWord_464362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464362).length < 2 ^ (prefixWord ++ tailWord_464362).sum := by decide
  have hdescent : baseEnd_464362 < baseStart_464362 := by decide
  rcases family_descends (prefixWord ++ tailWord_464362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464440 : List Nat := [2, 1, 2, 1, 4, 4, 2, 3]
def baseStart_464440 : Nat := 118140960795 + 464440 * 2 ^ 59
def prefixEnd_464440 : Nat := 4983230072969 + 3 ^ 40 * 464440 * 2
def baseEnd_464440 : Nat := 141322047510677398556495

theorem tailTrace_464440 : CollatzResearch.WordTrace tailWord_464440 prefixEnd_464440 141322047510677398556495 := by
  unfold tailWord_464440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8469759218710337441059387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11293012291613783254745849 8469759218710337441059387)
  ·
    refine ⟨12704638828065506161589081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8469759218710337441059387 12704638828065506161589081)
    ·
      refine ⟨9528479121049129621191811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12704638828065506161589081 9528479121049129621191811)
      ·
        refine ⟨14292718681573694431787717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9528479121049129621191811 14292718681573694431787717)
        ·
          refine ⟨2679884752795067705960197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14292718681573694431787717 2679884752795067705960197)
          ·
            refine ⟨502478391149075194867537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2679884752795067705960197 502478391149075194867537)
            ·
              refine ⟨376858793361806396150653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502478391149075194867537 376858793361806396150653)
              ·
                refine ⟨141322047510677398556495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376858793361806396150653 141322047510677398556495)
                ·
                  rfl

theorem cell19_464440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_464440 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464440 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464440 prefixEnd_464440 := by exact prefixLift 464440
  have htrace : WordTrace (prefixWord ++ tailWord_464440) baseStart_464440 baseEnd_464440 := by
    simpa [prefixWord, tailWord_464440, baseEnd_464440] using wordTrace_append hprefix tailTrace_464440
  have hstable : (prefixWord ++ tailWord_464440).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464440).length < 2 ^ (prefixWord ++ tailWord_464440).sum := by decide
  have hdescent : baseEnd_464440 < baseStart_464440 := by decide
  rcases family_descends (prefixWord ++ tailWord_464440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464609 : List Nat := [1, 2, 3, 1, 6, 1, 2, 3]
def baseStart_464609 : Nat := 118140960795 + 464609 * 2 ^ 59
def prefixEnd_464609 : Nat := 4983230072969 + 3 ^ 40 * 464609 * 2
def baseEnd_464609 : Nat := 141373471647335080800479

theorem tailTrace_464609 : CollatzResearch.WordTrace tailWord_464609 prefixEnd_464609 141373471647335080800479 := by
  unfold tailWord_464609
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945682373808416745020881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11297121582538944496680587 16945682373808416745020881)
  ·
    refine ⟨12709261780356312558765661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16945682373808416745020881 12709261780356312558765661)
    ·
      refine ⟨4765973167633617209537123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12709261780356312558765661 4765973167633617209537123)
      ·
        refine ⟨7148959751450425814305685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765973167633617209537123 7148959751450425814305685)
        ·
          refine ⟨335107488349238710045579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7148959751450425814305685 335107488349238710045579)
          ·
            refine ⟨502661232523858065068369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335107488349238710045579 502661232523858065068369)
            ·
              refine ⟨376995924392893548801277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502661232523858065068369 376995924392893548801277)
              ·
                refine ⟨141373471647335080800479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 376995924392893548801277 141373471647335080800479)
                ·
                  rfl

theorem cell19_464609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 3].length) (baseStart_464609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464609 prefixEnd_464609 := by exact prefixLift 464609
  have htrace : WordTrace (prefixWord ++ tailWord_464609) baseStart_464609 baseEnd_464609 := by
    simpa [prefixWord, tailWord_464609, baseEnd_464609] using wordTrace_append hprefix tailTrace_464609
  have hstable : (prefixWord ++ tailWord_464609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464609).length < 2 ^ (prefixWord ++ tailWord_464609).sum := by decide
  have hdescent : baseEnd_464609 < baseStart_464609 := by decide
  rcases family_descends (prefixWord ++ tailWord_464609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464628 : List Nat := [2, 6, 1, 1, 1, 3, 5]
def baseStart_464628 : Nat := 118140960795 + 464628 * 2 ^ 59
def prefixEnd_464628 : Nat := 4983230072969 + 3 ^ 40 * 464628 * 2
def baseEnd_464628 : Nat := 47126417686382888792735

theorem tailTrace_464628 : CollatzResearch.WordTrace tailWord_464628 prefixEnd_464628 47126417686382888792735 := by
  unfold tailWord_464628
  simp only [CollatzResearch.WordTrace]
  refine ⟨8473187680369791494981269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11297583573826388659975025 8473187680369791494981269)
  ·
    refine ⟨397180672517333976327247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8473187680369791494981269 397180672517333976327247)
    ·
      refine ⟨595771008776000964490871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397180672517333976327247 595771008776000964490871)
      ·
        refine ⟨893656513164001446736307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595771008776000964490871 893656513164001446736307)
        ·
          refine ⟨1340484769746002170104461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893656513164001446736307 1340484769746002170104461)
          ·
            refine ⟨502681788654750813789173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1340484769746002170104461 502681788654750813789173)
            ·
              refine ⟨47126417686382888792735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 502681788654750813789173 47126417686382888792735)
              ·
                rfl

theorem cell19_464628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_464628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464628 prefixEnd_464628 := by exact prefixLift 464628
  have htrace : WordTrace (prefixWord ++ tailWord_464628) baseStart_464628 baseEnd_464628 := by
    simpa [prefixWord, tailWord_464628, baseEnd_464628] using wordTrace_append hprefix tailTrace_464628
  have hstable : (prefixWord ++ tailWord_464628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464628).length < 2 ^ (prefixWord ++ tailWord_464628).sum := by decide
  have hdescent : baseEnd_464628 < baseStart_464628 := by decide
  rcases family_descends (prefixWord ++ tailWord_464628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464672 : List Nat := [2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_464672 : Nat := 118140960795 + 464672 * 2 ^ 59
def prefixEnd_464672 : Nat := 4983230072969 + 3 ^ 40 * 464672 * 2
def baseEnd_464672 : Nat := 141392641591769601400307

theorem tailTrace_464672 : CollatzResearch.WordTrace tailWord_464672 prefixEnd_464672 141392641591769601400307 := by
  unfold tailWord_464672
  simp only [CollatzResearch.WordTrace]
  refine ⟨8473990086290089252282135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11298653448386785669709513 8473990086290089252282135)
  ·
    refine ⟨12710985129435133878423203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8473990086290089252282135 12710985129435133878423203)
    ·
      refine ⟨19066477694152700817634805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12710985129435133878423203 19066477694152700817634805)
      ·
        refine ⟨1787482283826815701653263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19066477694152700817634805 1787482283826815701653263)
        ·
          refine ⟨2681223425740223552479895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787482283826815701653263 2681223425740223552479895)
          ·
            refine ⟨4021835138610335328719843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681223425740223552479895 4021835138610335328719843)
            ·
              refine ⟨6032752707915502993079765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021835138610335328719843 6032752707915502993079765)
              ·
                refine ⟨141392641591769601400307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6032752707915502993079765 141392641591769601400307)
                ·
                  rfl

theorem cell19_464672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_464672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464672 prefixEnd_464672 := by exact prefixLift 464672
  have htrace : WordTrace (prefixWord ++ tailWord_464672) baseStart_464672 baseEnd_464672 := by
    simpa [prefixWord, tailWord_464672, baseEnd_464672] using wordTrace_append hprefix tailTrace_464672
  have hstable : (prefixWord ++ tailWord_464672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464672).length < 2 ^ (prefixWord ++ tailWord_464672).sum := by decide
  have hdescent : baseEnd_464672 < baseStart_464672 := by decide
  rcases family_descends (prefixWord ++ tailWord_464672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464691 : List Nat := [1, 1, 1, 2, 7, 7]
def baseStart_464691 : Nat := 118140960795 + 464691 * 2 ^ 59
def prefixEnd_464691 : Nat := 4983230072969 + 3 ^ 40 * 464691 * 2
def baseEnd_464691 : Nat := 15710935889287020775337

theorem tailTrace_464691 : CollatzResearch.WordTrace tailWord_464691 prefixEnd_464691 15710935889287020775337 := by
  unfold tailWord_464691
  simp only [CollatzResearch.WordTrace]
  refine ⟨16948673159511344749505927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11299115439674229833003951 16948673159511344749505927)
  ·
    refine ⟨25423009739267017124258891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16948673159511344749505927 25423009739267017124258891)
    ·
      refine ⟨38134514608900525686388337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25423009739267017124258891 38134514608900525686388337)
      ·
        refine ⟨28600885956675394264791253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38134514608900525686388337 28600885956675394264791253)
        ·
          refine ⟨670333264609579553081045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28600885956675394264791253 670333264609579553081045)
          ·
            refine ⟨15710935889287020775337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 670333264609579553081045 15710935889287020775337)
            ·
              rfl

theorem cell19_464691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 7].length) (baseStart_464691 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464691 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464691 prefixEnd_464691 := by exact prefixLift 464691
  have htrace : WordTrace (prefixWord ++ tailWord_464691) baseStart_464691 baseEnd_464691 := by
    simpa [prefixWord, tailWord_464691, baseEnd_464691] using wordTrace_append hprefix tailTrace_464691
  have hstable : (prefixWord ++ tailWord_464691).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464691).length < 2 ^ (prefixWord ++ tailWord_464691).sum := by decide
  have hdescent : baseEnd_464691 < baseStart_464691 := by decide
  rcases family_descends (prefixWord ++ tailWord_464691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464748 : List Nat := [2, 2, 1, 1, 4, 3, 6]
def baseStart_464748 : Nat := 118140960795 + 464748 * 2 ^ 59
def prefixEnd_464748 : Nat := 4983230072969 + 3 ^ 40 * 464748 * 2
def baseEnd_464748 : Nat := 47138589079674647903737

theorem tailTrace_464748 : CollatzResearch.WordTrace tailWord_464748 prefixEnd_464748 47138589079674647903737 := by
  unfold tailWord_464748
  simp only [CollatzResearch.WordTrace]
  refine ⟨8475376060152421742165449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11300501413536562322887265 8475376060152421742165449)
  ·
    refine ⟨6356532045114316306624087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8475376060152421742165449 6356532045114316306624087)
    ·
      refine ⟨9534798067671474459936131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6356532045114316306624087 9534798067671474459936131)
      ·
        refine ⟨14302197101507211689904197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9534798067671474459936131 14302197101507211689904197)
        ·
          refine ⟨2681661956532602191857037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14302197101507211689904197 2681661956532602191857037)
          ·
            refine ⟨1005623233699725821946389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2681661956532602191857037 1005623233699725821946389)
            ·
              refine ⟨47138589079674647903737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1005623233699725821946389 47138589079674647903737)
              ·
                rfl

theorem cell19_464748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_464748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464748 prefixEnd_464748 := by exact prefixLift 464748
  have htrace : WordTrace (prefixWord ++ tailWord_464748) baseStart_464748 baseEnd_464748 := by
    simpa [prefixWord, tailWord_464748, baseEnd_464748] using wordTrace_append hprefix tailTrace_464748
  have hstable : (prefixWord ++ tailWord_464748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464748).length < 2 ^ (prefixWord ++ tailWord_464748).sum := by decide
  have hdescent : baseEnd_464748 < baseStart_464748 := by decide
  rcases family_descends (prefixWord ++ tailWord_464748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464782 : List Nat := [4, 1, 1, 5, 1, 1, 1, 5]
def baseStart_464782 : Nat := 118140960795 + 464782 * 2 ^ 59
def prefixEnd_464782 : Nat := 4983230072969 + 3 ^ 40 * 464782 * 2
def baseEnd_464782 : Nat := 141426112923321938955563

theorem tailTrace_464782 : CollatzResearch.WordTrace tailWord_464782 prefixEnd_464782 141426112923321938955563 := by
  unfold tailWord_464782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118999025272708411383575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11301328134787778194045733 2118999025272708411383575)
  ·
    refine ⟨3178498537909062617075363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2118999025272708411383575 3178498537909062617075363)
    ·
      refine ⟨4767747806863593925613045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3178498537909062617075363 4767747806863593925613045)
      ·
        refine ⟨446976356893461930526223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4767747806863593925613045 446976356893461930526223)
        ·
          refine ⟨670464535340192895789335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446976356893461930526223 670464535340192895789335)
          ·
            refine ⟨1005696803010289343684003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670464535340192895789335 1005696803010289343684003)
            ·
              refine ⟨1508545204515434015526005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005696803010289343684003 1508545204515434015526005)
              ·
                refine ⟨141426112923321938955563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1508545204515434015526005 141426112923321938955563)
                ·
                  rfl

theorem cell19_464782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_464782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464782 prefixEnd_464782 := by exact prefixLift 464782
  have htrace : WordTrace (prefixWord ++ tailWord_464782) baseStart_464782 baseEnd_464782 := by
    simpa [prefixWord, tailWord_464782, baseEnd_464782] using wordTrace_append hprefix tailTrace_464782
  have hstable : (prefixWord ++ tailWord_464782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464782).length < 2 ^ (prefixWord ++ tailWord_464782).sum := by decide
  have hdescent : baseEnd_464782 < baseStart_464782 := by decide
  rcases family_descends (prefixWord ++ tailWord_464782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464801 : List Nat := [1, 2, 3, 4, 3, 1, 5]
def baseStart_464801 : Nat := 118140960795 + 464801 * 2 ^ 59
def prefixEnd_464801 : Nat := 4983230072969 + 3 ^ 40 * 464801 * 2
def baseEnd_464801 : Nat := 47143964778378508177763

theorem tailTrace_464801 : CollatzResearch.WordTrace tailWord_464801 prefixEnd_464801 47143964778378508177763 := by
  unfold tailWord_464801
  simp only [CollatzResearch.WordTrace]
  refine ⟨16952685189112833536010257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11301790126075222357340171 16952685189112833536010257)
  ·
    refine ⟨12714513891834625152007693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16952685189112833536010257 12714513891834625152007693)
    ·
      refine ⟨4767942709437984432002885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12714513891834625152007693 4767942709437984432002885)
      ·
        refine ⟨893989258019622081000541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4767942709437984432002885 893989258019622081000541)
        ·
          refine ⟨335245971757358280375203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 893989258019622081000541 335245971757358280375203)
          ·
            refine ⟨502868957636037420562805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335245971757358280375203 502868957636037420562805)
            ·
              refine ⟨47143964778378508177763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 502868957636037420562805 47143964778378508177763)
              ·
                rfl

theorem cell19_464801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 5].length) (baseStart_464801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464801 prefixEnd_464801 := by exact prefixLift 464801
  have htrace : WordTrace (prefixWord ++ tailWord_464801) baseStart_464801 baseEnd_464801 := by
    simpa [prefixWord, tailWord_464801, baseEnd_464801] using wordTrace_append hprefix tailTrace_464801
  have hstable : (prefixWord ++ tailWord_464801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464801).length < 2 ^ (prefixWord ++ tailWord_464801).sum := by decide
  have hdescent : baseEnd_464801 < baseStart_464801 := by decide
  rcases family_descends (prefixWord ++ tailWord_464801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464824 : List Nat := [2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_464824 : Nat := 118140960795 + 464824 * 2 ^ 59
def prefixEnd_464824 : Nat := 4983230072969 + 3 ^ 40 * 464824 * 2
def baseEnd_464824 : Nat := 141438892886278286022115

theorem tailTrace_464824 : CollatzResearch.WordTrace tailWord_464824 prefixEnd_464824 141438892886278286022115 := by
  unfold tailWord_464824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8476762034014754232048763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11302349378686338976065017 8476762034014754232048763)
  ·
    refine ⟨12715143051022131348073145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8476762034014754232048763 12715143051022131348073145)
    ·
      refine ⟨9536357288266598511054859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12715143051022131348073145 9536357288266598511054859)
      ·
        refine ⟨14304535932399897766582289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9536357288266598511054859 14304535932399897766582289)
        ·
          refine ⟨10728401949299923324936717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14304535932399897766582289 10728401949299923324936717)
          ·
            refine ⟨4023150730987471246851269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10728401949299923324936717 4023150730987471246851269)
            ·
              refine ⟨754340762060150858784613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4023150730987471246851269 754340762060150858784613)
              ·
                refine ⟨141438892886278286022115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754340762060150858784613 141438892886278286022115)
                ·
                  rfl

theorem cell19_464824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_464824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464824 prefixEnd_464824 := by exact prefixLift 464824
  have htrace : WordTrace (prefixWord ++ tailWord_464824) baseStart_464824 baseEnd_464824 := by
    simpa [prefixWord, tailWord_464824, baseEnd_464824] using wordTrace_append hprefix tailTrace_464824
  have hstable : (prefixWord ++ tailWord_464824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464824).length < 2 ^ (prefixWord ++ tailWord_464824).sum := by decide
  have hdescent : baseEnd_464824 < baseStart_464824 := by decide
  rcases family_descends (prefixWord ++ tailWord_464824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464953 : List Nat := [1, 2, 1, 5, 3, 2, 2, 3]
def baseStart_464953 : Nat := 118140960795 + 464953 * 2 ^ 59
def prefixEnd_464953 : Nat := 4983230072969 + 3 ^ 40 * 464953 * 2
def baseEnd_464953 : Nat := 141478145629644209155097

theorem tailTrace_464953 : CollatzResearch.WordTrace tailWord_464953 prefixEnd_464953 141478145629644209155097 := by
  unfold tailWord_464953
  simp only [CollatzResearch.WordTrace]
  refine ⟨16958229084562163495543513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11305486056374775663695675 16958229084562163495543513)
  ·
    refine ⟨12718671813421622621657635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16958229084562163495543513 12718671813421622621657635)
    ·
      refine ⟨19078007720132433932486453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12718671813421622621657635 19078007720132433932486453)
      ·
        refine ⟨1788563223762415681170605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19078007720132433932486453 1788563223762415681170605)
        ·
          refine ⟨670711208910905880438977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1788563223762415681170605 670711208910905880438977)
          ·
            refine ⟨503033406683179410329233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670711208910905880438977 503033406683179410329233)
            ·
              refine ⟨377275055012384557746925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503033406683179410329233 377275055012384557746925)
              ·
                refine ⟨141478145629644209155097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377275055012384557746925 141478145629644209155097)
                ·
                  rfl

theorem cell19_464953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_464953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464953 prefixEnd_464953 := by exact prefixLift 464953
  have htrace : WordTrace (prefixWord ++ tailWord_464953) baseStart_464953 baseEnd_464953 := by
    simpa [prefixWord, tailWord_464953, baseEnd_464953] using wordTrace_append hprefix tailTrace_464953
  have hstable : (prefixWord ++ tailWord_464953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464953).length < 2 ^ (prefixWord ++ tailWord_464953).sum := by decide
  have hdescent : baseEnd_464953 < baseStart_464953 := by decide
  rcases family_descends (prefixWord ++ tailWord_464953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_464957 : List Nat := [1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_464957 : Nat := 118140960795 + 464957 * 2 ^ 59
def prefixEnd_464957 : Nat := 4983230072969 + 3 ^ 40 * 464957 * 2
def baseEnd_464957 : Nat := 141479362768973385066197

theorem tailTrace_464957 : CollatzResearch.WordTrace tailWord_464957 prefixEnd_464957 141479362768973385066197 := by
  unfold tailWord_464957
  simp only [CollatzResearch.WordTrace]
  refine ⟨16958374976547672178689125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11305583317698448119126083 16958374976547672178689125)
  ·
    refine ⟨3179695308102688533504211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16958374976547672178689125 3179695308102688533504211)
    ·
      refine ⟨4769542962154032800256317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3179695308102688533504211 4769542962154032800256317)
      ·
        refine ⟨1788578610807762300096119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4769542962154032800256317 1788578610807762300096119)
        ·
          refine ⟨2682867916211643450144179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788578610807762300096119 2682867916211643450144179)
          ·
            refine ⟨4024301874317465175216269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682867916211643450144179 4024301874317465175216269)
            ·
              refine ⟨1509113202869049440706101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4024301874317465175216269 1509113202869049440706101)
              ·
                refine ⟨141479362768973385066197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1509113202869049440706101 141479362768973385066197)
                ·
                  rfl

theorem cell19_464957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_464957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_464957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_464957 prefixEnd_464957 := by exact prefixLift 464957
  have htrace : WordTrace (prefixWord ++ tailWord_464957) baseStart_464957 baseEnd_464957 := by
    simpa [prefixWord, tailWord_464957, baseEnd_464957] using wordTrace_append hprefix tailTrace_464957
  have hstable : (prefixWord ++ tailWord_464957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_464957).length < 2 ^ (prefixWord ++ tailWord_464957).sum := by decide
  have hdescent : baseEnd_464957 < baseStart_464957 := by decide
  rcases family_descends (prefixWord ++ tailWord_464957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465048 : List Nat := [2, 1, 2, 4, 4, 1, 1, 4]
def baseStart_465048 : Nat := 118140960795 + 465048 * 2 ^ 59
def prefixEnd_465048 : Nat := 4983230072969 + 3 ^ 40 * 465048 * 2
def baseEnd_465048 : Nat := 141507052688712137043727

theorem tailTrace_465048 : CollatzResearch.WordTrace tailWord_465048 prefixEnd_465048 141507052688712137043727 := by
  unfold tailWord_465048
  simp only [CollatzResearch.WordTrace]
  refine ⟨8480847009608997360125899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11307796012811996480167865 8480847009608997360125899)
  ·
    refine ⟨12721270514413496040188849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8480847009608997360125899 12721270514413496040188849)
    ·
      refine ⟨9540952885810122030141637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12721270514413496040188849 9540952885810122030141637)
      ·
        refine ⟨1788928666089397880651557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9540952885810122030141637 1788928666089397880651557)
        ·
          refine ⟨335424124891762102622167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1788928666089397880651557 335424124891762102622167)
          ·
            refine ⟨503136187337643153933251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335424124891762102622167 503136187337643153933251)
            ·
              refine ⟨754704281006464730899877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503136187337643153933251 754704281006464730899877)
              ·
                refine ⟨141507052688712137043727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754704281006464730899877 141507052688712137043727)
                ·
                  rfl

theorem cell19_465048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_465048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465048 prefixEnd_465048 := by exact prefixLift 465048
  have htrace : WordTrace (prefixWord ++ tailWord_465048) baseStart_465048 baseEnd_465048 := by
    simpa [prefixWord, tailWord_465048, baseEnd_465048] using wordTrace_append hprefix tailTrace_465048
  have hstable : (prefixWord ++ tailWord_465048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465048).length < 2 ^ (prefixWord ++ tailWord_465048).sum := by decide
  have hdescent : baseEnd_465048 < baseStart_465048 := by decide
  rcases family_descends (prefixWord ++ tailWord_465048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465111 : List Nat := [1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_465111 : Nat := 118140960795 + 465111 * 2 ^ 59
def prefixEnd_465111 : Nat := 4983230072969 + 3 ^ 40 * 465111 * 2
def baseEnd_465111 : Nat := 141526222633146657643555

theorem tailTrace_465111 : CollatzResearch.WordTrace tailWord_465111 prefixEnd_465111 141526222633146657643555 := by
  unfold tailWord_465111
  simp only [CollatzResearch.WordTrace]
  refine ⟨16963991817989756479795187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11309327878659837653196791 16963991817989756479795187)
  ·
    refine ⟨25445987726984634719692781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16963991817989756479795187 25445987726984634719692781)
    ·
      refine ⟨9542245397619238019884793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25445987726984634719692781 9542245397619238019884793)
      ·
        refine ⟨7156684048214428514913595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9542245397619238019884793 7156684048214428514913595)
        ·
          refine ⟨10735026072321642772370393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156684048214428514913595 10735026072321642772370393)
          ·
            refine ⟨8051269554241232079277795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10735026072321642772370393 8051269554241232079277795)
            ·
              refine ⟨12076904331361848118916693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8051269554241232079277795 12076904331361848118916693)
              ·
                refine ⟨141526222633146657643555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12076904331361848118916693 141526222633146657643555)
                ·
                  rfl

theorem cell19_465111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_465111 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465111 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465111 prefixEnd_465111 := by exact prefixLift 465111
  have htrace : WordTrace (prefixWord ++ tailWord_465111) baseStart_465111 baseEnd_465111 := by
    simpa [prefixWord, tailWord_465111, baseEnd_465111] using wordTrace_append hprefix tailTrace_465111
  have hstable : (prefixWord ++ tailWord_465111).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465111).length < 2 ^ (prefixWord ++ tailWord_465111).sum := by decide
  have hdescent : baseEnd_465111 < baseStart_465111 := by decide
  rcases family_descends (prefixWord ++ tailWord_465111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465122 : List Nat := [3, 3, 4, 1, 1, 1, 1, 5]
def baseStart_465122 : Nat := 118140960795 + 465122 * 2 ^ 59
def prefixEnd_465122 : Nat := 4983230072969 + 3 ^ 40 * 465122 * 2
def baseEnd_465122 : Nat := 141529569766301891399081

theorem tailTrace_465122 : CollatzResearch.WordTrace tailWord_465122 prefixEnd_465122 141529569766301891399081 := by
  unfold tailWord_465122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241098255237476339611405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11309595347299936905630413 4241098255237476339611405)
  ·
    refine ⟨1590411845714053627354277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4241098255237476339611405 1590411845714053627354277)
    ·
      refine ⟨298202221071385055128927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1590411845714053627354277 298202221071385055128927)
      ·
        refine ⟨447303331607077582693391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298202221071385055128927 447303331607077582693391)
        ·
          refine ⟨670954997410616374040087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447303331607077582693391 670954997410616374040087)
          ·
            refine ⟨1006432496115924561060131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670954997410616374040087 1006432496115924561060131)
            ·
              refine ⟨1509648744173886841590197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006432496115924561060131 1509648744173886841590197)
              ·
                refine ⟨141529569766301891399081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1509648744173886841590197 141529569766301891399081)
                ·
                  rfl

theorem cell19_465122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_465122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465122 prefixEnd_465122 := by exact prefixLift 465122
  have htrace : WordTrace (prefixWord ++ tailWord_465122) baseStart_465122 baseEnd_465122 := by
    simpa [prefixWord, tailWord_465122, baseEnd_465122] using wordTrace_append hprefix tailTrace_465122
  have hstable : (prefixWord ++ tailWord_465122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465122).length < 2 ^ (prefixWord ++ tailWord_465122).sum := by decide
  have hdescent : baseEnd_465122 < baseStart_465122 := by decide
  rcases family_descends (prefixWord ++ tailWord_465122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465128 : List Nat := [2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_465128 : Nat := 118140960795 + 465128 * 2 ^ 59
def prefixEnd_465128 : Nat := 4983230072969 + 3 ^ 40 * 465128 * 2
def baseEnd_465128 : Nat := 141531395475295655265731

theorem tailTrace_465128 : CollatzResearch.WordTrace tailWord_465128 prefixEnd_465128 141531395475295655265731 := by
  unfold tailWord_465128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8482305929464084191582019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11309741239285445588776025 8482305929464084191582019)
  ·
    refine ⟨12723458894196126287373029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8482305929464084191582019 12723458894196126287373029)
    ·
      refine ⟨2385648542661773678882443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12723458894196126287373029 2385648542661773678882443)
      ·
        refine ⟨3578472813992660518323665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385648542661773678882443 3578472813992660518323665)
        ·
          refine ⟨2683854610494495388742749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3578472813992660518323665 2683854610494495388742749)
          ·
            refine ⟨1006445478935435770778531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2683854610494495388742749 1006445478935435770778531)
            ·
              refine ⟨1509668218403153656167797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006445478935435770778531 1509668218403153656167797)
              ·
                refine ⟨141531395475295655265731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1509668218403153656167797 141531395475295655265731)
                ·
                  rfl

theorem cell19_465128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_465128 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465128 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465128 prefixEnd_465128 := by exact prefixLift 465128
  have htrace : WordTrace (prefixWord ++ tailWord_465128) baseStart_465128 baseEnd_465128 := by
    simpa [prefixWord, tailWord_465128, baseEnd_465128] using wordTrace_append hprefix tailTrace_465128
  have hstable : (prefixWord ++ tailWord_465128).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465128).length < 2 ^ (prefixWord ++ tailWord_465128).sum := by decide
  have hdescent : baseEnd_465128 < baseStart_465128 := by decide
  rcases family_descends (prefixWord ++ tailWord_465128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465166 : List Nat := [4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_465166 : Nat := 118140960795 + 465166 * 2 ^ 59
def prefixEnd_465166 : Nat := 4983230072969 + 3 ^ 40 * 465166 * 2
def baseEnd_465166 : Nat := 141542958298922826421183

theorem tailTrace_465166 : CollatzResearch.WordTrace tailWord_465166 prefixEnd_465166 141542958298922826421183 := by
  unfold tailWord_465166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120749729098812609130919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11310665221860333915364901 2120749729098812609130919)
  ·
    refine ⟨3181124593648218913696379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2120749729098812609130919 3181124593648218913696379)
    ·
      refine ⟨4771686890472328370544569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3181124593648218913696379 4771686890472328370544569)
      ·
        refine ⟨3578765167854246277908427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4771686890472328370544569 3578765167854246277908427)
        ·
          refine ⟨5368147751781369416862641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3578765167854246277908427 5368147751781369416862641)
          ·
            refine ⟨4026110813836027062646981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5368147751781369416862641 4026110813836027062646981)
            ·
              refine ⟨754895777594255074246309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4026110813836027062646981 754895777594255074246309)
              ·
                refine ⟨141542958298922826421183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754895777594255074246309 141542958298922826421183)
                ·
                  rfl

theorem cell19_465166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_465166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465166 prefixEnd_465166 := by exact prefixLift 465166
  have htrace : WordTrace (prefixWord ++ tailWord_465166) baseStart_465166 baseEnd_465166 := by
    simpa [prefixWord, tailWord_465166, baseEnd_465166] using wordTrace_append hprefix tailTrace_465166
  have hstable : (prefixWord ++ tailWord_465166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465166).length < 2 ^ (prefixWord ++ tailWord_465166).sum := by decide
  have hdescent : baseEnd_465166 < baseStart_465166 := by decide
  rcases family_descends (prefixWord ++ tailWord_465166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465187 : List Nat := [1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_465187 : Nat := 118140960795 + 465187 * 2 ^ 59
def prefixEnd_465187 : Nat := 4983230072969 + 3 ^ 40 * 465187 * 2
def baseEnd_465187 : Nat := 141549348280400999954459

theorem tailTrace_465187 : CollatzResearch.WordTrace tailWord_465187 prefixEnd_465187 141549348280400999954459 := by
  unfold tailWord_465187
  simp only [CollatzResearch.WordTrace]
  refine ⟨16966763765714421459561815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11311175843809614306374543 16966763765714421459561815)
  ·
    refine ⟨25450145648571632189342723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16966763765714421459561815 25450145648571632189342723)
    ·
      refine ⟨38175218472857448284014085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25450145648571632189342723 38175218472857448284014085)
      ·
        refine ⟨7157853463660771553252641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38175218472857448284014085 7157853463660771553252641)
        ·
          refine ⟨5368390097745578664939481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7157853463660771553252641 5368390097745578664939481)
          ·
            refine ⟨4026292573309183998704611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5368390097745578664939481 4026292573309183998704611)
            ·
              refine ⟨6039438859963775998056917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026292573309183998704611 6039438859963775998056917)
              ·
                refine ⟨141549348280400999954459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6039438859963775998056917 141549348280400999954459)
                ·
                  rfl

theorem cell19_465187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_465187 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465187 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465187 prefixEnd_465187 := by exact prefixLift 465187
  have htrace : WordTrace (prefixWord ++ tailWord_465187) baseStart_465187 baseEnd_465187 := by
    simpa [prefixWord, tailWord_465187, baseEnd_465187] using wordTrace_append hprefix tailTrace_465187
  have hstable : (prefixWord ++ tailWord_465187).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465187).length < 2 ^ (prefixWord ++ tailWord_465187).sum := by decide
  have hdescent : baseEnd_465187 < baseStart_465187 := by decide
  rcases family_descends (prefixWord ++ tailWord_465187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465204 : List Nat := [2, 5, 1, 1, 1, 9]
def baseStart_465204 : Nat := 118140960795 + 465204 * 2 ^ 59
def prefixEnd_465204 : Nat := 4983230072969 + 3 ^ 40 * 465204 * 2
def baseEnd_465204 : Nat := 15728280124727777508515

theorem tailTrace_465204 : CollatzResearch.WordTrace tailWord_465204 prefixEnd_465204 15728280124727777508515 := by
  unfold tailWord_465204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8483691903326416681465333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11311589204435222241953777 8483691903326416681465333)
  ·
    refine ⟨795346115936851563887375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8483691903326416681465333 795346115936851563887375)
    ·
      refine ⟨1193019173905277345831063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795346115936851563887375 1193019173905277345831063)
      ·
        refine ⟨1789528760857916018746595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193019173905277345831063 1789528760857916018746595)
        ·
          refine ⟨2684293141286874028119893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1789528760857916018746595 2684293141286874028119893)
          ·
            refine ⟨15728280124727777508515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2684293141286874028119893 15728280124727777508515)
            ·
              rfl

theorem cell19_465204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 9].length) (baseStart_465204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465204 prefixEnd_465204 := by exact prefixLift 465204
  have htrace : WordTrace (prefixWord ++ tailWord_465204) baseStart_465204 baseEnd_465204 := by
    simpa [prefixWord, tailWord_465204, baseEnd_465204] using wordTrace_append hprefix tailTrace_465204
  have hstable : (prefixWord ++ tailWord_465204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465204).length < 2 ^ (prefixWord ++ tailWord_465204).sum := by decide
  have hdescent : baseEnd_465204 < baseStart_465204 := by decide
  rcases family_descends (prefixWord ++ tailWord_465204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465337 : List Nat := [1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_465337 : Nat := 118140960795 + 465337 * 2 ^ 59
def prefixEnd_465337 : Nat := 4983230072969 + 3 ^ 40 * 465337 * 2
def baseEnd_465337 : Nat := 141594991005245096620717

theorem tailTrace_465337 : CollatzResearch.WordTrace tailWord_465337 prefixEnd_465337 141594991005245096620717 := by
  unfold tailWord_465337
  simp only [CollatzResearch.WordTrace]
  refine ⟨16972234715170997077522265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11314823143447331385014843 16972234715170997077522265)
  ·
    refine ⟨12729176036378247808141699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16972234715170997077522265 12729176036378247808141699)
    ·
      refine ⟨19093764054567371712212549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12729176036378247808141699 19093764054567371712212549)
      ·
        refine ⟨3580080760231382196039853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19093764054567371712212549 3580080760231382196039853)
        ·
          refine ⟨1342530285086768323514945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3580080760231382196039853 1342530285086768323514945)
          ·
            refine ⟨1006897713815076242636209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1342530285086768323514945 1006897713815076242636209)
            ·
              refine ⟨755173285361307181977157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006897713815076242636209 755173285361307181977157)
              ·
                refine ⟨141594991005245096620717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 755173285361307181977157 141594991005245096620717)
                ·
                  rfl

theorem cell19_465337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_465337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465337 prefixEnd_465337 := by exact prefixLift 465337
  have htrace : WordTrace (prefixWord ++ tailWord_465337) baseStart_465337 baseEnd_465337 := by
    simpa [prefixWord, tailWord_465337, baseEnd_465337] using wordTrace_append hprefix tailTrace_465337
  have hstable : (prefixWord ++ tailWord_465337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465337).length < 2 ^ (prefixWord ++ tailWord_465337).sum := by decide
  have hdescent : baseEnd_465337 < baseStart_465337 := by decide
  rcases family_descends (prefixWord ++ tailWord_465337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465468 : List Nat := [2, 2, 2, 2, 3, 3, 2, 3]
def baseStart_465468 : Nat := 118140960795 + 465468 * 2 ^ 59
def prefixEnd_465468 : Nat := 4983230072969 + 3 ^ 40 * 465468 * 2
def baseEnd_465468 : Nat := 141634852318275607709249

theorem tailTrace_465468 : CollatzResearch.WordTrace tailWord_465468 prefixEnd_465468 141634852318275607709249 := by
  unfold tailWord_465468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8488506338848203225270529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11318008451797604300360705 8488506338848203225270529)
  ·
    refine ⟨6366379754136152418952897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8488506338848203225270529 6366379754136152418952897)
    ·
      refine ⟨4774784815602114314214673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6366379754136152418952897 4774784815602114314214673)
      ·
        refine ⟨3581088611701585735661005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4774784815602114314214673 3581088611701585735661005)
        ·
          refine ⟨1342908229388094650872877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3581088611701585735661005 1342908229388094650872877)
          ·
            refine ⟨503590586020535494077329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1342908229388094650872877 503590586020535494077329)
            ·
              refine ⟨377692939515401620557997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503590586020535494077329 377692939515401620557997)
              ·
                refine ⟨141634852318275607709249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377692939515401620557997 141634852318275607709249)
                ·
                  rfl

theorem cell19_465468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_465468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465468 prefixEnd_465468 := by exact prefixLift 465468
  have htrace : WordTrace (prefixWord ++ tailWord_465468) baseStart_465468 baseEnd_465468 := by
    simpa [prefixWord, tailWord_465468, baseEnd_465468] using wordTrace_append hprefix tailTrace_465468
  have hstable : (prefixWord ++ tailWord_465468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465468).length < 2 ^ (prefixWord ++ tailWord_465468).sum := by decide
  have hdescent : baseEnd_465468 < baseStart_465468 := by decide
  rcases family_descends (prefixWord ++ tailWord_465468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465502 : List Nat := [4, 4, 1, 2, 1, 1, 2, 4]
def baseStart_465502 : Nat := 118140960795 + 465502 * 2 ^ 59
def prefixEnd_465502 : Nat := 4983230072969 + 3 ^ 40 * 465502 * 2
def baseEnd_465502 : Nat := 141645198002573602953601

theorem tailTrace_465502 : CollatzResearch.WordTrace tailWord_465502 prefixEnd_465502 141645198002573602953601 := by
  unfold tailWord_465502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122281594946653782159845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11318835173048820171519173 2122281594946653782159845)
  ·
    refine ⟨397927799052497584154971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2122281594946653782159845 397927799052497584154971)
    ·
      refine ⟨596891698578746376232457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397927799052497584154971 596891698578746376232457)
      ·
        refine ⟨447668773934059782174343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596891698578746376232457 447668773934059782174343)
        ·
          refine ⟨671503160901089673261515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447668773934059782174343 671503160901089673261515)
          ·
            refine ⟨1007254741351634509892273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671503160901089673261515 1007254741351634509892273)
            ·
              refine ⟨755441056013725882419205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1007254741351634509892273 755441056013725882419205)
              ·
                refine ⟨141645198002573602953601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 755441056013725882419205 141645198002573602953601)
                ·
                  rfl

theorem cell19_465502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_465502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465502 prefixEnd_465502 := by exact prefixLift 465502
  have htrace : WordTrace (prefixWord ++ tailWord_465502) baseStart_465502 baseEnd_465502 := by
    simpa [prefixWord, tailWord_465502, baseEnd_465502] using wordTrace_append hprefix tailTrace_465502
  have hstable : (prefixWord ++ tailWord_465502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465502).length < 2 ^ (prefixWord ++ tailWord_465502).sum := by decide
  have hdescent : baseEnd_465502 < baseStart_465502 := by decide
  rcases family_descends (prefixWord ++ tailWord_465502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465529 : List Nat := [1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_465529 : Nat := 118140960795 + 465529 * 2 ^ 59
def prefixEnd_465529 : Nat := 4983230072969 + 3 ^ 40 * 465529 * 2
def baseEnd_465529 : Nat := 141653413693045540353527

theorem tailTrace_465529 : CollatzResearch.WordTrace tailWord_465529 prefixEnd_465529 141653413693045540353527 := by
  unfold tailWord_465529
  simp only [CollatzResearch.WordTrace]
  refine ⟨16979237530475413868511641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11319491686983609245674427 16979237530475413868511641)
  ·
    refine ⟨12734428147856560401383731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16979237530475413868511641 12734428147856560401383731)
    ·
      refine ⟨19101642221784840602075597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12734428147856560401383731 19101642221784840602075597)
      ·
        refine ⟨7163115833169315225778349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19101642221784840602075597 7163115833169315225778349)
        ·
          refine ⟨2686168437438493209666881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7163115833169315225778349 2686168437438493209666881)
          ·
            refine ⟨2014626328078869907250161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2686168437438493209666881 2014626328078869907250161)
            ·
              refine ⟨1510969746059152430437621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014626328078869907250161 1510969746059152430437621)
              ·
                refine ⟨141653413693045540353527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1510969746059152430437621 141653413693045540353527)
                ·
                  rfl

theorem cell19_465529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_465529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465529 prefixEnd_465529 := by exact prefixLift 465529
  have htrace : WordTrace (prefixWord ++ tailWord_465529) baseStart_465529 baseEnd_465529 := by
    simpa [prefixWord, tailWord_465529, baseEnd_465529] using wordTrace_append hprefix tailTrace_465529
  have hstable : (prefixWord ++ tailWord_465529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465529).length < 2 ^ (prefixWord ++ tailWord_465529).sum := by decide
  have hdescent : baseEnd_465529 < baseStart_465529 := by decide
  rcases family_descends (prefixWord ++ tailWord_465529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465546 : List Nat := [3, 1, 2, 3, 4, 6]
def baseStart_465546 : Nat := 118140960795 + 465546 * 2 ^ 59
def prefixEnd_465546 : Nat := 4983230072969 + 3 ^ 40 * 465546 * 2
def baseEnd_465546 : Nat := 15739842948354948663967

theorem tailTrace_465546 : CollatzResearch.WordTrace tailWord_465546 prefixEnd_465546 15739842948354948663967 := by
  unfold tailWord_465546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4244964392853456442970123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11319905047609217181253661 4244964392853456442970123)
  ·
    refine ⟨6367446589280184664455185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4244964392853456442970123 6367446589280184664455185)
    ·
      refine ⟨4775584941960138498341389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6367446589280184664455185 4775584941960138498341389)
      ·
        refine ⟨1790844353235051936878021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4775584941960138498341389 1790844353235051936878021)
        ·
          refine ⟨335783316231572238164629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1790844353235051936878021 335783316231572238164629)
          ·
            refine ⟨15739842948354948663967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 335783316231572238164629 15739842948354948663967)
            ·
              rfl

theorem cell19_465546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 6].length) (baseStart_465546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465546 prefixEnd_465546 := by exact prefixLift 465546
  have htrace : WordTrace (prefixWord ++ tailWord_465546) baseStart_465546 baseEnd_465546 := by
    simpa [prefixWord, tailWord_465546, baseEnd_465546] using wordTrace_append hprefix tailTrace_465546
  have hstable : (prefixWord ++ tailWord_465546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465546).length < 2 ^ (prefixWord ++ tailWord_465546).sum := by decide
  have hdescent : baseEnd_465546 < baseStart_465546 := by decide
  rcases family_descends (prefixWord ++ tailWord_465546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465601 : List Nat := [1, 2, 6, 2, 1, 1, 6]
def baseStart_465601 : Nat := 118140960795 + 465601 * 2 ^ 59
def prefixEnd_465601 : Nat := 4983230072969 + 3 ^ 40 * 465601 * 2
def baseEnd_465601 : Nat := 47225107400323568917777

theorem tailTrace_465601 : CollatzResearch.WordTrace tailWord_465601 prefixEnd_465601 47225107400323568917777 := by
  unfold tailWord_465601
  simp only [CollatzResearch.WordTrace]
  refine ⟨16981863586214570165132657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11321242390809713443421771 16981863586214570165132657)
  ·
    refine ⟨12736397689660927623849493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16981863586214570165132657 12736397689660927623849493)
    ·
      refine ⟨597018641702855982367945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12736397689660927623849493 597018641702855982367945)
      ·
        refine ⟨447763981277141986775959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597018641702855982367945 447763981277141986775959)
        ·
          refine ⟨671645971915712980163939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447763981277141986775959 671645971915712980163939)
          ·
            refine ⟨1007468957873569470245909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671645971915712980163939 1007468957873569470245909)
            ·
              refine ⟨47225107400323568917777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1007468957873569470245909 47225107400323568917777)
              ·
                rfl

theorem cell19_465601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_465601 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465601 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465601 prefixEnd_465601 := by exact prefixLift 465601
  have htrace : WordTrace (prefixWord ++ tailWord_465601) baseStart_465601 baseEnd_465601 := by
    simpa [prefixWord, tailWord_465601, baseEnd_465601] using wordTrace_append hprefix tailTrace_465601
  have hstable : (prefixWord ++ tailWord_465601).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465601).length < 2 ^ (prefixWord ++ tailWord_465601).sum := by decide
  have hdescent : baseEnd_465601 < baseStart_465601 := by decide
  rcases family_descends (prefixWord ++ tailWord_465601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465721 : List Nat := [1, 2, 1, 15]
def baseStart_465721 : Nat := 118140960795 + 465721 * 2 ^ 59
def prefixEnd_465721 : Nat := 4983230072969 + 3 ^ 40 * 465721 * 2
def baseEnd_465721 : Nat := 1749528844207975112177

theorem tailTrace_465721 : CollatzResearch.WordTrace tailWord_465721 prefixEnd_465721 1749528844207975112177 := by
  unfold tailWord_465721
  simp only [CollatzResearch.WordTrace]
  refine ⟨16986240345779830659501017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11324160230519887106334011 16986240345779830659501017)
  ·
    refine ⟨12739680259334872994625763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16986240345779830659501017 12739680259334872994625763)
    ·
      refine ⟨19109520389002309491938645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12739680259334872994625763 19109520389002309491938645)
      ·
        refine ⟨1749528844207975112177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 19109520389002309491938645 1749528844207975112177)
        ·
          rfl

theorem cell19_465721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 15].length) (baseStart_465721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465721 prefixEnd_465721 := by exact prefixLift 465721
  have htrace : WordTrace (prefixWord ++ tailWord_465721) baseStart_465721 baseEnd_465721 := by
    simpa [prefixWord, tailWord_465721, baseEnd_465721] using wordTrace_append hprefix tailTrace_465721
  have hstable : (prefixWord ++ tailWord_465721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465721).length < 2 ^ (prefixWord ++ tailWord_465721).sum := by decide
  have hdescent : baseEnd_465721 < baseStart_465721 := by decide
  rcases family_descends (prefixWord ++ tailWord_465721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465732 : List Nat := [2, 3, 4, 2, 1, 2, 1, 4]
def baseStart_465732 : Nat := 118140960795 + 465732 * 2 ^ 59
def prefixEnd_465732 : Nat := 4983230072969 + 3 ^ 40 * 465732 * 2
def baseEnd_465732 : Nat := 141715183514001217841863

theorem tailTrace_465732 : CollatzResearch.WordTrace tailWord_465732 prefixEnd_465732 141715183514001217841863 := by
  unfold tailWord_465732
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493320774369989769075725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11324427699159986358767633 8493320774369989769075725)
  ·
    refine ⟨3184995290388746163403397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8493320774369989769075725 3184995290388746163403397)
    ·
      refine ⟨597186616947889905638137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3184995290388746163403397 597186616947889905638137)
      ·
        refine ⟨447889962710917429228603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597186616947889905638137 447889962710917429228603)
        ·
          refine ⟨671834944066376143842905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447889962710917429228603 671834944066376143842905)
          ·
            refine ⟨503876208049782107882179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671834944066376143842905 503876208049782107882179)
            ·
              refine ⟨755814312074673161823269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503876208049782107882179 755814312074673161823269)
              ·
                refine ⟨141715183514001217841863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 755814312074673161823269 141715183514001217841863)
                ·
                  rfl

theorem cell19_465732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_465732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465732 prefixEnd_465732 := by exact prefixLift 465732
  have htrace : WordTrace (prefixWord ++ tailWord_465732) baseStart_465732 baseEnd_465732 := by
    simpa [prefixWord, tailWord_465732, baseEnd_465732] using wordTrace_append hprefix tailTrace_465732
  have hstable : (prefixWord ++ tailWord_465732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465732).length < 2 ^ (prefixWord ++ tailWord_465732).sum := by decide
  have hdescent : baseEnd_465732 < baseStart_465732 := by decide
  rcases family_descends (prefixWord ++ tailWord_465732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465774 : List Nat := [4, 1, 2, 3, 2, 1, 6]
def baseStart_465774 : Nat := 118140960795 + 465774 * 2 ^ 59
def prefixEnd_465774 : Nat := 4983230072969 + 3 ^ 40 * 465774 * 2
def baseEnd_465774 : Nat := 47242654492319188302805

theorem tailTrace_465774 : CollatzResearch.WordTrace tailWord_465774 prefixEnd_465774 47242654492319188302805 := by
  unfold tailWord_465774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2123521676823477588897547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11325448943058547140786917 2123521676823477588897547)
  ·
    refine ⟨3185282515235216383346321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2123521676823477588897547 3185282515235216383346321)
    ·
      refine ⟨2388961886426412287509741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3185282515235216383346321 2388961886426412287509741)
      ·
        refine ⟨895860707409904607816153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2388961886426412287509741 895860707409904607816153)
        ·
          refine ⟨671895530557428455862115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895860707409904607816153 671895530557428455862115)
          ·
            refine ⟨1007843295836142683793173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671895530557428455862115 1007843295836142683793173)
            ·
              refine ⟨47242654492319188302805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1007843295836142683793173 47242654492319188302805)
              ·
                rfl

theorem cell19_465774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_465774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465774 prefixEnd_465774 := by exact prefixLift 465774
  have htrace : WordTrace (prefixWord ++ tailWord_465774) baseStart_465774 baseEnd_465774 := by
    simpa [prefixWord, tailWord_465774, baseEnd_465774] using wordTrace_append hprefix tailTrace_465774
  have hstable : (prefixWord ++ tailWord_465774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465774).length < 2 ^ (prefixWord ++ tailWord_465774).sum := by decide
  have hdescent : baseEnd_465774 < baseStart_465774 := by decide
  rcases family_descends (prefixWord ++ tailWord_465774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465831 : List Nat := [1, 1, 6, 1, 3, 2, 5]
def baseStart_465831 : Nat := 118140960795 + 465831 * 2 ^ 59
def prefixEnd_465831 : Nat := 4983230072969 + 3 ^ 40 * 465831 * 2
def baseEnd_465831 : Nat := 47248435904132773880531

theorem tailTrace_465831 : CollatzResearch.WordTrace tailWord_465831 prefixEnd_465831 47248435904132773880531 := by
  unfold tailWord_465831
  simp only [CollatzResearch.WordTrace]
  refine ⟨16990252375381319446005347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11326834916920879630670231 16990252375381319446005347)
  ·
    refine ⟨25485378563071979169008021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16990252375381319446005347 25485378563071979169008021)
    ·
      refine ⟨1194627120143999023547251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25485378563071979169008021 1194627120143999023547251)
      ·
        refine ⟨1791940680215998535320877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194627120143999023547251 1791940680215998535320877)
        ·
          refine ⟨671977755080999450745329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1791940680215998535320877 671977755080999450745329)
          ·
            refine ⟨503983316310749588058997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671977755080999450745329 503983316310749588058997)
            ·
              refine ⟨47248435904132773880531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 503983316310749588058997 47248435904132773880531)
              ·
                rfl

theorem cell19_465831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 5].length) (baseStart_465831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465831 prefixEnd_465831 := by exact prefixLift 465831
  have htrace : WordTrace (prefixWord ++ tailWord_465831) baseStart_465831 baseEnd_465831 := by
    simpa [prefixWord, tailWord_465831, baseEnd_465831] using wordTrace_append hprefix tailTrace_465831
  have hstable : (prefixWord ++ tailWord_465831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465831).length < 2 ^ (prefixWord ++ tailWord_465831).sum := by decide
  have hdescent : baseEnd_465831 < baseStart_465831 := by decide
  rcases family_descends (prefixWord ++ tailWord_465831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465873 : List Nat := [1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_465873 : Nat := 118140960795 + 465873 * 2 ^ 59
def prefixEnd_465873 : Nat := 4983230072969 + 3 ^ 40 * 465873 * 2
def baseEnd_465873 : Nat := 141758087675354668708145

theorem tailTrace_465873 : CollatzResearch.WordTrace tailWord_465873 prefixEnd_465873 141758087675354668708145 := by
  unfold tailWord_465873
  simp only [CollatzResearch.WordTrace]
  refine ⟨16991784241229160619034273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11327856160819440412689515 16991784241229160619034273)
  ·
    refine ⟨12743838180921870464275705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16991784241229160619034273 12743838180921870464275705)
    ·
      refine ⟨9557878635691402848206779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12743838180921870464275705 9557878635691402848206779)
      ·
        refine ⟨14336817953537104272310169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9557878635691402848206779 14336817953537104272310169)
        ·
          refine ⟨10752613465152828204232627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14336817953537104272310169 10752613465152828204232627)
          ·
            refine ⟨16128920197729242306348941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10752613465152828204232627 16128920197729242306348941)
            ·
              refine ⟨6048345074148465864880853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16128920197729242306348941 6048345074148465864880853)
              ·
                refine ⟨141758087675354668708145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6048345074148465864880853 141758087675354668708145)
                ·
                  rfl

theorem cell19_465873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_465873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465873 prefixEnd_465873 := by exact prefixLift 465873
  have htrace : WordTrace (prefixWord ++ tailWord_465873) baseStart_465873 baseEnd_465873 := by
    simpa [prefixWord, tailWord_465873, baseEnd_465873] using wordTrace_append hprefix tailTrace_465873
  have hstable : (prefixWord ++ tailWord_465873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465873).length < 2 ^ (prefixWord ++ tailWord_465873).sum := by decide
  have hdescent : baseEnd_465873 < baseStart_465873 := by decide
  rcases family_descends (prefixWord ++ tailWord_465873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465922 : List Nat := [3, 4, 1, 3, 1, 1, 3, 3]
def baseStart_465922 : Nat := 118140960795 + 465922 * 2 ^ 59
def prefixEnd_465922 : Nat := 4983230072969 + 3 ^ 40 * 465922 * 2
def baseEnd_465922 : Nat := 141772997632137073619123

theorem tailTrace_465922 : CollatzResearch.WordTrace tailWord_465922 prefixEnd_465922 141772997632137073619123 := by
  unfold tailWord_465922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248392854512910496892005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11329047612034427991712013 4248392854512910496892005)
  ·
    refine ⟨796573660221170718167251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4248392854512910496892005 796573660221170718167251)
    ·
      refine ⟨1194860490331756077250877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796573660221170718167251 1194860490331756077250877)
      ·
        refine ⟨448072683874408528969079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1194860490331756077250877 448072683874408528969079)
        ·
          refine ⟨672109025811612793453619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448072683874408528969079 672109025811612793453619)
          ·
            refine ⟨1008163538717419190180429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672109025811612793453619 1008163538717419190180429)
            ·
              refine ⟨378061327019032196317661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1008163538717419190180429 378061327019032196317661)
              ·
                refine ⟨141772997632137073619123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378061327019032196317661 141772997632137073619123)
                ·
                  rfl

theorem cell19_465922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_465922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465922 prefixEnd_465922 := by exact prefixLift 465922
  have htrace : WordTrace (prefixWord ++ tailWord_465922) baseStart_465922 baseEnd_465922 := by
    simpa [prefixWord, tailWord_465922, baseEnd_465922] using wordTrace_append hprefix tailTrace_465922
  have hstable : (prefixWord ++ tailWord_465922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465922).length < 2 ^ (prefixWord ++ tailWord_465922).sum := by decide
  have hdescent : baseEnd_465922 < baseStart_465922 := by decide
  rcases family_descends (prefixWord ++ tailWord_465922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465966 : List Nat := [4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_465966 : Nat := 118140960795 + 465966 * 2 ^ 59
def prefixEnd_465966 : Nat := 4983230072969 + 3 ^ 40 * 465966 * 2
def baseEnd_465966 : Nat := 141786386164758008641225

theorem tailTrace_465966 : CollatzResearch.WordTrace tailWord_465966 prefixEnd_465966 141786386164758008641225 := by
  unfold tailWord_465966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2124397028736529687771219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11330117486594825001446501 2124397028736529687771219)
  ·
    refine ⟨3186595543104794531656829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2124397028736529687771219 3186595543104794531656829)
    ·
      refine ⟨1194973328664297949371311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3186595543104794531656829 1194973328664297949371311)
      ·
        refine ⟨1792459992996446924056967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194973328664297949371311 1792459992996446924056967)
        ·
          refine ⟨2688689989494670386085451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1792459992996446924056967 2688689989494670386085451)
          ·
            refine ⟨4033034984242005579128177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2688689989494670386085451 4033034984242005579128177)
            ·
              refine ⟨3024776238181504184346133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4033034984242005579128177 3024776238181504184346133)
              ·
                refine ⟨141786386164758008641225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3024776238181504184346133 141786386164758008641225)
                ·
                  rfl

theorem cell19_465966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_465966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465966 prefixEnd_465966 := by exact prefixLift 465966
  have htrace : WordTrace (prefixWord ++ tailWord_465966) baseStart_465966 baseEnd_465966 := by
    simpa [prefixWord, tailWord_465966, baseEnd_465966] using wordTrace_append hprefix tailTrace_465966
  have hstable : (prefixWord ++ tailWord_465966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465966).length < 2 ^ (prefixWord ++ tailWord_465966).sum := by decide
  have hdescent : baseEnd_465966 < baseStart_465966 := by decide
  rcases family_descends (prefixWord ++ tailWord_465966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465968 : List Nat := [2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_465968 : Nat := 118140960795 + 465968 * 2 ^ 59
def prefixEnd_465968 : Nat := 4983230072969 + 3 ^ 40 * 465968 * 2
def baseEnd_465968 : Nat := 141786994734422596596775

theorem tailTrace_465968 : CollatzResearch.WordTrace tailWord_465968 prefixEnd_465968 141786994734422596596775 := by
  unfold tailWord_465968
  simp only [CollatzResearch.WordTrace]
  refine ⟨8497624587942495921871279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11330166117256661229161705 8497624587942495921871279)
  ·
    refine ⟨12746436881913743882806919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8497624587942495921871279 12746436881913743882806919)
    ·
      refine ⟨19119655322870615824210379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12746436881913743882806919 19119655322870615824210379)
      ·
        refine ⟨28679482984305923736315569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19119655322870615824210379 28679482984305923736315569)
        ·
          refine ⟨21509612238229442802236677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28679482984305923736315569 21509612238229442802236677)
          ·
            refine ⟨4033052294668020525419377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21509612238229442802236677 4033052294668020525419377)
            ·
              refine ⟨3024789221001015394064533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4033052294668020525419377 3024789221001015394064533)
              ·
                refine ⟨141786994734422596596775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3024789221001015394064533 141786994734422596596775)
                ·
                  rfl

theorem cell19_465968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_465968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465968 prefixEnd_465968 := by exact prefixLift 465968
  have htrace : WordTrace (prefixWord ++ tailWord_465968) baseStart_465968 baseEnd_465968 := by
    simpa [prefixWord, tailWord_465968, baseEnd_465968] using wordTrace_append hprefix tailTrace_465968
  have hstable : (prefixWord ++ tailWord_465968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465968).length < 2 ^ (prefixWord ++ tailWord_465968).sum := by decide
  have hdescent : baseEnd_465968 < baseStart_465968 := by decide
  rcases family_descends (prefixWord ++ tailWord_465968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_465987 : List Nat := [1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_465987 : Nat := 118140960795 + 465987 * 2 ^ 59
def prefixEnd_465987 : Nat := 4983230072969 + 3 ^ 40 * 465987 * 2
def baseEnd_465987 : Nat := 141792776146236182174501

theorem tailTrace_465987 : CollatzResearch.WordTrace tailWord_465987 prefixEnd_465987 141792776146236182174501 := by
  unfold tailWord_465987
  simp only [CollatzResearch.WordTrace]
  refine ⟨16995942162816158088684215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11330628108544105392456143 16995942162816158088684215)
  ·
    refine ⟨25493913244224237133026323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16995942162816158088684215 25493913244224237133026323)
    ·
      refine ⟨38240869866336355699539485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25493913244224237133026323 38240869866336355699539485)
      ·
        refine ⟨14340326199876133387327307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38240869866336355699539485 14340326199876133387327307)
        ·
          refine ⟨21510489299814200080990961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14340326199876133387327307 21510489299814200080990961)
          ·
            refine ⟨16132866974860650060743221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21510489299814200080990961 16132866974860650060743221)
            ·
              refine ⟨1512456278893185943194677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16132866974860650060743221 1512456278893185943194677)
              ·
                refine ⟨141792776146236182174501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1512456278893185943194677 141792776146236182174501)
                ·
                  rfl

theorem cell19_465987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_465987 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_465987 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_465987 prefixEnd_465987 := by exact prefixLift 465987
  have htrace : WordTrace (prefixWord ++ tailWord_465987) baseStart_465987 baseEnd_465987 := by
    simpa [prefixWord, tailWord_465987, baseEnd_465987] using wordTrace_append hprefix tailTrace_465987
  have hstable : (prefixWord ++ tailWord_465987).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_465987).length < 2 ^ (prefixWord ++ tailWord_465987).sum := by decide
  have hdescent : baseEnd_465987 < baseStart_465987 := by decide
  rcases family_descends (prefixWord ++ tailWord_465987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466023 : List Nat := [1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_466023 : Nat := 118140960795 + 466023 * 2 ^ 59
def prefixEnd_466023 : Nat := 4983230072969 + 3 ^ 40 * 466023 * 2
def baseEnd_466023 : Nat := 141803730400198765374403

theorem tailTrace_466023 : CollatzResearch.WordTrace tailWord_466023 prefixEnd_466023 141803730400198765374403 := by
  unfold tailWord_466023
  simp only [CollatzResearch.WordTrace]
  refine ⟨16997255190685736236994723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11331503460457157491329815 16997255190685736236994723)
  ·
    refine ⟨25495882786028604355492085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16997255190685736236994723 25495882786028604355492085)
    ·
      refine ⟨2390239011190181658327383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25495882786028604355492085 2390239011190181658327383)
      ·
        refine ⟨3585358516785272487491075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2390239011190181658327383 3585358516785272487491075)
        ·
          refine ⟨5378037775177908731236613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585358516785272487491075 5378037775177908731236613)
          ·
            refine ⟨1008382082845857887106865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5378037775177908731236613 1008382082845857887106865)
            ·
              refine ⟨756286562134393415330149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008382082845857887106865 756286562134393415330149)
              ·
                refine ⟨141803730400198765374403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 756286562134393415330149 141803730400198765374403)
                ·
                  rfl

theorem cell19_466023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_466023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466023 prefixEnd_466023 := by exact prefixLift 466023
  have htrace : WordTrace (prefixWord ++ tailWord_466023) baseStart_466023 baseEnd_466023 := by
    simpa [prefixWord, tailWord_466023, baseEnd_466023] using wordTrace_append hprefix tailTrace_466023
  have hstable : (prefixWord ++ tailWord_466023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466023).length < 2 ^ (prefixWord ++ tailWord_466023).sum := by decide
  have hdescent : baseEnd_466023 < baseStart_466023 := by decide
  rcases family_descends (prefixWord ++ tailWord_466023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466025 : List Nat := [1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_466025 : Nat := 118140960795 + 466025 * 2 ^ 59
def prefixEnd_466025 : Nat := 4983230072969 + 3 ^ 40 * 466025 * 2
def baseEnd_466025 : Nat := 141804338969863353329953

theorem tailTrace_466025 : CollatzResearch.WordTrace tailWord_466025 prefixEnd_466025 141804338969863353329953 := by
  unfold tailWord_466025
  simp only [CollatzResearch.WordTrace]
  refine ⟨16997328136678490578567529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11331552091118993719045019 16997328136678490578567529)
  ·
    refine ⟨12747996102508867933925647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16997328136678490578567529 12747996102508867933925647)
    ·
      refine ⟨19121994153763301900888471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12747996102508867933925647 19121994153763301900888471)
      ·
        refine ⟨28682991230644952851332707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19121994153763301900888471 28682991230644952851332707)
        ·
          refine ⟨43024486845967429276999061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28682991230644952851332707 43024486845967429276999061)
          ·
            refine ⟨2016772820904723247359331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43024486845967429276999061 2016772820904723247359331)
            ·
              refine ⟨3025159231357084871038997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016772820904723247359331 3025159231357084871038997)
              ·
                refine ⟨141804338969863353329953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3025159231357084871038997 141804338969863353329953)
                ·
                  rfl

theorem cell19_466025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_466025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466025 prefixEnd_466025 := by exact prefixLift 466025
  have htrace : WordTrace (prefixWord ++ tailWord_466025) baseStart_466025 baseEnd_466025 := by
    simpa [prefixWord, tailWord_466025, baseEnd_466025] using wordTrace_append hprefix tailTrace_466025
  have hstable : (prefixWord ++ tailWord_466025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466025).length < 2 ^ (prefixWord ++ tailWord_466025).sum := by decide
  have hdescent : baseEnd_466025 < baseStart_466025 := by decide
  rcases family_descends (prefixWord ++ tailWord_466025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466044 : List Nat := [2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_466044 : Nat := 118140960795 + 466044 * 2 ^ 59
def prefixEnd_466044 : Nat := 4983230072969 + 3 ^ 40 * 466044 * 2
def baseEnd_466044 : Nat := 141810120381676938907679

theorem tailTrace_466044 : CollatzResearch.WordTrace tailWord_466044 prefixEnd_466044 141810120381676938907679 := by
  unfold tailWord_466044
  simp only [CollatzResearch.WordTrace]
  refine ⟨8499010561804828411754593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11332014082406437882339457 8499010561804828411754593)
  ·
    refine ⟨6374257921353621308815945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8499010561804828411754593 6374257921353621308815945)
    ·
      refine ⟨4780693441015215981611959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6374257921353621308815945 4780693441015215981611959)
      ·
        refine ⟨7171040161522823972417939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4780693441015215981611959 7171040161522823972417939)
        ·
          refine ⟨10756560242284235958626909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7171040161522823972417939 10756560242284235958626909)
          ·
            refine ⟨4033710090856588484485091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10756560242284235958626909 4033710090856588484485091)
            ·
              refine ⟨6050565136284882726727637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4033710090856588484485091 6050565136284882726727637)
              ·
                refine ⟨141810120381676938907679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6050565136284882726727637 141810120381676938907679)
                ·
                  rfl

theorem cell19_466044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_466044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466044 prefixEnd_466044 := by exact prefixLift 466044
  have htrace : WordTrace (prefixWord ++ tailWord_466044) baseStart_466044 baseEnd_466044 := by
    simpa [prefixWord, tailWord_466044, baseEnd_466044] using wordTrace_append hprefix tailTrace_466044
  have hstable : (prefixWord ++ tailWord_466044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466044).length < 2 ^ (prefixWord ++ tailWord_466044).sum := by decide
  have hdescent : baseEnd_466044 < baseStart_466044 := by decide
  rcases family_descends (prefixWord ++ tailWord_466044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466078 : List Nat := [4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_466078 : Nat := 118140960795 + 466078 * 2 ^ 59
def prefixEnd_466078 : Nat := 4983230072969 + 3 ^ 40 * 466078 * 2
def baseEnd_466078 : Nat := 141820466065974934152031

theorem tailTrace_466078 : CollatzResearch.WordTrace tailWord_466078 prefixEnd_466078 141820466065974934152031 := by
  unfold tailWord_466078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2124907650685810078780861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11332840803657653753497925 2124907650685810078780861)
  ·
    refine ⟨796840369007178779542823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2124907650685810078780861 796840369007178779542823)
    ·
      refine ⟨1195260553510768169314235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796840369007178779542823 1195260553510768169314235)
      ·
        refine ⟨1792890830266152253971353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195260553510768169314235 1792890830266152253971353)
        ·
          refine ⟨1344668122699614190478515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1792890830266152253971353 1344668122699614190478515)
          ·
            refine ⟨2017002184049421285717773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344668122699614190478515 2017002184049421285717773)
            ·
              refine ⟨756375819018532982144165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2017002184049421285717773 756375819018532982144165)
              ·
                refine ⟨141820466065974934152031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 756375819018532982144165 141820466065974934152031)
                ·
                  rfl

theorem cell19_466078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_466078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466078 prefixEnd_466078 := by exact prefixLift 466078
  have htrace : WordTrace (prefixWord ++ tailWord_466078) baseStart_466078 baseEnd_466078 := by
    simpa [prefixWord, tailWord_466078, baseEnd_466078] using wordTrace_append hprefix tailTrace_466078
  have hstable : (prefixWord ++ tailWord_466078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466078).length < 2 ^ (prefixWord ++ tailWord_466078).sum := by decide
  have hdescent : baseEnd_466078 < baseStart_466078 := by decide
  rcases family_descends (prefixWord ++ tailWord_466078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466097 : List Nat := [1, 2, 2, 5, 1, 2, 3, 3]
def baseStart_466097 : Nat := 118140960795 + 466097 * 2 ^ 59
def prefixEnd_466097 : Nat := 4983230072969 + 3 ^ 40 * 466097 * 2
def baseEnd_466097 : Nat := 141826247477788519729757

theorem tailTrace_466097 : CollatzResearch.WordTrace tailWord_466097 prefixEnd_466097 141826247477788519729757 := by
  unfold tailWord_466097
  simp only [CollatzResearch.WordTrace]
  refine ⟨16999954192417646875188545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11333302794945097916792363 16999954192417646875188545)
  ·
    refine ⟨12749965644313235156391409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16999954192417646875188545 12749965644313235156391409)
    ·
      refine ⟨9562474233234926367293557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12749965644313235156391409 9562474233234926367293557)
      ·
        refine ⟨896481959365774346933771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9562474233234926367293557 896481959365774346933771)
        ·
          refine ⟨1344722939048661520400657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896481959365774346933771 1344722939048661520400657)
          ·
            refine ⟨1008542204286496140300493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1344722939048661520400657 1008542204286496140300493)
            ·
              refine ⟨378203326607436052612685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1008542204286496140300493 378203326607436052612685)
              ·
                refine ⟨141826247477788519729757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378203326607436052612685 141826247477788519729757)
                ·
                  rfl

theorem cell19_466097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_466097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466097 prefixEnd_466097 := by exact prefixLift 466097
  have htrace : WordTrace (prefixWord ++ tailWord_466097) baseStart_466097 baseEnd_466097 := by
    simpa [prefixWord, tailWord_466097, baseEnd_466097] using wordTrace_append hprefix tailTrace_466097
  have hstable : (prefixWord ++ tailWord_466097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466097).length < 2 ^ (prefixWord ++ tailWord_466097).sum := by decide
  have hdescent : baseEnd_466097 < baseStart_466097 := by decide
  rcases family_descends (prefixWord ++ tailWord_466097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466114 : List Nat := [3, 5, 1, 1, 2, 1, 6]
def baseStart_466114 : Nat := 118140960795 + 466114 * 2 ^ 59
def prefixEnd_466114 : Nat := 4983230072969 + 3 ^ 40 * 466114 * 2
def baseEnd_466114 : Nat := 47277140106645839117311

theorem tailTrace_466114 : CollatzResearch.WordTrace tailWord_466114 prefixEnd_466114 47277140106645839117311 := by
  unfold tailWord_466114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250143558339014694639349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11333716155570705852371597 4250143558339014694639349)
  ·
    refine ⟨398450958594282627622439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4250143558339014694639349 398450958594282627622439)
    ·
      refine ⟨597676437891423941433659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398450958594282627622439 597676437891423941433659)
      ·
        refine ⟨896514656837135912150489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597676437891423941433659 896514656837135912150489)
        ·
          refine ⟨672385992627851934112867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896514656837135912150489 672385992627851934112867)
          ·
            refine ⟨1008578988941777901169301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672385992627851934112867 1008578988941777901169301)
            ·
              refine ⟨47277140106645839117311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1008578988941777901169301 47277140106645839117311)
              ·
                rfl

theorem cell19_466114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_466114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466114 prefixEnd_466114 := by exact prefixLift 466114
  have htrace : WordTrace (prefixWord ++ tailWord_466114) baseStart_466114 baseEnd_466114 := by
    simpa [prefixWord, tailWord_466114, baseEnd_466114] using wordTrace_append hprefix tailTrace_466114
  have hstable : (prefixWord ++ tailWord_466114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466114).length < 2 ^ (prefixWord ++ tailWord_466114).sum := by decide
  have hdescent : baseEnd_466114 < baseStart_466114 := by decide
  rcases family_descends (prefixWord ++ tailWord_466114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466154 : List Nat := [3, 1, 3, 1, 1, 5, 2, 3]
def baseStart_466154 : Nat := 118140960795 + 466154 * 2 ^ 59
def prefixEnd_466154 : Nat := 4983230072969 + 3 ^ 40 * 466154 * 2
def baseEnd_466154 : Nat := 141843591713229276462935

theorem tailTrace_466154 : CollatzResearch.WordTrace tailWord_466154 prefixEnd_466154 141843591713229276462935 := by
  unfold tailWord_466154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250508288302786402503379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11334688768807430406675677 4250508288302786402503379)
  ·
    refine ⟨6375762432454179603755069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4250508288302786402503379 6375762432454179603755069)
    ·
      refine ⟨2390910912170317351408151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6375762432454179603755069 2390910912170317351408151)
      ·
        refine ⟨3586366368255476027112227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2390910912170317351408151 3586366368255476027112227)
        ·
          refine ⟨5379549552383214040668341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586366368255476027112227 5379549552383214040668341)
          ·
            refine ⟨504332770535926316312657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5379549552383214040668341 504332770535926316312657)
            ·
              refine ⟨378249577901944737234493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 504332770535926316312657 378249577901944737234493)
              ·
                refine ⟨141843591713229276462935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378249577901944737234493 141843591713229276462935)
                ·
                  rfl

theorem cell19_466154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_466154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466154 prefixEnd_466154 := by exact prefixLift 466154
  have htrace : WordTrace (prefixWord ++ tailWord_466154) baseStart_466154 baseEnd_466154 := by
    simpa [prefixWord, tailWord_466154, baseEnd_466154] using wordTrace_append hprefix tailTrace_466154
  have hstable : (prefixWord ++ tailWord_466154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466154).length < 2 ^ (prefixWord ++ tailWord_466154).sum := by decide
  have hdescent : baseEnd_466154 < baseStart_466154 := by decide
  rcases family_descends (prefixWord ++ tailWord_466154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466156 : List Nat := [2, 2, 1, 1, 2, 4, 4, 3]
def baseStart_466156 : Nat := 118140960795 + 466156 * 2 ^ 59
def prefixEnd_466156 : Nat := 4983230072969 + 3 ^ 40 * 466156 * 2
def baseEnd_466156 : Nat := 141844200282893864418485

theorem tailTrace_466156 : CollatzResearch.WordTrace tailWord_466156 prefixEnd_466156 141844200282893864418485 := by
  unfold tailWord_466156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501053049601949975793161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11334737399469266634390881 8501053049601949975793161)
  ·
    refine ⟨6375789787201462481844871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8501053049601949975793161 6375789787201462481844871)
    ·
      refine ⟨9563684680802193722767307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6375789787201462481844871 9563684680802193722767307)
      ·
        refine ⟨14345527021203290584150961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9563684680802193722767307 14345527021203290584150961)
        ·
          refine ⟨10759145265902467938113221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14345527021203290584150961 10759145265902467938113221)
          ·
            refine ⟨2017339737356712738396229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10759145265902467938113221 2017339737356712738396229)
            ·
              refine ⟨378251200754383638449293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2017339737356712738396229 378251200754383638449293)
              ·
                refine ⟨141844200282893864418485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378251200754383638449293 141844200282893864418485)
                ·
                  rfl

theorem cell19_466156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_466156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466156 prefixEnd_466156 := by exact prefixLift 466156
  have htrace : WordTrace (prefixWord ++ tailWord_466156) baseStart_466156 baseEnd_466156 := by
    simpa [prefixWord, tailWord_466156, baseEnd_466156] using wordTrace_append hprefix tailTrace_466156
  have hstable : (prefixWord ++ tailWord_466156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466156).length < 2 ^ (prefixWord ++ tailWord_466156).sum := by decide
  have hdescent : baseEnd_466156 < baseStart_466156 := by decide
  rcases family_descends (prefixWord ++ tailWord_466156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466177 : List Nat := [1, 2, 4, 1, 1, 3, 7]
def baseStart_466177 : Nat := 118140960795 + 466177 * 2 ^ 59
def prefixEnd_466177 : Nat := 4983230072969 + 3 ^ 40 * 466177 * 2
def baseEnd_466177 : Nat := 47283530088124012650587

theorem tailTrace_466177 : CollatzResearch.WordTrace tailWord_466177 prefixEnd_466177 47283530088124012650587 := by
  unfold tailWord_466177
  simp only [CollatzResearch.WordTrace]
  refine ⟨17002872032127820538100785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11335248021418547025400523 17002872032127820538100785)
  ·
    refine ⟨12752154024095865403575589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17002872032127820538100785 12752154024095865403575589)
    ·
      refine ⟨2391028879517974763170423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12752154024095865403575589 2391028879517974763170423)
      ·
        refine ⟨3586543319276962144755635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391028879517974763170423 3586543319276962144755635)
        ·
          refine ⟨5379814978915443217133453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586543319276962144755635 5379814978915443217133453)
          ·
            refine ⟨2017430617093291206425045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5379814978915443217133453 2017430617093291206425045)
            ·
              refine ⟨47283530088124012650587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2017430617093291206425045 47283530088124012650587)
              ·
                rfl

theorem cell19_466177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_466177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466177 prefixEnd_466177 := by exact prefixLift 466177
  have htrace : WordTrace (prefixWord ++ tailWord_466177) baseStart_466177 baseEnd_466177 := by
    simpa [prefixWord, tailWord_466177, baseEnd_466177] using wordTrace_append hprefix tailTrace_466177
  have hstable : (prefixWord ++ tailWord_466177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466177).length < 2 ^ (prefixWord ++ tailWord_466177).sum := by decide
  have hdescent : baseEnd_466177 < baseStart_466177 := by decide
  rcases family_descends (prefixWord ++ tailWord_466177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466230 : List Nat := [5, 1, 2, 3, 1, 7]
def baseStart_466230 : Nat := 118140960795 + 466230 * 2 ^ 59
def prefixEnd_466230 : Nat := 4983230072969 + 3 ^ 40 * 466230 * 2
def baseEnd_466230 : Nat := 15762968595609290974871

theorem tailTrace_466230 : CollatzResearch.WordTrace tailWord_466230 prefixEnd_466230 15762968595609290974871 := by
  unfold tailWord_466230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1062800318808488161861259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11336536733957207059853429 1062800318808488161861259)
  ·
    refine ⟨1594200478212732242791889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1062800318808488161861259 1594200478212732242791889)
    ·
      refine ⟨1195650358659549182093917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1594200478212732242791889 1195650358659549182093917)
      ·
        refine ⟨448368884497330943285219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1195650358659549182093917 448368884497330943285219)
        ·
          refine ⟨672553326745996414927829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448368884497330943285219 672553326745996414927829)
          ·
            refine ⟨15762968595609290974871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 672553326745996414927829 15762968595609290974871)
            ·
              rfl

theorem cell19_466230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 7].length) (baseStart_466230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466230 prefixEnd_466230 := by exact prefixLift 466230
  have htrace : WordTrace (prefixWord ++ tailWord_466230) baseStart_466230 baseEnd_466230 := by
    simpa [prefixWord, tailWord_466230, baseEnd_466230] using wordTrace_append hprefix tailTrace_466230
  have hstable : (prefixWord ++ tailWord_466230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466230).length < 2 ^ (prefixWord ++ tailWord_466230).sum := by decide
  have hdescent : baseEnd_466230 < baseStart_466230 := by decide
  rcases family_descends (prefixWord ++ tailWord_466230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466262 : List Nat := [5, 2, 3, 1, 1, 1, 3, 3]
def baseStart_466262 : Nat := 118140960795 + 466262 * 2 ^ 59
def prefixEnd_466262 : Nat := 4983230072969 + 3 ^ 40 * 466262 * 2
def baseEnd_466262 : Nat := 141876454475117026062641

theorem tailTrace_466262 : CollatzResearch.WordTrace tailWord_466262 prefixEnd_466262 141876454475117026062641 := by
  unfold tailWord_466262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1062873264801242503434065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11337314824546586703296693 1062873264801242503434065)
  ·
    refine ⟨797154948600931877575549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1062873264801242503434065 797154948600931877575549)
    ·
      refine ⟨298933105725349454090831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 797154948600931877575549 298933105725349454090831)
      ·
        refine ⟨448399658588024181136247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298933105725349454090831 448399658588024181136247)
        ·
          refine ⟨672599487882036271704371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448399658588024181136247 672599487882036271704371)
          ·
            refine ⟨1008899231823054407556557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 672599487882036271704371 1008899231823054407556557)
            ·
              refine ⟨378337211933645402833709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1008899231823054407556557 378337211933645402833709)
              ·
                refine ⟨141876454475117026062641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378337211933645402833709 141876454475117026062641)
                ·
                  rfl

theorem cell19_466262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_466262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466262 prefixEnd_466262 := by exact prefixLift 466262
  have htrace : WordTrace (prefixWord ++ tailWord_466262) baseStart_466262 baseEnd_466262 := by
    simpa [prefixWord, tailWord_466262, baseEnd_466262] using wordTrace_append hprefix tailTrace_466262
  have hstable : (prefixWord ++ tailWord_466262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466262).length < 2 ^ (prefixWord ++ tailWord_466262).sum := by decide
  have hdescent : baseEnd_466262 < baseStart_466262 := by decide
  rcases family_descends (prefixWord ++ tailWord_466262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466329 : List Nat := [1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_466329 : Nat := 118140960795 + 466329 * 2 ^ 59
def prefixEnd_466329 : Nat := 4983230072969 + 3 ^ 40 * 466329 * 2
def baseEnd_466329 : Nat := 141896841558880722573569

theorem tailTrace_466329 : CollatzResearch.WordTrace tailWord_466329 prefixEnd_466329 141896841558880722573569 := by
  unfold tailWord_466329
  simp only [CollatzResearch.WordTrace]
  refine ⟨17008415927577150497634041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11338943951718100331756027 17008415927577150497634041)
  ·
    refine ⟨12756311945682862873225531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17008415927577150497634041 12756311945682862873225531)
    ·
      refine ⟨19134467918524294309838297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12756311945682862873225531 19134467918524294309838297)
      ·
        refine ⟨14350850938893220732378723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19134467918524294309838297 14350850938893220732378723)
        ·
          refine ⟨21526276408339831098568085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14350850938893220732378723 21526276408339831098568085)
          ·
            refine ⟨1009044206640929582745379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21526276408339831098568085 1009044206640929582745379)
            ·
              refine ⟨1513566309961394374118069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1009044206640929582745379 1513566309961394374118069)
              ·
                refine ⟨141896841558880722573569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1513566309961394374118069 141896841558880722573569)
                ·
                  rfl

theorem cell19_466329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_466329 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466329 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466329 prefixEnd_466329 := by exact prefixLift 466329
  have htrace : WordTrace (prefixWord ++ tailWord_466329) baseStart_466329 baseEnd_466329 := by
    simpa [prefixWord, tailWord_466329, baseEnd_466329] using wordTrace_append hprefix tailTrace_466329
  have hstable : (prefixWord ++ tailWord_466329).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466329).length < 2 ^ (prefixWord ++ tailWord_466329).sum := by decide
  have hdescent : baseEnd_466329 < baseStart_466329 := by decide
  rcases family_descends (prefixWord ++ tailWord_466329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466344 : List Nat := [2, 1, 6, 1, 2, 2, 5]
def baseStart_466344 : Nat := 118140960795 + 466344 * 2 ^ 59
def prefixEnd_466344 : Nat := 4983230072969 + 3 ^ 40 * 466344 * 2
def baseEnd_466344 : Nat := 47300468610455044080065

theorem tailTrace_466344 : CollatzResearch.WordTrace tailWord_466344 prefixEnd_466344 47300468610455044080065 := by
  unfold tailWord_466344
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504481511261404029715043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11339308681681872039620057 8504481511261404029715043)
  ·
    refine ⟨12756722266892106044572565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504481511261404029715043 12756722266892106044572565)
    ·
      refine ⟨597971356260567470839339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12756722266892106044572565 597971356260567470839339)
      ·
        refine ⟨896957034390851206259009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 597971356260567470839339 896957034390851206259009)
        ·
          refine ⟨672717775793138404694257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 896957034390851206259009 672717775793138404694257)
          ·
            refine ⟨504538331844853803520693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672717775793138404694257 504538331844853803520693)
            ·
              refine ⟨47300468610455044080065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 504538331844853803520693 47300468610455044080065)
              ·
                rfl

theorem cell19_466344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 5].length) (baseStart_466344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466344 prefixEnd_466344 := by exact prefixLift 466344
  have htrace : WordTrace (prefixWord ++ tailWord_466344) baseStart_466344 baseEnd_466344 := by
    simpa [prefixWord, tailWord_466344, baseEnd_466344] using wordTrace_append hprefix tailTrace_466344
  have hstable : (prefixWord ++ tailWord_466344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466344).length < 2 ^ (prefixWord ++ tailWord_466344).sum := by decide
  have hdescent : baseEnd_466344 < baseStart_466344 := by decide
  rcases family_descends (prefixWord ++ tailWord_466344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466405 : List Nat := [1, 3, 1, 5, 1, 8]
def baseStart_466405 : Nat := 118140960795 + 466405 * 2 ^ 59
def prefixEnd_466405 : Nat := 4983230072969 + 3 ^ 40 * 466405 * 2
def baseEnd_466405 : Nat := 15768885245126118320497

theorem tailTrace_466405 : CollatzResearch.WordTrace tailWord_466405 prefixEnd_466405 15768885245126118320497 := by
  unfold tailWord_466405
  simp only [CollatzResearch.WordTrace]
  refine ⟨17011187875301815477400669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11340791916867876984933779 17011187875301815477400669)
  ·
    refine ⟨6379195453238180804025251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17011187875301815477400669 6379195453238180804025251)
    ·
      refine ⟨9568793179857271206037877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6379195453238180804025251 9568793179857271206037877)
      ·
        refine ⟨897074360611619175566051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9568793179857271206037877 897074360611619175566051)
        ·
          refine ⟨1345611540917428763349077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897074360611619175566051 1345611540917428763349077)
          ·
            refine ⟨15768885245126118320497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1345611540917428763349077 15768885245126118320497)
            ·
              rfl

theorem cell19_466405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 8].length) (baseStart_466405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466405 prefixEnd_466405 := by exact prefixLift 466405
  have htrace : WordTrace (prefixWord ++ tailWord_466405) baseStart_466405 baseEnd_466405 := by
    simpa [prefixWord, tailWord_466405, baseEnd_466405] using wordTrace_append hprefix tailTrace_466405
  have hstable : (prefixWord ++ tailWord_466405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466405).length < 2 ^ (prefixWord ++ tailWord_466405).sum := by decide
  have hdescent : baseEnd_466405 < baseStart_466405 := by decide
  rcases family_descends (prefixWord ++ tailWord_466405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466422 : List Nat := [5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_466422 : Nat := 118140960795 + 466422 * 2 ^ 59
def prefixEnd_466422 : Nat := 4983230072969 + 3 ^ 40 * 466422 * 2
def baseEnd_466422 : Nat := 141925140048284062506649

theorem tailTrace_466422 : CollatzResearch.WordTrace tailWord_466422 prefixEnd_466422 141925140048284062506649 := by
  unfold tailWord_466422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1063237994765014211298095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11341205277493484920513013 1063237994765014211298095)
  ·
    refine ⟨1594856992147521316947143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1063237994765014211298095 1594856992147521316947143)
    ·
      refine ⟨2392285488221281975420715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1594856992147521316947143 2392285488221281975420715)
      ·
        refine ⟨3588428232331922963131073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392285488221281975420715 3588428232331922963131073)
        ·
          refine ⟨2691321174248942222348305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3588428232331922963131073 2691321174248942222348305)
          ·
            refine ⟨2018490880686706666761229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2691321174248942222348305 2018490880686706666761229)
            ·
              refine ⟨756934080257515000035461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2018490880686706666761229 756934080257515000035461)
              ·
                refine ⟨141925140048284062506649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 756934080257515000035461 141925140048284062506649)
                ·
                  rfl

theorem cell19_466422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_466422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466422 prefixEnd_466422 := by exact prefixLift 466422
  have htrace : WordTrace (prefixWord ++ tailWord_466422) baseStart_466422 baseEnd_466422 := by
    simpa [prefixWord, tailWord_466422, baseEnd_466422] using wordTrace_append hprefix tailTrace_466422
  have hstable : (prefixWord ++ tailWord_466422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466422).length < 2 ^ (prefixWord ++ tailWord_466422).sum := by decide
  have hdescent : baseEnd_466422 < baseStart_466422 := by decide
  rcases family_descends (prefixWord ++ tailWord_466422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466424 : List Nat := [2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_466424 : Nat := 118140960795 + 466424 * 2 ^ 59
def prefixEnd_466424 : Nat := 4983230072969 + 3 ^ 40 * 466424 * 2
def baseEnd_466424 : Nat := 141925748617948650462199

theorem tailTrace_466424 : CollatzResearch.WordTrace tailWord_466424 prefixEnd_466424 141925748617948650462199 := by
  unfold tailWord_466424
  simp only [CollatzResearch.WordTrace]
  refine ⟨8505940431116490861171163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11341253908155321148228217 8505940431116490861171163)
  ·
    refine ⟨12758910646674736291756745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8505940431116490861171163 12758910646674736291756745)
    ·
      refine ⟨9569182985006052218817559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12758910646674736291756745 9569182985006052218817559)
      ·
        refine ⟨14353774477509078328226339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9569182985006052218817559 14353774477509078328226339)
        ·
          refine ⟨21530661716263617492339509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14353774477509078328226339 21530661716263617492339509)
          ·
            refine ⟨2018499535899714139906829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21530661716263617492339509 2018499535899714139906829)
            ·
              refine ⟨756937325962392802465061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2018499535899714139906829 756937325962392802465061)
              ·
                refine ⟨141925748617948650462199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 756937325962392802465061 141925748617948650462199)
                ·
                  rfl

theorem cell19_466424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_466424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466424 prefixEnd_466424 := by exact prefixLift 466424
  have htrace : WordTrace (prefixWord ++ tailWord_466424) baseStart_466424 baseEnd_466424 := by
    simpa [prefixWord, tailWord_466424, baseEnd_466424] using wordTrace_append hprefix tailTrace_466424
  have hstable : (prefixWord ++ tailWord_466424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466424).length < 2 ^ (prefixWord ++ tailWord_466424).sum := by decide
  have hdescent : baseEnd_466424 < baseStart_466424 := by decide
  rcases family_descends (prefixWord ++ tailWord_466424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466519 : List Nat := [1, 1, 3, 2, 2, 5, 5]
def baseStart_466519 : Nat := 118140960795 + 466519 * 2 ^ 59
def prefixEnd_466519 : Nat := 4983230072969 + 3 ^ 40 * 466519 * 2
def baseEnd_466519 : Nat := 47318218559005526116943

theorem tailTrace_466519 : CollatzResearch.WordTrace tailWord_466519 prefixEnd_466519 47318218559005526116943 := by
  unfold tailWord_466519
  simp only [CollatzResearch.WordTrace]
  refine ⟨17015345796888812947050611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11343563864592541964700407 17015345796888812947050611)
  ·
    refine ⟨25523018695333219420575917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17015345796888812947050611 25523018695333219420575917)
    ·
      refine ⟨9571132010749957282715969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25523018695333219420575917 9571132010749957282715969)
      ·
        refine ⟨7178349008062467962036977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9571132010749957282715969 7178349008062467962036977)
        ·
          refine ⟨5383761756046850971527733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7178349008062467962036977 5383761756046850971527733)
          ·
            refine ⟨504727664629392278580725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5383761756046850971527733 504727664629392278580725)
            ·
              refine ⟨47318218559005526116943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 504727664629392278580725 47318218559005526116943)
              ·
                rfl

theorem cell19_466519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_466519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466519 prefixEnd_466519 := by exact prefixLift 466519
  have htrace : WordTrace (prefixWord ++ tailWord_466519) baseStart_466519 baseEnd_466519 := by
    simpa [prefixWord, tailWord_466519, baseEnd_466519] using wordTrace_append hprefix tailTrace_466519
  have hstable : (prefixWord ++ tailWord_466519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466519).length < 2 ^ (prefixWord ++ tailWord_466519).sum := by decide
  have hdescent : baseEnd_466519 < baseStart_466519 := by decide
  rcases family_descends (prefixWord ++ tailWord_466519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466536 : List Nat := [2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_466536 : Nat := 118140960795 + 466536 * 2 ^ 59
def prefixEnd_466536 : Nat := 4983230072969 + 3 ^ 40 * 466536 * 2
def baseEnd_466536 : Nat := 141959828519165575973005

theorem tailTrace_466536 : CollatzResearch.WordTrace tailWord_466536 prefixEnd_466536 141959828519165575973005 := by
  unfold tailWord_466536
  simp only [CollatzResearch.WordTrace]
  refine ⟨8507982918913612425209731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11343977225218149900279641 8507982918913612425209731)
  ·
    refine ⟨12761974378370418637814597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8507982918913612425209731 12761974378370418637814597)
    ·
      refine ⟨2392870195944453494590237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12761974378370418637814597 2392870195944453494590237)
      ·
        refine ⟨897326323479170060471339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2392870195944453494590237 897326323479170060471339)
        ·
          refine ⟨1345989485218755090707009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 897326323479170060471339 1345989485218755090707009)
          ·
            refine ⟨1009492113914066318030257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1345989485218755090707009 1009492113914066318030257)
            ·
              refine ⟨757119085435549738522693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009492113914066318030257 757119085435549738522693)
              ·
                refine ⟨141959828519165575973005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 757119085435549738522693 141959828519165575973005)
                ·
                  rfl

theorem cell19_466536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_466536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466536 prefixEnd_466536 := by exact prefixLift 466536
  have htrace : WordTrace (prefixWord ++ tailWord_466536) baseStart_466536 baseEnd_466536 := by
    simpa [prefixWord, tailWord_466536, baseEnd_466536] using wordTrace_append hprefix tailTrace_466536
  have hstable : (prefixWord ++ tailWord_466536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466536).length < 2 ^ (prefixWord ++ tailWord_466536).sum := by decide
  have hdescent : baseEnd_466536 < baseStart_466536 := by decide
  rcases family_descends (prefixWord ++ tailWord_466536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466538 : List Nat := [3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_466538 : Nat := 118140960795 + 466538 * 2 ^ 59
def prefixEnd_466538 : Nat := 4983230072969 + 3 ^ 40 * 466538 * 2
def baseEnd_466538 : Nat := 141960437088830163928555

theorem tailTrace_466538 : CollatzResearch.WordTrace tailWord_466538 prefixEnd_466538 141960437088830163928555 := by
  unfold tailWord_466538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4254009695954994797998067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11344025855879986127994845 4254009695954994797998067)
  ·
    refine ⟨6381014543932492196997101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4254009695954994797998067 6381014543932492196997101)
    ·
      refine ⟨2392880453974684573873913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6381014543932492196997101 2392880453974684573873913)
      ·
        refine ⟨1794660340481013430405435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2392880453974684573873913 1794660340481013430405435)
        ·
          refine ⟨2691990510721520145608153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794660340481013430405435 2691990510721520145608153)
          ·
            refine ⟨2018992883041140109206115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2691990510721520145608153 2018992883041140109206115)
            ·
              refine ⟨3028489324561710163809173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018992883041140109206115 3028489324561710163809173)
              ·
                refine ⟨141960437088830163928555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3028489324561710163809173 141960437088830163928555)
                ·
                  rfl

theorem cell19_466538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_466538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466538 prefixEnd_466538 := by exact prefixLift 466538
  have htrace : WordTrace (prefixWord ++ tailWord_466538) baseStart_466538 baseEnd_466538 := by
    simpa [prefixWord, tailWord_466538, baseEnd_466538] using wordTrace_append hprefix tailTrace_466538
  have hstable : (prefixWord ++ tailWord_466538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466538).length < 2 ^ (prefixWord ++ tailWord_466538).sum := by decide
  have hdescent : baseEnd_466538 < baseStart_466538 := by decide
  rcases family_descends (prefixWord ++ tailWord_466538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466557 : List Nat := [1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_466557 : Nat := 118140960795 + 466557 * 2 ^ 59
def prefixEnd_466557 : Nat := 4983230072969 + 3 ^ 40 * 466557 * 2
def baseEnd_466557 : Nat := 141966218500643749506281

theorem tailTrace_466557 : CollatzResearch.WordTrace tailWord_466557 prefixEnd_466557 141966218500643749506281 := by
  unfold tailWord_466557
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016731770751145436933925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11344487847167430291289283 17016731770751145436933925)
  ·
    refine ⟨3190637207015839769425111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17016731770751145436933925 3190637207015839769425111)
    ·
      refine ⟨4785955810523759654137667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190637207015839769425111 4785955810523759654137667)
      ·
        refine ⟨7178933715785639481206501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785955810523759654137667 7178933715785639481206501)
        ·
          refine ⟨1346050071709807402726219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7178933715785639481206501 1346050071709807402726219)
          ·
            refine ⟨2019075107564711104089329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346050071709807402726219 2019075107564711104089329)
            ·
              refine ⟨1514306330673533328066997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019075107564711104089329 1514306330673533328066997)
              ·
                refine ⟨141966218500643749506281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1514306330673533328066997 141966218500643749506281)
                ·
                  rfl

theorem cell19_466557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_466557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466557 prefixEnd_466557 := by exact prefixLift 466557
  have htrace : WordTrace (prefixWord ++ tailWord_466557) baseStart_466557 baseEnd_466557 := by
    simpa [prefixWord, tailWord_466557, baseEnd_466557] using wordTrace_append hprefix tailTrace_466557
  have hstable : (prefixWord ++ tailWord_466557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466557).length < 2 ^ (prefixWord ++ tailWord_466557).sum := by decide
  have hdescent : baseEnd_466557 < baseStart_466557 := by decide
  rcases family_descends (prefixWord ++ tailWord_466557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466591 : List Nat := [1, 1, 2, 7, 1, 2, 1, 4]
def baseStart_466591 : Nat := 118140960795 + 466591 * 2 ^ 59
def prefixEnd_466591 : Nat := 4983230072969 + 3 ^ 40 * 466591 * 2
def baseEnd_466591 : Nat := 141976564184941744750633

theorem tailTrace_466591 : CollatzResearch.WordTrace tailWord_466591 prefixEnd_466591 141976564184941744750633 := by
  unfold tailWord_466591
  simp only [CollatzResearch.WordTrace]
  refine ⟨17017971852627969243671627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11345314568418646162447751 17017971852627969243671627)
  ·
    refine ⟨25526957778941953865507441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17017971852627969243671627 25526957778941953865507441)
    ·
      refine ⟨19145218334206465399130581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25526957778941953865507441 19145218334206465399130581)
      ·
        refine ⟨448716054707964032792123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19145218334206465399130581 448716054707964032792123)
        ·
          refine ⟨673074082061946049188185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448716054707964032792123 673074082061946049188185)
          ·
            refine ⟨504805561546459536891139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673074082061946049188185 504805561546459536891139)
            ·
              refine ⟨757208342319689305336709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504805561546459536891139 757208342319689305336709)
              ·
                refine ⟨141976564184941744750633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 757208342319689305336709 141976564184941744750633)
                ·
                  rfl

theorem cell19_466591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_466591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466591 prefixEnd_466591 := by exact prefixLift 466591
  have htrace : WordTrace (prefixWord ++ tailWord_466591) baseStart_466591 baseEnd_466591 := by
    simpa [prefixWord, tailWord_466591, baseEnd_466591] using wordTrace_append hprefix tailTrace_466591
  have hstable : (prefixWord ++ tailWord_466591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466591).length < 2 ^ (prefixWord ++ tailWord_466591).sum := by decide
  have hdescent : baseEnd_466591 < baseStart_466591 := by decide
  rcases family_descends (prefixWord ++ tailWord_466591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466593 : List Nat := [1, 2, 3, 3, 2, 3, 1, 4]
def baseStart_466593 : Nat := 118140960795 + 466593 * 2 ^ 59
def prefixEnd_466593 : Nat := 4983230072969 + 3 ^ 40 * 466593 * 2
def baseEnd_466593 : Nat := 141977172754606332706183

theorem tailTrace_466593 : CollatzResearch.WordTrace tailWord_466593 prefixEnd_466593 141977172754606332706183 := by
  unfold tailWord_466593
  simp only [CollatzResearch.WordTrace]
  refine ⟨17018044798620723585244433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11345363199080482390162955 17018044798620723585244433)
  ·
    refine ⟨12763533598965542688933325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17018044798620723585244433 12763533598965542688933325)
    ·
      refine ⟨4786325099612078508349997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12763533598965542688933325 4786325099612078508349997)
      ·
        refine ⟨1794871912354529440631249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4786325099612078508349997 1794871912354529440631249)
        ·
          refine ⟨1346153934265897080473437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1794871912354529440631249 1346153934265897080473437)
          ·
            refine ⟨504807725349711405177539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1346153934265897080473437 504807725349711405177539)
            ·
              refine ⟨757211588024567107766309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504807725349711405177539 757211588024567107766309)
              ·
                refine ⟨141977172754606332706183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 757211588024567107766309 141977172754606332706183)
                ·
                  rfl

theorem cell19_466593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_466593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466593 prefixEnd_466593 := by exact prefixLift 466593
  have htrace : WordTrace (prefixWord ++ tailWord_466593) baseStart_466593 baseEnd_466593 := by
    simpa [prefixWord, tailWord_466593, baseEnd_466593] using wordTrace_append hprefix tailTrace_466593
  have hstable : (prefixWord ++ tailWord_466593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466593).length < 2 ^ (prefixWord ++ tailWord_466593).sum := by decide
  have hdescent : baseEnd_466593 < baseStart_466593 := by decide
  rcases family_descends (prefixWord ++ tailWord_466593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466616 : List Nat := [2, 1, 2, 1, 2, 1, 1, 9]
def baseStart_466616 : Nat := 118140960795 + 466616 * 2 ^ 59
def prefixEnd_466616 : Nat := 4983230072969 + 3 ^ 40 * 466616 * 2
def baseEnd_466616 : Nat := 141984171305749094195009

theorem tailTrace_466616 : CollatzResearch.WordTrace tailWord_466616 prefixEnd_466616 141984171305749094195009 := by
  unfold tailWord_466616
  simp only [CollatzResearch.WordTrace]
  refine ⟨8509441838768699256665851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11345922451691599008887801 8509441838768699256665851)
  ·
    refine ⟨12764162758153048884998777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8509441838768699256665851 12764162758153048884998777)
    ·
      refine ⟨9573122068614786663749083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12764162758153048884998777 9573122068614786663749083)
      ·
        refine ⟨14359683102922179995623625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9573122068614786663749083 14359683102922179995623625)
        ·
          refine ⟨10769762327191634996717719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14359683102922179995623625 10769762327191634996717719)
          ·
            refine ⟨16154643490787452495076579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10769762327191634996717719 16154643490787452495076579)
            ·
              refine ⟨24231965236181178742614869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16154643490787452495076579 24231965236181178742614869)
              ·
                refine ⟨141984171305749094195009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24231965236181178742614869 141984171305749094195009)
                ·
                  rfl

theorem cell19_466616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_466616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466616 prefixEnd_466616 := by exact prefixLift 466616
  have htrace : WordTrace (prefixWord ++ tailWord_466616) baseStart_466616 baseEnd_466616 := by
    simpa [prefixWord, tailWord_466616, baseEnd_466616] using wordTrace_append hprefix tailTrace_466616
  have hstable : (prefixWord ++ tailWord_466616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466616).length < 2 ^ (prefixWord ++ tailWord_466616).sum := by decide
  have hdescent : baseEnd_466616 < baseStart_466616 := by decide
  rcases family_descends (prefixWord ++ tailWord_466616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466669 : List Nat := [1, 5, 1, 2, 1, 2, 4, 3]
def baseStart_466669 : Nat := 118140960795 + 466669 * 2 ^ 59
def prefixEnd_466669 : Nat := 4983230072969 + 3 ^ 40 * 466669 * 2
def baseEnd_466669 : Nat := 142000298401860675017087

theorem tailTrace_466669 : CollatzResearch.WordTrace tailWord_466669 prefixEnd_466669 142000298401860675017087 := by
  unfold tailWord_466669
  simp only [CollatzResearch.WordTrace]
  refine ⟨17020816746345388565011061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11347211164230259043340707 17020816746345388565011061)
  ·
    refine ⟨1595701569969880177969787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17020816746345388565011061 1595701569969880177969787)
    ·
      refine ⟨2393552354954820266954681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1595701569969880177969787 2393552354954820266954681)
      ·
        refine ⟨1795164266216115200216011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2393552354954820266954681 1795164266216115200216011)
        ·
          refine ⟨2692746399324172800324017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795164266216115200216011 2692746399324172800324017)
          ·
            refine ⟨2019559799493129600243013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2692746399324172800324017 2019559799493129600243013)
            ·
              refine ⟨378667462404961800045565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2019559799493129600243013 378667462404961800045565)
              ·
                refine ⟨142000298401860675017087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378667462404961800045565 142000298401860675017087)
                ·
                  rfl

theorem cell19_466669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_466669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466669 prefixEnd_466669 := by exact prefixLift 466669
  have htrace : WordTrace (prefixWord ++ tailWord_466669) baseStart_466669 baseEnd_466669 := by
    simpa [prefixWord, tailWord_466669, baseEnd_466669] using wordTrace_append hprefix tailTrace_466669
  have hstable : (prefixWord ++ tailWord_466669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466669).length < 2 ^ (prefixWord ++ tailWord_466669).sum := by decide
  have hdescent : baseEnd_466669 < baseStart_466669 := by decide
  rcases family_descends (prefixWord ++ tailWord_466669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466686 : List Nat := [4, 2, 2, 1, 4, 1, 5]
def baseStart_466686 : Nat := 118140960795 + 466686 * 2 ^ 59
def prefixEnd_466686 : Nat := 4983230072969 + 3 ^ 40 * 466686 * 2
def baseEnd_466686 : Nat := 47335157081336557546421

theorem tailTrace_466686 : CollatzResearch.WordTrace tailWord_466686 prefixEnd_466686 47335157081336557546421 := by
  unfold tailWord_466686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127679598410475058547489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11347624524855866978919941 2127679598410475058547489)
  ·
    refine ⟨1595759698807856293910617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2127679598410475058547489 1595759698807856293910617)
    ·
      refine ⟨1196819774105892220432963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1595759698807856293910617 1196819774105892220432963)
      ·
        refine ⟨1795229661158838330649445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196819774105892220432963 1795229661158838330649445)
        ·
          refine ⟨336605561467282186996771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1795229661158838330649445 336605561467282186996771)
          ·
            refine ⟨504908342200923280495157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336605561467282186996771 504908342200923280495157)
            ·
              refine ⟨47335157081336557546421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 504908342200923280495157 47335157081336557546421)
              ·
                rfl

theorem cell19_466686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 5].length) (baseStart_466686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466686 prefixEnd_466686 := by exact prefixLift 466686
  have htrace : WordTrace (prefixWord ++ tailWord_466686) baseStart_466686 baseEnd_466686 := by
    simpa [prefixWord, tailWord_466686, baseEnd_466686] using wordTrace_append hprefix tailTrace_466686
  have hstable : (prefixWord ++ tailWord_466686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466686).length < 2 ^ (prefixWord ++ tailWord_466686).sum := by decide
  have hdescent : baseEnd_466686 < baseStart_466686 := by decide
  rcases family_descends (prefixWord ++ tailWord_466686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466701 : List Nat := [1, 7, 2, 1, 1, 1, 2, 4]
def baseStart_466701 : Nat := 118140960795 + 466701 * 2 ^ 59
def prefixEnd_466701 : Nat := 4983230072969 + 3 ^ 40 * 466701 * 2
def baseEnd_466701 : Nat := 142010035516494082305889

theorem tailTrace_466701 : CollatzResearch.WordTrace tailWord_466701 prefixEnd_466701 142010035516494082305889 := by
  unfold tailWord_466701
  simp only [CollatzResearch.WordTrace]
  refine ⟨17021983882229458030175957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11347989254819638686783971 17021983882229458030175957)
  ·
    refine ⟨398952747239752922582249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17021983882229458030175957 398952747239752922582249)
    ·
      refine ⟨299214560429814691936687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398952747239752922582249 299214560429814691936687)
      ·
        refine ⟨448821840644722037905031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299214560429814691936687 448821840644722037905031)
        ·
          refine ⟨673232760967083056857547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448821840644722037905031 673232760967083056857547)
          ·
            refine ⟨1009849141450624585286321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673232760967083056857547 1009849141450624585286321)
            ·
              refine ⟨757386856087968438964741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009849141450624585286321 757386856087968438964741)
              ·
                refine ⟨142010035516494082305889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 757386856087968438964741 142010035516494082305889)
                ·
                  rfl

theorem cell19_466701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 4].length) (baseStart_466701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466701 prefixEnd_466701 := by exact prefixLift 466701
  have htrace : WordTrace (prefixWord ++ tailWord_466701) baseStart_466701 baseEnd_466701 := by
    simpa [prefixWord, tailWord_466701, baseEnd_466701] using wordTrace_append hprefix tailTrace_466701
  have hstable : (prefixWord ++ tailWord_466701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466701).length < 2 ^ (prefixWord ++ tailWord_466701).sum := by decide
  have hdescent : baseEnd_466701 < baseStart_466701 := by decide
  rcases family_descends (prefixWord ++ tailWord_466701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466709 : List Nat := [1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_466709 : Nat := 118140960795 + 466709 * 2 ^ 59
def prefixEnd_466709 : Nat := 4983230072969 + 3 ^ 40 * 466709 * 2
def baseEnd_466709 : Nat := 142012469795152434128089

theorem tailTrace_466709 : CollatzResearch.WordTrace tailWord_466709 prefixEnd_466709 142012469795152434128089 := by
  unfold tailWord_466709
  simp only [CollatzResearch.WordTrace]
  refine ⟨17022275666200475396467181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11348183777466983597644787 17022275666200475396467181)
  ·
    refine ⟨6383353374825178273675193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17022275666200475396467181 6383353374825178273675193)
    ·
      refine ⟨4787515031118883705256395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6383353374825178273675193 4787515031118883705256395)
      ·
        refine ⟨7181272546678325557884593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787515031118883705256395 7181272546678325557884593)
        ·
          refine ⟨5385954410008744168413445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7181272546678325557884593 5385954410008744168413445)
          ·
            refine ⟨1009866451876639531577521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5385954410008744168413445 1009866451876639531577521)
            ·
              refine ⟨757399838907479648683141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009866451876639531577521 757399838907479648683141)
              ·
                refine ⟨142012469795152434128089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 757399838907479648683141 142012469795152434128089)
                ·
                  rfl

theorem cell19_466709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_466709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466709 prefixEnd_466709 := by exact prefixLift 466709
  have htrace : WordTrace (prefixWord ++ tailWord_466709) baseStart_466709 baseEnd_466709 := by
    simpa [prefixWord, tailWord_466709, baseEnd_466709] using wordTrace_append hprefix tailTrace_466709
  have hstable : (prefixWord ++ tailWord_466709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466709).length < 2 ^ (prefixWord ++ tailWord_466709).sum := by decide
  have hdescent : baseEnd_466709 < baseStart_466709 := by decide
  rcases family_descends (prefixWord ++ tailWord_466709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466728 : List Nat := [2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_466728 : Nat := 118140960795 + 466728 * 2 ^ 59
def prefixEnd_466728 : Nat := 4983230072969 + 3 ^ 40 * 466728 * 2
def baseEnd_466728 : Nat := 142018251206966019705815

theorem tailTrace_466728 : CollatzResearch.WordTrace tailWord_466728 prefixEnd_466728 142018251206966019705815 := by
  unfold tailWord_466728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511484326565820820704419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11348645768754427760939225 8511484326565820820704419)
  ·
    refine ⟨12767226489848731231056629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8511484326565820820704419 12767226489848731231056629)
    ·
      refine ⟨1196927483423318552911559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12767226489848731231056629 1196927483423318552911559)
      ·
        refine ⟨1795391225134977829367339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1196927483423318552911559 1795391225134977829367339)
        ·
          refine ⟨2693086837702466744051009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795391225134977829367339 2693086837702466744051009)
          ·
            refine ⟨2019815128276850058038257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2693086837702466744051009 2019815128276850058038257)
            ·
              refine ⟨1514861346207637543528693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019815128276850058038257 1514861346207637543528693)
              ·
                refine ⟨142018251206966019705815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1514861346207637543528693 142018251206966019705815)
                ·
                  rfl

theorem cell19_466728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_466728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466728 prefixEnd_466728 := by exact prefixLift 466728
  have htrace : WordTrace (prefixWord ++ tailWord_466728) baseStart_466728 baseEnd_466728 := by
    simpa [prefixWord, tailWord_466728, baseEnd_466728] using wordTrace_append hprefix tailTrace_466728
  have hstable : (prefixWord ++ tailWord_466728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466728).length < 2 ^ (prefixWord ++ tailWord_466728).sum := by decide
  have hdescent : baseEnd_466728 < baseStart_466728 := by decide
  rcases family_descends (prefixWord ++ tailWord_466728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466745 : List Nat := [1, 2, 1, 7, 2, 6]
def baseStart_466745 : Nat := 118140960795 + 466745 * 2 ^ 59
def prefixEnd_466745 : Nat := 4983230072969 + 3 ^ 40 * 466745 * 2
def baseEnd_466745 : Nat := 15780380449901668591999

theorem tailTrace_466745 : CollatzResearch.WordTrace tailWord_466745 prefixEnd_466745 15780380449901668591999 := by
  unfold tailWord_466745
  simp only [CollatzResearch.WordTrace]
  refine ⟨17023588694070053544777689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11349059129380035696518459 17023588694070053544777689)
  ·
    refine ⟨12767691520552540158583267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17023588694070053544777689 12767691520552540158583267)
    ·
      refine ⟨19151537280828810237874901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12767691520552540158583267 19151537280828810237874901)
      ·
        refine ⟨448864155019425239950193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19151537280828810237874901 448864155019425239950193)
        ·
          refine ⟨336648116264568929962645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448864155019425239950193 336648116264568929962645)
          ·
            refine ⟨15780380449901668591999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 336648116264568929962645 15780380449901668591999)
            ·
              rfl

theorem cell19_466745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 6].length) (baseStart_466745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466745 prefixEnd_466745 := by exact prefixLift 466745
  have htrace : WordTrace (prefixWord ++ tailWord_466745) baseStart_466745 baseEnd_466745 := by
    simpa [prefixWord, tailWord_466745, baseEnd_466745] using wordTrace_append hprefix tailTrace_466745
  have hstable : (prefixWord ++ tailWord_466745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466745).length < 2 ^ (prefixWord ++ tailWord_466745).sum := by decide
  have hdescent : baseEnd_466745 < baseStart_466745 := by decide
  rcases family_descends (prefixWord ++ tailWord_466745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466764 : List Nat := [2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_466764 : Nat := 118140960795 + 466764 * 2 ^ 59
def prefixEnd_466764 : Nat := 4983230072969 + 3 ^ 40 * 466764 * 2
def baseEnd_466764 : Nat := 142029205460928602905717

theorem tailTrace_466764 : CollatzResearch.WordTrace tailWord_466764 prefixEnd_466764 142029205460928602905717 := by
  unfold tailWord_466764
  simp only [CollatzResearch.WordTrace]
  refine ⟨8512140840500609894859673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11349521120667479859812897 8512140840500609894859673)
  ·
    refine ⟨6384105630375457421144755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8512140840500609894859673 6384105630375457421144755)
    ·
      refine ⟨9576158445563186131717133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6384105630375457421144755 9576158445563186131717133)
      ·
        refine ⟨3591059417086194799393925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9576158445563186131717133 3591059417086194799393925)
        ·
          refine ⟨673323640703661524886361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3591059417086194799393925 673323640703661524886361)
          ·
            refine ⟨504992730527746143664771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673323640703661524886361 504992730527746143664771)
            ·
              refine ⟨757489095791619215497157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504992730527746143664771 757489095791619215497157)
              ·
                refine ⟨142029205460928602905717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 757489095791619215497157 142029205460928602905717)
                ·
                  rfl

theorem cell19_466764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_466764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466764 prefixEnd_466764 := by exact prefixLift 466764
  have htrace : WordTrace (prefixWord ++ tailWord_466764) baseStart_466764 baseEnd_466764 := by
    simpa [prefixWord, tailWord_466764, baseEnd_466764] using wordTrace_append hprefix tailTrace_466764
  have hstable : (prefixWord ++ tailWord_466764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466764).length < 2 ^ (prefixWord ++ tailWord_466764).sum := by decide
  have hdescent : baseEnd_466764 < baseStart_466764 := by decide
  rcases family_descends (prefixWord ++ tailWord_466764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466785 : List Nat := [1, 2, 3, 1, 1, 1, 7, 3]
def baseStart_466785 : Nat := 118140960795 + 466785 * 2 ^ 59
def prefixEnd_466785 : Nat := 4983230072969 + 3 ^ 40 * 466785 * 2
def baseEnd_466785 : Nat := 142035595442406776438993

theorem tailTrace_466785 : CollatzResearch.WordTrace tailWord_466785 prefixEnd_466785 142035595442406776438993 := by
  unfold tailWord_466785
  simp only [CollatzResearch.WordTrace]
  refine ⟨17025047613925140376233809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11350031742616760250822539 17025047613925140376233809)
  ·
    refine ⟨12768785710443855282175357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17025047613925140376233809 12768785710443855282175357)
    ·
      refine ⟨4788294641416445730815759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12768785710443855282175357 4788294641416445730815759)
      ·
        refine ⟨7182441962124668596223639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4788294641416445730815759 7182441962124668596223639)
        ·
          refine ⟨10773662943187002894335459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7182441962124668596223639 10773662943187002894335459)
          ·
            refine ⟨16160494414780504341503189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10773662943187002894335459 16160494414780504341503189)
            ·
              refine ⟨378761587846418070503981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16160494414780504341503189 378761587846418070503981)
              ·
                refine ⟨142035595442406776438993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378761587846418070503981 142035595442406776438993)
                ·
                  rfl

theorem cell19_466785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_466785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466785 prefixEnd_466785 := by exact prefixLift 466785
  have htrace : WordTrace (prefixWord ++ tailWord_466785) baseStart_466785 baseEnd_466785 := by
    simpa [prefixWord, tailWord_466785, baseEnd_466785] using wordTrace_append hprefix tailTrace_466785
  have hstable : (prefixWord ++ tailWord_466785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466785).length < 2 ^ (prefixWord ++ tailWord_466785).sum := by decide
  have hdescent : baseEnd_466785 < baseStart_466785 := by decide
  rcases family_descends (prefixWord ++ tailWord_466785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466825 : List Nat := [1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_466825 : Nat := 118140960795 + 466825 * 2 ^ 59
def prefixEnd_466825 : Nat := 4983230072969 + 3 ^ 40 * 466825 * 2
def baseEnd_466825 : Nat := 142047766835698535549995

theorem tailTrace_466825 : CollatzResearch.WordTrace tailWord_466825 prefixEnd_466825 142047766835698535549995 := by
  unfold tailWord_466825
  simp only [CollatzResearch.WordTrace]
  refine ⟨17026506533780227207689929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11351004355853484805126619 17026506533780227207689929)
  ·
    refine ⟨12769879900335170405767447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17026506533780227207689929 12769879900335170405767447)
    ·
      refine ⟨19154819850502755608651171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12769879900335170405767447 19154819850502755608651171)
      ·
        refine ⟨28732229775754133412976757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19154819850502755608651171 28732229775754133412976757)
        ·
          refine ⟨2693646541476950007466571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28732229775754133412976757 2693646541476950007466571)
          ·
            refine ⟨4040469812215425011199857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693646541476950007466571 4040469812215425011199857)
            ·
              refine ⟨3030352359161568758399893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4040469812215425011199857 3030352359161568758399893)
              ·
                refine ⟨142047766835698535549995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3030352359161568758399893 142047766835698535549995)
                ·
                  rfl

theorem cell19_466825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_466825 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466825 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466825 prefixEnd_466825 := by exact prefixLift 466825
  have htrace : WordTrace (prefixWord ++ tailWord_466825) baseStart_466825 baseEnd_466825 := by
    simpa [prefixWord, tailWord_466825, baseEnd_466825] using wordTrace_append hprefix tailTrace_466825
  have hstable : (prefixWord ++ tailWord_466825).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466825).length < 2 ^ (prefixWord ++ tailWord_466825).sum := by decide
  have hdescent : baseEnd_466825 < baseStart_466825 := by decide
  rcases family_descends (prefixWord ++ tailWord_466825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466840 : List Nat := [2, 1, 2, 6, 1, 1, 1, 5]
def baseStart_466840 : Nat := 118140960795 + 466840 * 2 ^ 59
def prefixEnd_466840 : Nat := 4983230072969 + 3 ^ 40 * 466840 * 2
def baseEnd_466840 : Nat := 142052331108182945216621

theorem tailTrace_466840 : CollatzResearch.WordTrace tailWord_466840 prefixEnd_466840 142052331108182945216621 := by
  unfold tailWord_466840
  simp only [CollatzResearch.WordTrace]
  refine ⟨8513526814362942384742987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11351369085817256512990649 8513526814362942384742987)
  ·
    refine ⟨12770290221544413577114481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8513526814362942384742987 12770290221544413577114481)
    ·
      refine ⟨9577717666158310182835861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12770290221544413577114481 9577717666158310182835861)
      ·
        refine ⟨448955515601170789820431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9577717666158310182835861 448955515601170789820431)
        ·
          refine ⟨673433273401756184730647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448955515601170789820431 673433273401756184730647)
          ·
            refine ⟨1010149910102634277095971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673433273401756184730647 1010149910102634277095971)
            ·
              refine ⟨1515224865153951415643957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010149910102634277095971 1515224865153951415643957)
              ·
                refine ⟨142052331108182945216621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1515224865153951415643957 142052331108182945216621)
                ·
                  rfl

theorem cell19_466840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_466840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466840 prefixEnd_466840 := by exact prefixLift 466840
  have htrace : WordTrace (prefixWord ++ tailWord_466840) baseStart_466840 baseEnd_466840 := by
    simpa [prefixWord, tailWord_466840, baseEnd_466840] using wordTrace_append hprefix tailTrace_466840
  have hstable : (prefixWord ++ tailWord_466840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466840).length < 2 ^ (prefixWord ++ tailWord_466840).sum := by decide
  have hdescent : baseEnd_466840 < baseStart_466840 := by decide
  rcases family_descends (prefixWord ++ tailWord_466840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466842 : List Nat := [3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_466842 : Nat := 118140960795 + 466842 * 2 ^ 59
def prefixEnd_466842 : Nat := 4983230072969 + 3 ^ 40 * 466842 * 2
def baseEnd_466842 : Nat := 142052939677847533172171

theorem tailTrace_466842 : CollatzResearch.WordTrace tailWord_466842 prefixEnd_466842 142052939677847533172171 := by
  unfold tailWord_466842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256781643679659777764695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11351417716479092740705853 4256781643679659777764695)
  ·
    refine ⟨6385172465519489666647043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4256781643679659777764695 6385172465519489666647043)
    ·
      refine ⟨9577758698279234499970565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6385172465519489666647043 9577758698279234499970565)
      ·
        refine ⟨1795829755927356468744481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9577758698279234499970565 1795829755927356468744481)
        ·
          refine ⟨1346872316945517351558361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1795829755927356468744481 1346872316945517351558361)
          ·
            refine ⟨1010154237709138013668771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1346872316945517351558361 1010154237709138013668771)
            ·
              refine ⟨1515231356563707020503157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010154237709138013668771 1515231356563707020503157)
              ·
                refine ⟨142052939677847533172171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1515231356563707020503157 142052939677847533172171)
                ·
                  rfl

theorem cell19_466842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_466842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466842 prefixEnd_466842 := by exact prefixLift 466842
  have htrace : WordTrace (prefixWord ++ tailWord_466842) baseStart_466842 baseEnd_466842 := by
    simpa [prefixWord, tailWord_466842, baseEnd_466842] using wordTrace_append hprefix tailTrace_466842
  have hstable : (prefixWord ++ tailWord_466842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466842).length < 2 ^ (prefixWord ++ tailWord_466842).sum := by decide
  have hdescent : baseEnd_466842 < baseStart_466842 := by decide
  rcases family_descends (prefixWord ++ tailWord_466842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466937 : List Nat := [1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_466937 : Nat := 118140960795 + 466937 * 2 ^ 59
def prefixEnd_466937 : Nat := 4983230072969 + 3 ^ 40 * 466937 * 2
def baseEnd_466937 : Nat := 142081846736915461060801

theorem tailTrace_466937 : CollatzResearch.WordTrace tailWord_466937 prefixEnd_466937 142081846736915461060801 := by
  unfold tailWord_466937
  simp only [CollatzResearch.WordTrace]
  refine ⟨17030591509374470335767065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11353727672916313557178043 17030591509374470335767065)
  ·
    refine ⟨12772943632030852751825299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17030591509374470335767065 12772943632030852751825299)
    ·
      refine ⟨19159415448046279127737949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12772943632030852751825299 19159415448046279127737949)
      ·
        refine ⟨7184780793017354672901731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19159415448046279127737949 7184780793017354672901731)
        ·
          refine ⟨10777171189526032009352597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7184780793017354672901731 10777171189526032009352597)
          ·
            refine ⟨505179899509032750438403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10777171189526032009352597 505179899509032750438403)
            ·
              refine ⟨757769849263549125657605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505179899509032750438403 757769849263549125657605)
              ·
                refine ⟨142081846736915461060801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 757769849263549125657605 142081846736915461060801)
                ·
                  rfl

theorem cell19_466937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_466937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466937 prefixEnd_466937 := by exact prefixLift 466937
  have htrace : WordTrace (prefixWord ++ tailWord_466937) baseStart_466937 baseEnd_466937 := by
    simpa [prefixWord, tailWord_466937, baseEnd_466937] using wordTrace_append hprefix tailTrace_466937
  have hstable : (prefixWord ++ tailWord_466937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466937).length < 2 ^ (prefixWord ++ tailWord_466937).sum := by decide
  have hdescent : baseEnd_466937 < baseStart_466937 := by decide
  rcases family_descends (prefixWord ++ tailWord_466937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466939 : List Nat := [1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_466939 : Nat := 118140960795 + 466939 * 2 ^ 59
def prefixEnd_466939 : Nat := 4983230072969 + 3 ^ 40 * 466939 * 2
def baseEnd_466939 : Nat := 142082455306580049016351

theorem tailTrace_466939 : CollatzResearch.WordTrace tailWord_466939 prefixEnd_466939 142082455306580049016351 := by
  unfold tailWord_466939
  simp only [CollatzResearch.WordTrace]
  refine ⟨17030664455367224677339871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11353776303578149784893247 17030664455367224677339871)
  ·
    refine ⟨25545996683050837016009807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17030664455367224677339871 25545996683050837016009807)
    ·
      refine ⟨38318995024576255524014711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25545996683050837016009807 38318995024576255524014711)
      ·
        refine ⟨57478492536864383286022067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38318995024576255524014711 57478492536864383286022067)
        ·
          refine ⟨86217738805296574929033101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57478492536864383286022067 86217738805296574929033101)
          ·
            refine ⟨32331652051986215598387413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86217738805296574929033101 32331652051986215598387413)
            ·
              refine ⟨757773094968426928087205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32331652051986215598387413 757773094968426928087205)
              ·
                refine ⟨142082455306580049016351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 757773094968426928087205 142082455306580049016351)
                ·
                  rfl

theorem cell19_466939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_466939 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466939 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466939 prefixEnd_466939 := by exact prefixLift 466939
  have htrace : WordTrace (prefixWord ++ tailWord_466939) baseStart_466939 baseEnd_466939 := by
    simpa [prefixWord, tailWord_466939, baseEnd_466939] using wordTrace_append hprefix tailTrace_466939
  have hstable : (prefixWord ++ tailWord_466939).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466939).length < 2 ^ (prefixWord ++ tailWord_466939).sum := by decide
  have hdescent : baseEnd_466939 < baseStart_466939 := by decide
  rcases family_descends (prefixWord ++ tailWord_466939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466954 : List Nat := [3, 1, 2, 2, 4, 1, 3, 3]
def baseStart_466954 : Nat := 118140960795 + 466954 * 2 ^ 59
def prefixEnd_466954 : Nat := 4983230072969 + 3 ^ 40 * 466954 * 2
def baseEnd_466954 : Nat := 142087019579064458682977

theorem tailTrace_466954 : CollatzResearch.WordTrace tailWord_466954 prefixEnd_466954 142087019579064458682977 := by
  unfold tailWord_466954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257802887578220559783979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11354141033541921492757277 4257802887578220559783979)
  ·
    refine ⟨6386704331367330839675969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4257802887578220559783979 6386704331367330839675969)
    ·
      refine ⟨4790028248525498129756977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6386704331367330839675969 4790028248525498129756977)
      ·
        refine ⟨3592521186394123597317733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4790028248525498129756977 3592521186394123597317733)
        ·
          refine ⟨673597722448898174497075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3592521186394123597317733 673597722448898174497075)
          ·
            refine ⟨1010396583673347261745613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673597722448898174497075 1010396583673347261745613)
            ·
              refine ⟨378898718877505223154605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1010396583673347261745613 378898718877505223154605)
              ·
                refine ⟨142087019579064458682977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378898718877505223154605 142087019579064458682977)
                ·
                  rfl

theorem cell19_466954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_466954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466954 prefixEnd_466954 := by exact prefixLift 466954
  have htrace : WordTrace (prefixWord ++ tailWord_466954) baseStart_466954 baseEnd_466954 := by
    simpa [prefixWord, tailWord_466954, baseEnd_466954] using wordTrace_append hprefix tailTrace_466954
  have hstable : (prefixWord ++ tailWord_466954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466954).length < 2 ^ (prefixWord ++ tailWord_466954).sum := by decide
  have hdescent : baseEnd_466954 < baseStart_466954 := by decide
  rcases family_descends (prefixWord ++ tailWord_466954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_466956 : List Nat := [2, 2, 1, 2, 3, 1, 5, 3]
def baseStart_466956 : Nat := 118140960795 + 466956 * 2 ^ 59
def prefixEnd_466956 : Nat := 4983230072969 + 3 ^ 40 * 466956 * 2
def baseEnd_466956 : Nat := 142087628148729046638527

theorem tailTrace_466956 : CollatzResearch.WordTrace tailWord_466956 prefixEnd_466956 142087628148729046638527 := by
  unfold tailWord_466956
  simp only [CollatzResearch.WordTrace]
  refine ⟨8515642248152818290354361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11354189664203757720472481 8515642248152818290354361)
  ·
    refine ⟨6386731686114613717765771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8515642248152818290354361 6386731686114613717765771)
    ·
      refine ⟨9580097529171920576648657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6386731686114613717765771 9580097529171920576648657)
      ·
        refine ⟨7185073146878940432486493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9580097529171920576648657 7185073146878940432486493)
        ·
          refine ⟨2694402430079602662182435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7185073146878940432486493 2694402430079602662182435)
          ·
            refine ⟨4041603645119403993273653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694402430079602662182435 4041603645119403993273653)
            ·
              refine ⟨378900341729944124369405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4041603645119403993273653 378900341729944124369405)
              ·
                refine ⟨142087628148729046638527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378900341729944124369405 142087628148729046638527)
                ·
                  rfl

theorem cell19_466956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_466956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_466956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_466956 prefixEnd_466956 := by exact prefixLift 466956
  have htrace : WordTrace (prefixWord ++ tailWord_466956) baseStart_466956 baseEnd_466956 := by
    simpa [prefixWord, tailWord_466956, baseEnd_466956] using wordTrace_append hprefix tailTrace_466956
  have hstable : (prefixWord ++ tailWord_466956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_466956).length < 2 ^ (prefixWord ++ tailWord_466956).sum := by decide
  have hdescent : baseEnd_466956 < baseStart_466956 := by decide
  rcases family_descends (prefixWord ++ tailWord_466956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467015 : List Nat := [1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_467015 : Nat := 118140960795 + 467015 * 2 ^ 59
def prefixEnd_467015 : Nat := 4983230072969 + 3 ^ 40 * 467015 * 2
def baseEnd_467015 : Nat := 142105580953834391327255

theorem tailTrace_467015 : CollatzResearch.WordTrace tailWord_467015 prefixEnd_467015 142105580953834391327255 := by
  unfold tailWord_467015
  simp only [CollatzResearch.WordTrace]
  refine ⟨17033436403091889657106499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11355624268727926438070999 17033436403091889657106499)
  ·
    refine ⟨25550154604637834485659749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17033436403091889657106499 25550154604637834485659749)
    ·
      refine ⟨4790653988369593966061203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25550154604637834485659749 4790653988369593966061203)
      ·
        refine ⟨7185980982554390949091805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4790653988369593966061203 7185980982554390949091805)
        ·
          refine ⟨2694742868457896605909427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7185980982554390949091805 2694742868457896605909427)
          ·
            refine ⟨4042114302686844908864141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2694742868457896605909427 4042114302686844908864141)
            ·
              refine ⟨1515792863507566840824053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4042114302686844908864141 1515792863507566840824053)
              ·
                refine ⟨142105580953834391327255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1515792863507566840824053 142105580953834391327255)
                ·
                  rfl

theorem cell19_467015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_467015 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467015 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467015 prefixEnd_467015 := by exact prefixLift 467015
  have htrace : WordTrace (prefixWord ++ tailWord_467015) baseStart_467015 baseEnd_467015 := by
    simpa [prefixWord, tailWord_467015, baseEnd_467015] using wordTrace_append hprefix tailTrace_467015
  have hstable : (prefixWord ++ tailWord_467015).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467015).length < 2 ^ (prefixWord ++ tailWord_467015).sum := by decide
  have hdescent : baseEnd_467015 < baseStart_467015 := by decide
  rcases family_descends (prefixWord ++ tailWord_467015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467030 : List Nat := [5, 2, 2, 1, 1, 1, 7]
def baseStart_467030 : Nat := 118140960795 + 467030 * 2 ^ 59
def prefixEnd_467030 : Nat := 4983230072969 + 3 ^ 40 * 467030 * 2
def baseEnd_467030 : Nat := 47370048408772933664627

theorem tailTrace_467030 : CollatzResearch.WordTrace tailWord_467030 prefixEnd_467030 47370048408772933664627 := by
  unfold tailWord_467030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064623968627346701181409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11355988998691698145935029 1064623968627346701181409)
  ·
    refine ⟨798467976470510025886057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1064623968627346701181409 798467976470510025886057)
    ·
      refine ⟨598850982352882519414543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798467976470510025886057 598850982352882519414543)
      ·
        refine ⟨898276473529323779121815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 598850982352882519414543 898276473529323779121815)
        ·
          refine ⟨1347414710293985668682723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898276473529323779121815 1347414710293985668682723)
          ·
            refine ⟨2021122065440978503024085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347414710293985668682723 2021122065440978503024085)
            ·
              refine ⟨47370048408772933664627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2021122065440978503024085 47370048408772933664627)
              ·
                rfl

theorem cell19_467030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_467030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467030 prefixEnd_467030 := by exact prefixLift 467030
  have htrace : WordTrace (prefixWord ++ tailWord_467030) baseStart_467030 baseEnd_467030 := by
    simpa [prefixWord, tailWord_467030, baseEnd_467030] using wordTrace_append hprefix tailTrace_467030
  have hstable : (prefixWord ++ tailWord_467030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467030).length < 2 ^ (prefixWord ++ tailWord_467030).sum := by decide
  have hdescent : baseEnd_467030 < baseStart_467030 := by decide
  rcases family_descends (prefixWord ++ tailWord_467030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467106 : List Nat := [3, 3, 1, 3, 1, 3, 1, 4]
def baseStart_467106 : Nat := 118140960795 + 467106 * 2 ^ 59
def prefixEnd_467106 : Nat := 4983230072969 + 3 ^ 40 * 467106 * 2
def baseEnd_467106 : Nat := 142133270873573143304785

theorem tailTrace_467106 : CollatzResearch.WordTrace tailWord_467106 prefixEnd_467106 142133270873573143304785 := by
  unfold tailWord_467106
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259188861440553049667293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11357836963841474799112781 4259188861440553049667293)
  ·
    refine ⟨1597195823040207393625235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4259188861440553049667293 1597195823040207393625235)
    ·
      refine ⟨2395793734560311090437853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597195823040207393625235 2395793734560311090437853)
      ·
        refine ⟨898422650460116658914195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2395793734560311090437853 898422650460116658914195)
        ·
          refine ⟨1347633975690174988371293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898422650460116658914195 1347633975690174988371293)
          ·
            refine ⟨505362740883815620639235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1347633975690174988371293 505362740883815620639235)
            ·
              refine ⟨758044111325723430958853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505362740883815620639235 758044111325723430958853)
              ·
                refine ⟨142133270873573143304785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758044111325723430958853 142133270873573143304785)
                ·
                  rfl

theorem cell19_467106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_467106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467106 prefixEnd_467106 := by exact prefixLift 467106
  have htrace : WordTrace (prefixWord ++ tailWord_467106) baseStart_467106 baseEnd_467106 := by
    simpa [prefixWord, tailWord_467106, baseEnd_467106] using wordTrace_append hprefix tailTrace_467106
  have hstable : (prefixWord ++ tailWord_467106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467106).length < 2 ^ (prefixWord ++ tailWord_467106).sum := by decide
  have hdescent : baseEnd_467106 < baseStart_467106 := by decide
  rcases family_descends (prefixWord ++ tailWord_467106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467127 : List Nat := [1, 1, 3, 1, 4, 3, 3, 3]
def baseStart_467127 : Nat := 118140960795 + 467127 * 2 ^ 59
def prefixEnd_467127 : Nat := 4983230072969 + 3 ^ 40 * 467127 * 2
def baseEnd_467127 : Nat := 142139660855051316838061

theorem tailTrace_467127 : CollatzResearch.WordTrace tailWord_467127 prefixEnd_467127 142139660855051316838061 := by
  unfold tailWord_467127
  simp only [CollatzResearch.WordTrace]
  refine ⟨17037521378686132785183635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11358347585790755190122423 17037521378686132785183635)
  ·
    refine ⟨25556282068029199177775453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17037521378686132785183635 25556282068029199177775453)
    ·
      refine ⟨9583605775510949691665795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25556282068029199177775453 9583605775510949691665795)
      ·
        refine ⟨14375408663266424537498693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9583605775510949691665795 14375408663266424537498693)
        ·
          refine ⟨2695389124362454600781005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14375408663266424537498693 2695389124362454600781005)
          ·
            refine ⟨1010770921635920475292877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2695389124362454600781005 1010770921635920475292877)
            ·
              refine ⟨379039095613470178234829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1010770921635920475292877 379039095613470178234829)
              ·
                refine ⟨142139660855051316838061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379039095613470178234829 142139660855051316838061)
                ·
                  rfl

theorem cell19_467127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_467127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467127 prefixEnd_467127 := by exact prefixLift 467127
  have htrace : WordTrace (prefixWord ++ tailWord_467127) baseStart_467127 baseEnd_467127 := by
    simpa [prefixWord, tailWord_467127, baseEnd_467127] using wordTrace_append hprefix tailTrace_467127
  have hstable : (prefixWord ++ tailWord_467127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467127).length < 2 ^ (prefixWord ++ tailWord_467127).sum := by decide
  have hdescent : baseEnd_467127 < baseStart_467127 := by decide
  rcases family_descends (prefixWord ++ tailWord_467127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467224 : List Nat := [2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_467224 : Nat := 118140960795 + 467224 * 2 ^ 59
def prefixEnd_467224 : Nat := 4983230072969 + 3 ^ 40 * 467224 * 2
def baseEnd_467224 : Nat := 142169176483783832682241

theorem tailTrace_467224 : CollatzResearch.WordTrace tailWord_467224 prefixEnd_467224 142169176483783832682241 := by
  unfold tailWord_467224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8520529629667359175732363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11360706172889812234309817 8520529629667359175732363)
  ·
    refine ⟨12780794444501038763598545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8520529629667359175732363 12780794444501038763598545)
    ·
      refine ⟨9585595833375779072698909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12780794444501038763598545 9585595833375779072698909)
      ·
        refine ⟨3594598437515917152262091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9585595833375779072698909 3594598437515917152262091)
        ·
          refine ⟨5391897656273875728393137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594598437515917152262091 5391897656273875728393137)
          ·
            refine ⟨4043923242205406796294853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5391897656273875728393137 4043923242205406796294853)
            ·
              refine ⟨758235607913513774305285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4043923242205406796294853 758235607913513774305285)
              ·
                refine ⟨142169176483783832682241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758235607913513774305285 142169176483783832682241)
                ·
                  rfl

theorem cell19_467224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_467224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467224 prefixEnd_467224 := by exact prefixLift 467224
  have htrace : WordTrace (prefixWord ++ tailWord_467224) baseStart_467224 baseEnd_467224 := by
    simpa [prefixWord, tailWord_467224, baseEnd_467224] using wordTrace_append hprefix tailTrace_467224
  have hstable : (prefixWord ++ tailWord_467224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467224).length < 2 ^ (prefixWord ++ tailWord_467224).sum := by decide
  have hdescent : baseEnd_467224 < baseStart_467224 := by decide
  rcases family_descends (prefixWord ++ tailWord_467224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467262 : List Nat := [4, 2, 1, 2, 1, 9]
def baseStart_467262 : Nat := 118140960795 + 467262 * 2 ^ 59
def prefixEnd_467262 : Nat := 4983230072969 + 3 ^ 40 * 467262 * 2
def baseEnd_467262 : Nat := 15797859923045667093077

theorem tailTrace_467262 : CollatzResearch.WordTrace tailWord_467262 prefixEnd_467262 15797859923045667093077 := by
  unfold tailWord_467262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130305654149631355168505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11361630155464700560898693 2130305654149631355168505)
  ·
    refine ⟨1597729240612223516376379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2130305654149631355168505 1597729240612223516376379)
    ·
      refine ⟨2396593860918335274564569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1597729240612223516376379 2396593860918335274564569)
      ·
        refine ⟨1797445395688751455923427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2396593860918335274564569 1797445395688751455923427)
        ·
          refine ⟨2696168093533127183885141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797445395688751455923427 2696168093533127183885141)
          ·
            refine ⟨15797859923045667093077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2696168093533127183885141 15797859923045667093077)
            ·
              rfl

theorem cell19_467262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 9].length) (baseStart_467262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467262 prefixEnd_467262 := by exact prefixLift 467262
  have htrace : WordTrace (prefixWord ++ tailWord_467262) baseStart_467262 baseEnd_467262 := by
    simpa [prefixWord, tailWord_467262, baseEnd_467262] using wordTrace_append hprefix tailTrace_467262
  have hstable : (prefixWord ++ tailWord_467262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467262).length < 2 ^ (prefixWord ++ tailWord_467262).sum := by decide
  have hdescent : baseEnd_467262 < baseStart_467262 := by decide
  rcases family_descends (prefixWord ++ tailWord_467262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467281 : List Nat := [1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_467281 : Nat := 118140960795 + 467281 * 2 ^ 59
def prefixEnd_467281 : Nat := 4983230072969 + 3 ^ 40 * 467281 * 2
def baseEnd_467281 : Nat := 142186520719224589415419

theorem tailTrace_467281 : CollatzResearch.WordTrace tailWord_467281 prefixEnd_467281 142186520719224589415419 := by
  unfold tailWord_467281
  simp only [CollatzResearch.WordTrace]
  refine ⟨17043138220128217086289697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11362092146752144724193131 17043138220128217086289697)
  ·
    refine ⟨12782353665096162814717273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17043138220128217086289697 12782353665096162814717273)
    ·
      refine ⟨9586765248822122111037955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12782353665096162814717273 9586765248822122111037955)
      ·
        refine ⟨14380147873233183166556933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586765248822122111037955 14380147873233183166556933)
        ·
          refine ⟨2696277726231221843729425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14380147873233183166556933 2696277726231221843729425)
          ·
            refine ⟨2022208294673416382797069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2696277726231221843729425 2022208294673416382797069)
            ·
              refine ⟨758328110502531143548901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2022208294673416382797069 758328110502531143548901)
              ·
                refine ⟨142186520719224589415419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758328110502531143548901 142186520719224589415419)
                ·
                  rfl

theorem cell19_467281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_467281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467281 prefixEnd_467281 := by exact prefixLift 467281
  have htrace : WordTrace (prefixWord ++ tailWord_467281) baseStart_467281 baseEnd_467281 := by
    simpa [prefixWord, tailWord_467281, baseEnd_467281] using wordTrace_append hprefix tailTrace_467281
  have hstable : (prefixWord ++ tailWord_467281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467281).length < 2 ^ (prefixWord ++ tailWord_467281).sum := by decide
  have hdescent : baseEnd_467281 < baseStart_467281 := by decide
  rcases family_descends (prefixWord ++ tailWord_467281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467283 : List Nat := [1, 1, 1, 2, 1, 1, 4, 8]
def baseStart_467283 : Nat := 118140960795 + 467283 * 2 ^ 59
def prefixEnd_467283 : Nat := 4983230072969 + 3 ^ 40 * 467283 * 2
def baseEnd_467283 : Nat := 142187129288889177370969

theorem tailTrace_467283 : CollatzResearch.WordTrace tailWord_467283 prefixEnd_467283 142187129288889177370969 := by
  unfold tailWord_467283
  simp only [CollatzResearch.WordTrace]
  refine ⟨17043211166120971427862503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11362140777413980951908335 17043211166120971427862503)
  ·
    refine ⟨25564816749181457141793755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17043211166120971427862503 25564816749181457141793755)
    ·
      refine ⟨38347225123772185712690633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25564816749181457141793755 38347225123772185712690633)
      ·
        refine ⟨28760418842829139284517975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38347225123772185712690633 28760418842829139284517975)
        ·
          refine ⟨43140628264243708926776963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28760418842829139284517975 43140628264243708926776963)
          ·
            refine ⟨64710942396365563390165445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43140628264243708926776963 64710942396365563390165445)
            ·
              refine ⟨12133301699318543135656021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64710942396365563390165445 12133301699318543135656021)
              ·
                refine ⟨142187129288889177370969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12133301699318543135656021 142187129288889177370969)
                ·
                  rfl

theorem cell19_467283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_467283 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467283 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467283 prefixEnd_467283 := by exact prefixLift 467283
  have htrace : WordTrace (prefixWord ++ tailWord_467283) baseStart_467283 baseEnd_467283 := by
    simpa [prefixWord, tailWord_467283, baseEnd_467283] using wordTrace_append hprefix tailTrace_467283
  have hstable : (prefixWord ++ tailWord_467283).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467283).length < 2 ^ (prefixWord ++ tailWord_467283).sum := by decide
  have hdescent : baseEnd_467283 < baseStart_467283 := by decide
  rcases family_descends (prefixWord ++ tailWord_467283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467370 : List Nat := [3, 1, 6, 1, 1, 2, 5]
def baseStart_467370 : Nat := 118140960795 + 467370 * 2 ^ 59
def prefixEnd_467370 : Nat := 4983230072969 + 3 ^ 40 * 467370 * 2
def baseEnd_467370 : Nat := 47404534023099584479133

theorem tailTrace_467370 : CollatzResearch.WordTrace tailWord_467370 prefixEnd_467370 47404534023099584479133 := by
  unfold tailWord_467370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261596079201446321569891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11364256211203856857519709 4261596079201446321569891)
  ·
    refine ⟨6392394118802169482354837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261596079201446321569891 6392394118802169482354837)
    ·
      refine ⟨299643474318851694485383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6392394118802169482354837 299643474318851694485383)
      ·
        refine ⟨449465211478277541728075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299643474318851694485383 449465211478277541728075)
        ·
          refine ⟨674197817217416312592113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449465211478277541728075 674197817217416312592113)
          ·
            refine ⟨505648362913062234444085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674197817217416312592113 505648362913062234444085)
            ·
              refine ⟨47404534023099584479133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 505648362913062234444085 47404534023099584479133)
              ·
                rfl

theorem cell19_467370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 5].length) (baseStart_467370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467370 prefixEnd_467370 := by exact prefixLift 467370
  have htrace : WordTrace (prefixWord ++ tailWord_467370) baseStart_467370 baseEnd_467370 := by
    simpa [prefixWord, tailWord_467370, baseEnd_467370] using wordTrace_append hprefix tailTrace_467370
  have hstable : (prefixWord ++ tailWord_467370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467370).length < 2 ^ (prefixWord ++ tailWord_467370).sum := by decide
  have hdescent : baseEnd_467370 < baseStart_467370 := by decide
  rcases family_descends (prefixWord ++ tailWord_467370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467511 : List Nat := [1, 1, 3, 1, 2, 3, 2, 6]
def baseStart_467511 : Nat := 118140960795 + 467511 * 2 ^ 59
def prefixEnd_467511 : Nat := 4983230072969 + 3 ^ 40 * 467511 * 2
def baseEnd_467511 : Nat := 142256506230652204303681

theorem tailTrace_467511 : CollatzResearch.WordTrace tailWord_467511 prefixEnd_467511 142256506230652204303681 := by
  unfold tailWord_467511
  simp only [CollatzResearch.WordTrace]
  refine ⟨17051527009294966367162387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11367684672863310911441591 17051527009294966367162387)
  ·
    refine ⟨25577290513942449550743581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17051527009294966367162387 25577290513942449550743581)
    ·
      refine ⟨9591483942728418581528843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25577290513942449550743581 9591483942728418581528843)
      ·
        refine ⟨14387225914092627872293265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9591483942728418581528843 14387225914092627872293265)
        ·
          refine ⟨10790419435569470904219949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14387225914092627872293265 10790419435569470904219949)
          ·
            refine ⟨4046407288338551589082481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10790419435569470904219949 4046407288338551589082481)
            ·
              refine ⟨3034805466253913691811861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4046407288338551589082481 3034805466253913691811861)
              ·
                refine ⟨142256506230652204303681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3034805466253913691811861 142256506230652204303681)
                ·
                  rfl

theorem cell19_467511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_467511 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467511 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467511 prefixEnd_467511 := by exact prefixLift 467511
  have htrace : WordTrace (prefixWord ++ tailWord_467511) baseStart_467511 baseEnd_467511 := by
    simpa [prefixWord, tailWord_467511, baseEnd_467511] using wordTrace_append hprefix tailTrace_467511
  have hstable : (prefixWord ++ tailWord_467511).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467511).length < 2 ^ (prefixWord ++ tailWord_467511).sum := by decide
  have hdescent : baseEnd_467511 < baseStart_467511 := by decide
  rcases family_descends (prefixWord ++ tailWord_467511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467566 : List Nat := [4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_467566 : Nat := 118140960795 + 467566 * 2 ^ 59
def prefixEnd_467566 : Nat := 4983230072969 + 3 ^ 40 * 467566 * 2
def baseEnd_467566 : Nat := 142273241896428373081309

theorem tailTrace_467566 : CollatzResearch.WordTrace tailWord_467566 prefixEnd_467566 142273241896428373081309 := by
  unfold tailWord_467566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131691628011963845051819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11369022016063807173609701 2131691628011963845051819)
  ·
    refine ⟨3197537442017945767577729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2131691628011963845051819 3197537442017945767577729)
    ·
      refine ⟨2398153081513459325683297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3197537442017945767577729 2398153081513459325683297)
      ·
        refine ⟨1798614811135094494262473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2398153081513459325683297 1798614811135094494262473)
        ·
          refine ⟨1348961108351320870696855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1798614811135094494262473 1348961108351320870696855)
          ·
            refine ⟨2023441662526981306045283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348961108351320870696855 2023441662526981306045283)
            ·
              refine ⟨3035162493790471959067925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023441662526981306045283 3035162493790471959067925)
              ·
                refine ⟨142273241896428373081309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3035162493790471959067925 142273241896428373081309)
                ·
                  rfl

theorem cell19_467566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_467566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467566 prefixEnd_467566 := by exact prefixLift 467566
  have htrace : WordTrace (prefixWord ++ tailWord_467566) baseStart_467566 baseEnd_467566 := by
    simpa [prefixWord, tailWord_467566, baseEnd_467566] using wordTrace_append hprefix tailTrace_467566
  have hstable : (prefixWord ++ tailWord_467566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467566).length < 2 ^ (prefixWord ++ tailWord_467566).sum := by decide
  have hdescent : baseEnd_467566 < baseStart_467566 := by decide
  rcases family_descends (prefixWord ++ tailWord_467566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467587 : List Nat := [1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_467587 : Nat := 118140960795 + 467587 * 2 ^ 59
def prefixEnd_467587 : Nat := 4983230072969 + 3 ^ 40 * 467587 * 2
def baseEnd_467587 : Nat := 142279631877906546614585

theorem tailTrace_467587 : CollatzResearch.WordTrace tailWord_467587 prefixEnd_467587 142279631877906546614585 := by
  unfold tailWord_467587
  simp only [CollatzResearch.WordTrace]
  refine ⟨17054298957019631346929015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11369532638013087564619343 17054298957019631346929015)
  ·
    refine ⟨25581448435529447020393523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17054298957019631346929015 25581448435529447020393523)
    ·
      refine ⟨38372172653294170530590285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25581448435529447020393523 38372172653294170530590285)
      ·
        refine ⟨14389564744985313948971357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38372172653294170530590285 14389564744985313948971357)
        ·
          refine ⟨5396086779369492730864259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14389564744985313948971357 5396086779369492730864259)
          ·
            refine ⟨8094130169054239096296389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396086779369492730864259 8094130169054239096296389)
            ·
              refine ⟨1517649406697669830555573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8094130169054239096296389 1517649406697669830555573)
              ·
                refine ⟨142279631877906546614585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1517649406697669830555573 142279631877906546614585)
                ·
                  rfl

theorem cell19_467587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_467587 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467587 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467587 prefixEnd_467587 := by exact prefixLift 467587
  have htrace : WordTrace (prefixWord ++ tailWord_467587) baseStart_467587 baseEnd_467587 := by
    simpa [prefixWord, tailWord_467587, baseEnd_467587] using wordTrace_append hprefix tailTrace_467587
  have hstable : (prefixWord ++ tailWord_467587).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467587).length < 2 ^ (prefixWord ++ tailWord_467587).sum := by decide
  have hdescent : baseEnd_467587 < baseStart_467587 := by decide
  rcases family_descends (prefixWord ++ tailWord_467587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467604 : List Nat := [2, 4, 2, 2, 1, 8]
def baseStart_467604 : Nat := 118140960795 + 467604 * 2 ^ 59
def prefixEnd_467604 : Nat := 4983230072969 + 3 ^ 40 * 467604 * 2
def baseEnd_467604 : Nat := 15809422746672838248529

theorem tailTrace_467604 : CollatzResearch.WordTrace tailWord_467604 prefixEnd_467604 15809422746672838248529 := by
  unfold tailWord_467604
  simp only [CollatzResearch.WordTrace]
  refine ⟨8527459498979021625148933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11369945998638695500198577 8527459498979021625148933)
  ·
    refine ⟨1598898656058566554715425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8527459498979021625148933 1598898656058566554715425)
    ·
      refine ⟨1199173992043924916036569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1598898656058566554715425 1199173992043924916036569)
      ·
        refine ⟨899380494032943687027427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1199173992043924916036569 899380494032943687027427)
        ·
          refine ⟨1349070741049415530541141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 899380494032943687027427 1349070741049415530541141)
          ·
            refine ⟨15809422746672838248529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1349070741049415530541141 15809422746672838248529)
            ·
              rfl

theorem cell19_467604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 8].length) (baseStart_467604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467604 prefixEnd_467604 := by exact prefixLift 467604
  have htrace : WordTrace (prefixWord ++ tailWord_467604) baseStart_467604 baseEnd_467604 := by
    simpa [prefixWord, tailWord_467604, baseEnd_467604] using wordTrace_append hprefix tailTrace_467604
  have hstable : (prefixWord ++ tailWord_467604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467604).length < 2 ^ (prefixWord ++ tailWord_467604).sum := by decide
  have hdescent : baseEnd_467604 < baseStart_467604 := by decide
  rcases family_descends (prefixWord ++ tailWord_467604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467642 : List Nat := [3, 1, 1, 1, 2, 3, 5, 3]
def baseStart_467642 : Nat := 118140960795 + 467642 * 2 ^ 59
def prefixEnd_467642 : Nat := 4983230072969 + 3 ^ 40 * 467642 * 2
def baseEnd_467642 : Nat := 142296367543682715392213

theorem tailTrace_467642 : CollatzResearch.WordTrace tailWord_467642 prefixEnd_467642 142296367543682715392213 := by
  unfold tailWord_467642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4264076242955093935045295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11370869981213583826787453 4264076242955093935045295)
  ·
    refine ⟨6396114364432640902567943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4264076242955093935045295 6396114364432640902567943)
    ·
      refine ⟨9594171546648961353851915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6396114364432640902567943 9594171546648961353851915)
      ·
        refine ⟨14391257319973442030777873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9594171546648961353851915 14391257319973442030777873)
        ·
          refine ⟨10793442989980081523083405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14391257319973442030777873 10793442989980081523083405)
          ·
            refine ⟨4047541121242530571156277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10793442989980081523083405 4047541121242530571156277)
            ·
              refine ⟨379456980116487241045901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4047541121242530571156277 379456980116487241045901)
              ·
                refine ⟨142296367543682715392213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379456980116487241045901 142296367543682715392213)
                ·
                  rfl

theorem cell19_467642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_467642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467642 prefixEnd_467642 := by exact prefixLift 467642
  have htrace : WordTrace (prefixWord ++ tailWord_467642) baseStart_467642 baseEnd_467642 := by
    simpa [prefixWord, tailWord_467642, baseEnd_467642] using wordTrace_append hprefix tailTrace_467642
  have hstable : (prefixWord ++ tailWord_467642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467642).length < 2 ^ (prefixWord ++ tailWord_467642).sum := by decide
  have hdescent : baseEnd_467642 < baseStart_467642 := by decide
  rcases family_descends (prefixWord ++ tailWord_467642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467720 : List Nat := [2, 1, 3, 2, 2, 2, 7]
def baseStart_467720 : Nat := 118140960795 + 467720 * 2 ^ 59
def prefixEnd_467720 : Nat := 4983230072969 + 3 ^ 40 * 467720 * 2
def baseEnd_467720 : Nat := 47440033920200548552889

theorem tailTrace_467720 : CollatzResearch.WordTrace tailWord_467720 prefixEnd_467720 47440033920200548552889 := by
  unfold tailWord_467720
  simp only [CollatzResearch.WordTrace]
  refine ⟨8529574932768897530760307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11372766577025196707680409 8529574932768897530760307)
  ·
    refine ⟨12794362399153346296140461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8529574932768897530760307 12794362399153346296140461)
    ·
      refine ⟨4797885899682504861052673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12794362399153346296140461 4797885899682504861052673)
      ·
        refine ⟨3598414424761878645789505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4797885899682504861052673 3598414424761878645789505)
        ·
          refine ⟨2698810818571408984342129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3598414424761878645789505 2698810818571408984342129)
          ·
            refine ⟨2024108113928556738256597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2698810818571408984342129 2024108113928556738256597)
            ·
              refine ⟨47440033920200548552889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2024108113928556738256597 47440033920200548552889)
              ·
                rfl

theorem cell19_467720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 7].length) (baseStart_467720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467720 prefixEnd_467720 := by exact prefixLift 467720
  have htrace : WordTrace (prefixWord ++ tailWord_467720) baseStart_467720 baseEnd_467720 := by
    simpa [prefixWord, tailWord_467720, baseEnd_467720] using wordTrace_append hprefix tailTrace_467720
  have hstable : (prefixWord ++ tailWord_467720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467720).length < 2 ^ (prefixWord ++ tailWord_467720).sum := by decide
  have hdescent : baseEnd_467720 < baseStart_467720 := by decide
  rcases family_descends (prefixWord ++ tailWord_467720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467866 : List Nat := [3, 1, 1, 4, 4, 1, 2, 3]
def baseStart_467866 : Nat := 118140960795 + 467866 * 2 ^ 59
def prefixEnd_467866 : Nat := 4983230072969 + 3 ^ 40 * 467866 * 2
def baseEnd_467866 : Nat := 142364527346116566413825

theorem tailTrace_467866 : CollatzResearch.WordTrace tailWord_467866 prefixEnd_467866 142364527346116566413825 := by
  unfold tailWord_467866
  simp only [CollatzResearch.WordTrace]
  refine ⟨4266118730752215499083863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11376316615339241330890301 4266118730752215499083863)
  ·
    refine ⟨6399178096128323248625795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4266118730752215499083863 6399178096128323248625795)
    ·
      refine ⟨9598767144192484872938693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6399178096128323248625795 9598767144192484872938693)
      ·
        refine ⟨1799768839536090913676005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9598767144192484872938693 1799768839536090913676005)
        ·
          refine ⟨337456657413017046314251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1799768839536090913676005 337456657413017046314251)
          ·
            refine ⟨506184986119525569471377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337456657413017046314251 506184986119525569471377)
            ·
              refine ⟨379638739589644177103533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506184986119525569471377 379638739589644177103533)
              ·
                refine ⟨142364527346116566413825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379638739589644177103533 142364527346116566413825)
                ·
                  rfl

theorem cell19_467866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_467866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467866 prefixEnd_467866 := by exact prefixLift 467866
  have htrace : WordTrace (prefixWord ++ tailWord_467866) baseStart_467866 baseEnd_467866 := by
    simpa [prefixWord, tailWord_467866, baseEnd_467866] using wordTrace_append hprefix tailTrace_467866
  have hstable : (prefixWord ++ tailWord_467866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467866).length < 2 ^ (prefixWord ++ tailWord_467866).sum := by decide
  have hdescent : baseEnd_467866 < baseStart_467866 := by decide
  rcases family_descends (prefixWord ++ tailWord_467866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467885 : List Nat := [1, 5, 2, 3, 2, 1, 5]
def baseStart_467885 : Nat := 118140960795 + 467885 * 2 ^ 59
def prefixEnd_467885 : Nat := 4983230072969 + 3 ^ 40 * 467885 * 2
def baseEnd_467885 : Nat := 47456769585976717330517

theorem tailTrace_467885 : CollatzResearch.WordTrace tailWord_467885 prefixEnd_467885 47456769585976717330517 := by
  unfold tailWord_467885
  simp only [CollatzResearch.WordTrace]
  refine ⟨17065167909940028241277109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11376778606626685494184739 17065167909940028241277109)
  ·
    refine ⟨1599859491556877647619729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17065167909940028241277109 1599859491556877647619729)
    ·
      refine ⟨1199894618667658235714797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1599859491556877647619729 1199894618667658235714797)
      ·
        refine ⟨449960482000371838393049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1199894618667658235714797 449960482000371838393049)
        ·
          refine ⟨337470361500278878794787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449960482000371838393049 337470361500278878794787)
          ·
            refine ⟨506205542250418318192181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337470361500278878794787 506205542250418318192181)
            ·
              refine ⟨47456769585976717330517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506205542250418318192181 47456769585976717330517)
              ·
                rfl

theorem cell19_467885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 5].length) (baseStart_467885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467885 prefixEnd_467885 := by exact prefixLift 467885
  have htrace : WordTrace (prefixWord ++ tailWord_467885) baseStart_467885 baseEnd_467885 := by
    simpa [prefixWord, tailWord_467885, baseEnd_467885] using wordTrace_append hprefix tailTrace_467885
  have hstable : (prefixWord ++ tailWord_467885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467885).length < 2 ^ (prefixWord ++ tailWord_467885).sum := by decide
  have hdescent : baseEnd_467885 < baseStart_467885 := by decide
  rcases family_descends (prefixWord ++ tailWord_467885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467889 : List Nat := [1, 2, 2, 4, 3, 2, 5]
def baseStart_467889 : Nat := 118140960795 + 467889 * 2 ^ 59
def prefixEnd_467889 : Nat := 4983230072969 + 3 ^ 40 * 467889 * 2
def baseEnd_467889 : Nat := 47457175299086442634217

theorem tailTrace_467889 : CollatzResearch.WordTrace tailWord_467889 prefixEnd_467889 47457175299086442634217 := by
  unfold tailWord_467889
  simp only [CollatzResearch.WordTrace]
  refine ⟨17065313801925536924422721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11376875867950357949615147 17065313801925536924422721)
  ·
    refine ⟨12798985351444152693317041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17065313801925536924422721 12798985351444152693317041)
    ·
      refine ⟨9599239013583114519987781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12798985351444152693317041 9599239013583114519987781)
      ·
        refine ⟨1799857315046833972497709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9599239013583114519987781 1799857315046833972497709)
        ·
          refine ⟨674946493142562739686641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1799857315046833972497709 674946493142562739686641)
          ·
            refine ⟨506209869856922054764981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674946493142562739686641 506209869856922054764981)
            ·
              refine ⟨47457175299086442634217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506209869856922054764981 47457175299086442634217)
              ·
                rfl

theorem cell19_467889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 5].length) (baseStart_467889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467889 prefixEnd_467889 := by exact prefixLift 467889
  have htrace : WordTrace (prefixWord ++ tailWord_467889) baseStart_467889 baseEnd_467889 := by
    simpa [prefixWord, tailWord_467889, baseEnd_467889] using wordTrace_append hprefix tailTrace_467889
  have hstable : (prefixWord ++ tailWord_467889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467889).length < 2 ^ (prefixWord ++ tailWord_467889).sum := by decide
  have hdescent : baseEnd_467889 < baseStart_467889 := by decide
  rcases family_descends (prefixWord ++ tailWord_467889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_467929 : List Nat := [1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_467929 : Nat := 118140960795 + 467929 * 2 ^ 59
def prefixEnd_467929 : Nat := 4983230072969 + 3 ^ 40 * 467929 * 2
def baseEnd_467929 : Nat := 142383697290551087013653

theorem tailTrace_467929 : CollatzResearch.WordTrace tailWord_467929 prefixEnd_467929 142383697290551087013653 := by
  unfold tailWord_467929
  simp only [CollatzResearch.WordTrace]
  refine ⟨17066772721780623755878841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11377848481187082503919227 17066772721780623755878841)
  ·
    refine ⟨12800079541335467816909131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17066772721780623755878841 12800079541335467816909131)
    ·
      refine ⟨19200119312003201725363697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12800079541335467816909131 19200119312003201725363697)
      ·
        refine ⟨14400089484002401294022773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19200119312003201725363697 14400089484002401294022773)
        ·
          refine ⟨1350008389125225121314635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14400089484002401294022773 1350008389125225121314635)
          ·
            refine ⟨2025012583687837681971953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350008389125225121314635 2025012583687837681971953)
            ·
              refine ⟨1518759437765878261478965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025012583687837681971953 1518759437765878261478965)
              ·
                refine ⟨142383697290551087013653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1518759437765878261478965 142383697290551087013653)
                ·
                  rfl

theorem cell19_467929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_467929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_467929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_467929 prefixEnd_467929 := by exact prefixLift 467929
  have htrace : WordTrace (prefixWord ++ tailWord_467929) baseStart_467929 baseEnd_467929 := by
    simpa [prefixWord, tailWord_467929, baseEnd_467929] using wordTrace_append hprefix tailTrace_467929
  have hstable : (prefixWord ++ tailWord_467929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_467929).length < 2 ^ (prefixWord ++ tailWord_467929).sum := by decide
  have hdescent : baseEnd_467929 < baseStart_467929 := by decide
  rcases family_descends (prefixWord ++ tailWord_467929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468100 : List Nat := [2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_468100 : Nat := 118140960795 + 468100 * 2 ^ 59
def prefixEnd_468100 : Nat := 4983230072969 + 3 ^ 40 * 468100 * 2
def baseEnd_468100 : Nat := 142435729996873357213187

theorem tailTrace_468100 : CollatzResearch.WordTrace tailWord_468100 prefixEnd_468100 142435729996873357213187 := by
  unfold tailWord_468100
  simp only [CollatzResearch.WordTrace]
  refine ⟨8536504802080559980176877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11382006402774079973569169 8536504802080559980176877)
  ·
    refine ⟨3201189300780209992566329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8536504802080559980176877 3201189300780209992566329)
    ·
      refine ⟨2400891975585157494424747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3201189300780209992566329 2400891975585157494424747)
      ·
        refine ⟨3601337963377736241637121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400891975585157494424747 3601337963377736241637121)
        ·
          refine ⟨2701003472533302181227841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3601337963377736241637121 2701003472533302181227841)
          ·
            refine ⟨2025752604399976635920881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701003472533302181227841 2025752604399976635920881)
            ·
              refine ⟨1519314453299982476940661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025752604399976635920881 1519314453299982476940661)
              ·
                refine ⟨142435729996873357213187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1519314453299982476940661 142435729996873357213187)
                ·
                  rfl

theorem cell19_468100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_468100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468100 prefixEnd_468100 := by exact prefixLift 468100
  have htrace : WordTrace (prefixWord ++ tailWord_468100) baseStart_468100 baseEnd_468100 := by
    simpa [prefixWord, tailWord_468100, baseEnd_468100] using wordTrace_append hprefix tailTrace_468100
  have hstable : (prefixWord ++ tailWord_468100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468100).length < 2 ^ (prefixWord ++ tailWord_468100).sum := by decide
  have hdescent : baseEnd_468100 < baseStart_468100 := by decide
  rcases family_descends (prefixWord ++ tailWord_468100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468140 : List Nat := [2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_468140 : Nat := 118140960795 + 468140 * 2 ^ 59
def prefixEnd_468140 : Nat := 4983230072969 + 3 ^ 40 * 468140 * 2
def baseEnd_468140 : Nat := 142447901390165116324189

theorem tailTrace_468140 : CollatzResearch.WordTrace tailWord_468140 prefixEnd_468140 142447901390165116324189 := by
  unfold tailWord_468140
  simp only [CollatzResearch.WordTrace]
  refine ⟨8537234262008103395904937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11382979016010804527873249 8537234262008103395904937)
  ·
    refine ⟨6402925696506077546928703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8537234262008103395904937 6402925696506077546928703)
    ·
      refine ⟨9604388544759116320393055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402925696506077546928703 9604388544759116320393055)
      ·
        refine ⟨14406582817138674480589583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9604388544759116320393055 14406582817138674480589583)
        ·
          refine ⟨21609874225708011720884375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14406582817138674480589583 21609874225708011720884375)
          ·
            refine ⟨32414811338562017581326563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21609874225708011720884375 32414811338562017581326563)
            ·
              refine ⟨48622217007843026371989845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32414811338562017581326563 48622217007843026371989845)
              ·
                refine ⟨142447901390165116324189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48622217007843026371989845 142447901390165116324189)
                ·
                  rfl

theorem cell19_468140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_468140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468140 prefixEnd_468140 := by exact prefixLift 468140
  have htrace : WordTrace (prefixWord ++ tailWord_468140) baseStart_468140 baseEnd_468140 := by
    simpa [prefixWord, tailWord_468140, baseEnd_468140] using wordTrace_append hprefix tailTrace_468140
  have hstable : (prefixWord ++ tailWord_468140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468140).length < 2 ^ (prefixWord ++ tailWord_468140).sum := by decide
  have hdescent : baseEnd_468140 < baseStart_468140 := by decide
  rcases family_descends (prefixWord ++ tailWord_468140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468159 : List Nat := [1, 1, 2, 2, 2, 2, 2, 7]
def baseStart_468159 : Nat := 118140960795 + 468159 * 2 ^ 59
def prefixEnd_468159 : Nat := 4983230072969 + 3 ^ 40 * 468159 * 2
def baseEnd_468159 : Nat := 142453682801978701901915

theorem tailTrace_468159 : CollatzResearch.WordTrace tailWord_468159 prefixEnd_468159 142453682801978701901915 := by
  unfold tailWord_468159
  simp only [CollatzResearch.WordTrace]
  refine ⟨17075161510947373036751531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11383441007298248691167687 17075161510947373036751531)
  ·
    refine ⟨25612742266421059555127297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17075161510947373036751531 25612742266421059555127297)
    ·
      refine ⟨19209556699815794666345473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25612742266421059555127297 19209556699815794666345473)
      ·
        refine ⟨14407167524861845999759105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19209556699815794666345473 14407167524861845999759105)
        ·
          refine ⟨10805375643646384499819329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14407167524861845999759105 10805375643646384499819329)
          ·
            refine ⟨8104031732734788374864497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10805375643646384499819329 8104031732734788374864497)
            ·
              refine ⟨6078023799551091281148373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8104031732734788374864497 6078023799551091281148373)
              ·
                refine ⟨142453682801978701901915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6078023799551091281148373 142453682801978701901915)
                ·
                  rfl

theorem cell19_468159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_468159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468159 prefixEnd_468159 := by exact prefixLift 468159
  have htrace : WordTrace (prefixWord ++ tailWord_468159) baseStart_468159 baseEnd_468159 := by
    simpa [prefixWord, tailWord_468159, baseEnd_468159] using wordTrace_append hprefix tailTrace_468159
  have hstable : (prefixWord ++ tailWord_468159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468159).length < 2 ^ (prefixWord ++ tailWord_468159).sum := by decide
  have hdescent : baseEnd_468159 < baseStart_468159 := by decide
  rcases family_descends (prefixWord ++ tailWord_468159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468210 : List Nat := [3, 2, 1, 3, 3, 2, 2, 3]
def baseStart_468210 : Nat := 118140960795 + 468210 * 2 ^ 59
def prefixEnd_468210 : Nat := 4983230072969 + 3 ^ 40 * 468210 * 2
def baseEnd_468210 : Nat := 142469201328425694768443

theorem tailTrace_468210 : CollatzResearch.WordTrace tailWord_468210 prefixEnd_468210 142469201328425694768443 := by
  unfold tailWord_468210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4269255408440652186714521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11384681089175072497905389 4269255408440652186714521)
  ·
    refine ⟨3201941556330489140035891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4269255408440652186714521 3201941556330489140035891)
    ·
      refine ⟨4802912334495733710053837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3201941556330489140035891 4802912334495733710053837)
      ·
        refine ⟨1801092125435900141270189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4802912334495733710053837 1801092125435900141270189)
        ·
          refine ⟨675409547038462552976321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1801092125435900141270189 675409547038462552976321)
          ·
            refine ⟨506557160278846914732241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675409547038462552976321 506557160278846914732241)
            ·
              refine ⟨379917870209135186049181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506557160278846914732241 379917870209135186049181)
              ·
                refine ⟨142469201328425694768443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379917870209135186049181 142469201328425694768443)
                ·
                  rfl

theorem cell19_468210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_468210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468210 prefixEnd_468210 := by exact prefixLift 468210
  have htrace : WordTrace (prefixWord ++ tailWord_468210) baseStart_468210 baseEnd_468210 := by
    simpa [prefixWord, tailWord_468210, baseEnd_468210] using wordTrace_append hprefix tailTrace_468210
  have hstable : (prefixWord ++ tailWord_468210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468210).length < 2 ^ (prefixWord ++ tailWord_468210).sum := by decide
  have hdescent : baseEnd_468210 < baseStart_468210 := by decide
  rcases family_descends (prefixWord ++ tailWord_468210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468235 : List Nat := [1, 1, 1, 1, 5, 3, 7]
def baseStart_468235 : Nat := 118140960795 + 468235 * 2 ^ 59
def prefixEnd_468235 : Nat := 4983230072969 + 3 ^ 40 * 468235 * 2
def baseEnd_468235 : Nat := 47492269483077681404273

theorem tailTrace_468235 : CollatzResearch.WordTrace tailWord_468235 prefixEnd_468235 47492269483077681404273 := by
  unfold tailWord_468235
  simp only [CollatzResearch.WordTrace]
  refine ⟨17077933458672038016518159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11385288972448025344345439 17077933458672038016518159)
  ·
    refine ⟨25616900188008057024777239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17077933458672038016518159 25616900188008057024777239)
    ·
      refine ⟨38425350282012085537165859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25616900188008057024777239 38425350282012085537165859)
      ·
        refine ⟨57638025423018128305748789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38425350282012085537165859 57638025423018128305748789)
        ·
          refine ⟨5403564883407949528663949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57638025423018128305748789 5403564883407949528663949)
          ·
            refine ⟨2026336831277981073248981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5403564883407949528663949 2026336831277981073248981)
            ·
              refine ⟨47492269483077681404273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2026336831277981073248981 47492269483077681404273)
              ·
                rfl

theorem cell19_468235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_468235 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468235 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468235 prefixEnd_468235 := by exact prefixLift 468235
  have htrace : WordTrace (prefixWord ++ tailWord_468235) baseStart_468235 baseEnd_468235 := by
    simpa [prefixWord, tailWord_468235, baseEnd_468235] using wordTrace_append hprefix tailTrace_468235
  have hstable : (prefixWord ++ tailWord_468235).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468235).length < 2 ^ (prefixWord ++ tailWord_468235).sum := by decide
  have hdescent : baseEnd_468235 < baseStart_468235 := by decide
  rcases family_descends (prefixWord ++ tailWord_468235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468269 : List Nat := [1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_468269 : Nat := 118140960795 + 468269 * 2 ^ 59
def prefixEnd_468269 : Nat := 4983230072969 + 3 ^ 40 * 468269 * 2
def baseEnd_468269 : Nat := 142487154133531039457171

theorem tailTrace_468269 : CollatzResearch.WordTrace tailWord_468269 prefixEnd_468269 142487154133531039457171 := by
  unfold tailWord_468269
  simp only [CollatzResearch.WordTrace]
  refine ⟨17079173540548861823255861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11386115693699241215503907 17079173540548861823255861)
  ·
    refine ⟨1601172519426455795930237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17079173540548861823255861 1601172519426455795930237)
    ·
      refine ⟨600439694784920923473839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1601172519426455795930237 600439694784920923473839)
      ·
        refine ⟨900659542177381385210759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600439694784920923473839 900659542177381385210759)
        ·
          refine ⟨1350989313266072077816139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900659542177381385210759 1350989313266072077816139)
          ·
            refine ⟨2026483969899108116724209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350989313266072077816139 2026483969899108116724209)
            ·
              refine ⟨1519862977424331087543157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026483969899108116724209 1519862977424331087543157)
              ·
                refine ⟨142487154133531039457171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1519862977424331087543157 142487154133531039457171)
                ·
                  rfl

theorem cell19_468269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_468269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468269 prefixEnd_468269 := by exact prefixLift 468269
  have htrace : WordTrace (prefixWord ++ tailWord_468269) baseStart_468269 baseEnd_468269 := by
    simpa [prefixWord, tailWord_468269, baseEnd_468269] using wordTrace_append hprefix tailTrace_468269
  have hstable : (prefixWord ++ tailWord_468269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468269).length < 2 ^ (prefixWord ++ tailWord_468269).sum := by decide
  have hdescent : baseEnd_468269 < baseStart_468269 := by decide
  rcases family_descends (prefixWord ++ tailWord_468269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468309 : List Nat := [1, 3, 2, 2, 3, 1, 3, 4]
def baseStart_468309 : Nat := 118140960795 + 468309 * 2 ^ 59
def prefixEnd_468309 : Nat := 4983230072969 + 3 ^ 40 * 468309 * 2
def baseEnd_468309 : Nat := 142499325526822798568173

theorem tailTrace_468309 : CollatzResearch.WordTrace tailWord_468309 prefixEnd_468309 142499325526822798568173 := by
  unfold tailWord_468309
  simp only [CollatzResearch.WordTrace]
  refine ⟨17080632460403948654711981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11387088306935965769807987 17080632460403948654711981)
  ·
    refine ⟨6405237172651480745516993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17080632460403948654711981 6405237172651480745516993)
    ·
      refine ⟨4803927879488610559137745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6405237172651480745516993 4803927879488610559137745)
      ·
        refine ⟨3602945909616457919353309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4803927879488610559137745 3602945909616457919353309)
        ·
          refine ⟨1351104716106171719757491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3602945909616457919353309 1351104716106171719757491)
          ·
            refine ⟨2026657074159257579636237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351104716106171719757491 2026657074159257579636237)
            ·
              refine ⟨759996402809721592363589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2026657074159257579636237 759996402809721592363589)
              ·
                refine ⟨142499325526822798568173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 759996402809721592363589 142499325526822798568173)
                ·
                  rfl

theorem cell19_468309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_468309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468309 prefixEnd_468309 := by exact prefixLift 468309
  have htrace : WordTrace (prefixWord ++ tailWord_468309) baseStart_468309 baseEnd_468309 := by
    simpa [prefixWord, tailWord_468309, baseEnd_468309] using wordTrace_append hprefix tailTrace_468309
  have hstable : (prefixWord ++ tailWord_468309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468309).length < 2 ^ (prefixWord ++ tailWord_468309).sum := by decide
  have hdescent : baseEnd_468309 < baseStart_468309 := by decide
  rcases family_descends (prefixWord ++ tailWord_468309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468349 : List Nat := [1, 4, 1, 1, 2, 2, 8]
def baseStart_468349 : Nat := 118140960795 + 468349 * 2 ^ 59
def prefixEnd_468349 : Nat := 4983230072969 + 3 ^ 40 * 468349 * 2
def baseEnd_468349 : Nat := 47503832306704852559725

theorem tailTrace_468349 : CollatzResearch.WordTrace tailWord_468349 prefixEnd_468349 47503832306704852559725 := by
  unfold tailWord_468349
  simp only [CollatzResearch.WordTrace]
  refine ⟨17082091380259035486168101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11388060920172690324112067 17082091380259035486168101)
  ·
    refine ⟨3202892133798569153656519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17082091380259035486168101 3202892133798569153656519)
    ·
      refine ⟨4804338200697853730484779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3202892133798569153656519 4804338200697853730484779)
      ·
        refine ⟨7206507301046780595727169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804338200697853730484779 7206507301046780595727169)
        ·
          refine ⟨5404880475785085446795377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7206507301046780595727169 5404880475785085446795377)
          ·
            refine ⟨4053660356838814085096533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5404880475785085446795377 4053660356838814085096533)
            ·
              refine ⟨47503832306704852559725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4053660356838814085096533 47503832306704852559725)
              ·
                rfl

theorem cell19_468349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_468349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468349 prefixEnd_468349 := by exact prefixLift 468349
  have htrace : WordTrace (prefixWord ++ tailWord_468349) baseStart_468349 baseEnd_468349 := by
    simpa [prefixWord, tailWord_468349, baseEnd_468349] using wordTrace_append hprefix tailTrace_468349
  have hstable : (prefixWord ++ tailWord_468349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468349).length < 2 ^ (prefixWord ++ tailWord_468349).sum := by decide
  have hdescent : baseEnd_468349 < baseStart_468349 := by decide
  rcases family_descends (prefixWord ++ tailWord_468349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468383 : List Nat := [1, 1, 2, 5, 1, 4, 2, 3]
def baseStart_468383 : Nat := 118140960795 + 468383 * 2 ^ 59
def prefixEnd_468383 : Nat := 4983230072969 + 3 ^ 40 * 468383 * 2
def baseEnd_468383 : Nat := 142521842604412552923527

theorem tailTrace_468383 : CollatzResearch.WordTrace tailWord_468383 prefixEnd_468383 142521842604412552923527 := by
  unfold tailWord_468383
  simp only [CollatzResearch.WordTrace]
  refine ⟨17083331462135859292905803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11388887641423906195270535 17083331462135859292905803)
  ·
    refine ⟨25624997193203788939358705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17083331462135859292905803 25624997193203788939358705)
    ·
      refine ⟨19218747894902841704519029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25624997193203788939358705 19218747894902841704519029)
      ·
        refine ⟨1801757615147141409798659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19218747894902841704519029 1801757615147141409798659)
        ·
          refine ⟨2702636422720712114697989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801757615147141409798659 2702636422720712114697989)
          ·
            refine ⟨506744329260133521505873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2702636422720712114697989 506744329260133521505873)
            ·
              refine ⟨380058246945100141129405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506744329260133521505873 380058246945100141129405)
              ·
                refine ⟨142521842604412552923527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380058246945100141129405 142521842604412552923527)
                ·
                  rfl

theorem cell19_468383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_468383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468383 prefixEnd_468383 := by exact prefixLift 468383
  have htrace : WordTrace (prefixWord ++ tailWord_468383) baseStart_468383 baseEnd_468383 := by
    simpa [prefixWord, tailWord_468383, baseEnd_468383] using wordTrace_append hprefix tailTrace_468383
  have hstable : (prefixWord ++ tailWord_468383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468383).length < 2 ^ (prefixWord ++ tailWord_468383).sum := by decide
  have hdescent : baseEnd_468383 < baseStart_468383 := by decide
  rcases family_descends (prefixWord ++ tailWord_468383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468387 : List Nat := [1, 1, 1, 4, 1, 3, 3, 5]
def baseStart_468387 : Nat := 118140960795 + 468387 * 2 ^ 59
def prefixEnd_468387 : Nat := 4983230072969 + 3 ^ 40 * 468387 * 2
def baseEnd_468387 : Nat := 142523059743741728834627

theorem tailTrace_468387 : CollatzResearch.WordTrace tailWord_468387 prefixEnd_468387 142523059743741728834627 := by
  unfold tailWord_468387
  simp only [CollatzResearch.WordTrace]
  refine ⟨17083477354121367976051415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11388984902747578650700943 17083477354121367976051415)
  ·
    refine ⟨25625216031182051964077123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17083477354121367976051415 25625216031182051964077123)
    ·
      refine ⟨38437824046773077946115685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25625216031182051964077123 38437824046773077946115685)
      ·
        refine ⟨7207092008769952114896691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38437824046773077946115685 7207092008769952114896691)
        ·
          refine ⟨10810638013154928172345037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7207092008769952114896691 10810638013154928172345037)
          ·
            refine ⟨4053989254933098064629389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10810638013154928172345037 4053989254933098064629389)
            ·
              refine ⟨1520245970599911774236021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4053989254933098064629389 1520245970599911774236021)
              ·
                refine ⟨142523059743741728834627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1520245970599911774236021 142523059743741728834627)
                ·
                  rfl

theorem cell19_468387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_468387 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468387 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468387 prefixEnd_468387 := by exact prefixLift 468387
  have htrace : WordTrace (prefixWord ++ tailWord_468387) baseStart_468387 baseEnd_468387 := by
    simpa [prefixWord, tailWord_468387, baseEnd_468387] using wordTrace_append hprefix tailTrace_468387
  have hstable : (prefixWord ++ tailWord_468387).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468387).length < 2 ^ (prefixWord ++ tailWord_468387).sum := by decide
  have hdescent : baseEnd_468387 < baseStart_468387 := by decide
  rcases family_descends (prefixWord ++ tailWord_468387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468461 : List Nat := [1, 5, 1, 3, 2, 7]
def baseStart_468461 : Nat := 118140960795 + 468461 * 2 ^ 59
def prefixEnd_468461 : Nat := 4983230072969 + 3 ^ 40 * 468461 * 2
def baseEnd_468461 : Nat := 15838397424592387021109

theorem tailTrace_468461 : CollatzResearch.WordTrace tailWord_468461 prefixEnd_468461 15838397424592387021109 := by
  unfold tailWord_468461
  simp only [CollatzResearch.WordTrace]
  refine ⟨17086176355853278614245237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11390784237235519076163491 17086176355853278614245237)
  ·
    refine ⟨1601829033361244870085491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17086176355853278614245237 1601829033361244870085491)
    ·
      refine ⟨2402743550041867305128237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1601829033361244870085491 2402743550041867305128237)
      ·
        refine ⟨901028831265700239423089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2402743550041867305128237 901028831265700239423089)
        ·
          refine ⟨675771623449275179567317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901028831265700239423089 675771623449275179567317)
          ·
            refine ⟨15838397424592387021109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 675771623449275179567317 15838397424592387021109)
            ·
              rfl

theorem cell19_468461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 7].length) (baseStart_468461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468461 prefixEnd_468461 := by exact prefixLift 468461
  have htrace : WordTrace (prefixWord ++ tailWord_468461) baseStart_468461 baseEnd_468461 := by
    simpa [prefixWord, tailWord_468461, baseEnd_468461] using wordTrace_append hprefix tailTrace_468461
  have hstable : (prefixWord ++ tailWord_468461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468461).length < 2 ^ (prefixWord ++ tailWord_468461).sum := by decide
  have hdescent : baseEnd_468461 < baseStart_468461 := by decide
  rcases family_descends (prefixWord ++ tailWord_468461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468493 : List Nat := [1, 7, 1, 1, 2, 1, 3, 3]
def baseStart_468493 : Nat := 118140960795 + 468493 * 2 ^ 59
def prefixEnd_468493 : Nat := 4983230072969 + 3 ^ 40 * 468493 * 2
def baseEnd_468493 : Nat := 142555313935964890478783

theorem tailTrace_468493 : CollatzResearch.WordTrace tailWord_468493 prefixEnd_468493 142555313935964890478783 := by
  unfold tailWord_468493
  simp only [CollatzResearch.WordTrace]
  refine ⟨17087343491737348079410133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11391562327824898719606755 17087343491737348079410133)
  ·
    refine ⟨400484613087594095611175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 17087343491737348079410133 400484613087594095611175)
    ·
      refine ⟨600726919631391143416763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400484613087594095611175 600726919631391143416763)
      ·
        refine ⟨901090379447086715125145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 600726919631391143416763 901090379447086715125145)
        ·
          refine ⟨675817784585315036343859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901090379447086715125145 675817784585315036343859)
          ·
            refine ⟨1013726676877972554515789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675817784585315036343859 1013726676877972554515789)
            ·
              refine ⟨380147503829239707943421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1013726676877972554515789 380147503829239707943421)
              ·
                refine ⟨142555313935964890478783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380147503829239707943421 142555313935964890478783)
                ·
                  rfl

theorem cell19_468493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_468493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468493 prefixEnd_468493 := by exact prefixLift 468493
  have htrace : WordTrace (prefixWord ++ tailWord_468493) baseStart_468493 baseEnd_468493 := by
    simpa [prefixWord, tailWord_468493, baseEnd_468493] using wordTrace_append hprefix tailTrace_468493
  have hstable : (prefixWord ++ tailWord_468493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468493).length < 2 ^ (prefixWord ++ tailWord_468493).sum := by decide
  have hdescent : baseEnd_468493 < baseStart_468493 := by decide
  rcases family_descends (prefixWord ++ tailWord_468493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468499 : List Nat := [1, 1, 1, 2, 1, 7, 3, 3]
def baseStart_468499 : Nat := 118140960795 + 468499 * 2 ^ 59
def prefixEnd_468499 : Nat := 4983230072969 + 3 ^ 40 * 468499 * 2
def baseEnd_468499 : Nat := 142557139644958654345433

theorem tailTrace_468499 : CollatzResearch.WordTrace tailWord_468499 prefixEnd_468499 142557139644958654345433 := by
  unfold tailWord_468499
  simp only [CollatzResearch.WordTrace]
  refine ⟨17087562329715611104128551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11391708219810407402752367 17087562329715611104128551)
  ·
    refine ⟨25631343494573416656192827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17087562329715611104128551 25631343494573416656192827)
    ·
      refine ⟨38447015241860124984289241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25631343494573416656192827 38447015241860124984289241)
      ·
        refine ⟨28835261431395093738216931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38447015241860124984289241 28835261431395093738216931)
        ·
          refine ⟨43252892147092640607325397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28835261431395093738216931 43252892147092640607325397)
          ·
            refine ⟨1013739659697483764234189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43252892147092640607325397 1013739659697483764234189)
            ·
              refine ⟨380152372386556411587821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1013739659697483764234189 380152372386556411587821)
              ·
                refine ⟨142557139644958654345433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380152372386556411587821 142557139644958654345433)
                ·
                  rfl

theorem cell19_468499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_468499 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468499 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468499 prefixEnd_468499 := by exact prefixLift 468499
  have htrace : WordTrace (prefixWord ++ tailWord_468499) baseStart_468499 baseEnd_468499 := by
    simpa [prefixWord, tailWord_468499, baseEnd_468499] using wordTrace_append hprefix tailTrace_468499
  have hstable : (prefixWord ++ tailWord_468499).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468499).length < 2 ^ (prefixWord ++ tailWord_468499).sum := by decide
  have hdescent : baseEnd_468499 < baseStart_468499 := by decide
  rcases family_descends (prefixWord ++ tailWord_468499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468550 : List Nat := [6, 1, 1, 1, 3, 2, 2, 3]
def baseStart_468550 : Nat := 118140960795 + 468550 * 2 ^ 59
def prefixEnd_468550 : Nat := 4983230072969 + 3 ^ 40 * 468550 * 2
def baseEnd_468550 : Nat := 142572658171405647211961

theorem tailTrace_468550 : CollatzResearch.WordTrace tailWord_468550 prefixEnd_468550 142572658171405647211961 := by
  unfold tailWord_468550
  simp only [CollatzResearch.WordTrace]
  refine ⟨534044451641588962944847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11392948301687231209490069 534044451641588962944847)
  ·
    refine ⟨801066677462383444417271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 534044451641588962944847 801066677462383444417271)
    ·
      refine ⟨1201600016193575166625907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801066677462383444417271 1201600016193575166625907)
      ·
        refine ⟨1802400024290362749938861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201600016193575166625907 1802400024290362749938861)
        ·
          refine ⟨675900009108886031227073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1802400024290362749938861 675900009108886031227073)
          ·
            refine ⟨506925006831664523420305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 675900009108886031227073 506925006831664523420305)
            ·
              refine ⟨380193755123748392565229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506925006831664523420305 380193755123748392565229)
              ·
                refine ⟨142572658171405647211961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380193755123748392565229 142572658171405647211961)
                ·
                  rfl

theorem cell19_468550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_468550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468550 prefixEnd_468550 := by exact prefixLift 468550
  have htrace : WordTrace (prefixWord ++ tailWord_468550) baseStart_468550 baseEnd_468550 := by
    simpa [prefixWord, tailWord_468550, baseEnd_468550] using wordTrace_append hprefix tailTrace_468550
  have hstable : (prefixWord ++ tailWord_468550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468550).length < 2 ^ (prefixWord ++ tailWord_468550).sum := by decide
  have hdescent : baseEnd_468550 < baseStart_468550 := by decide
  rcases family_descends (prefixWord ++ tailWord_468550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468556 : List Nat := [2, 2, 1, 3, 1, 3, 4, 3]
def baseStart_468556 : Nat := 118140960795 + 468556 * 2 ^ 59
def prefixEnd_468556 : Nat := 4983230072969 + 3 ^ 40 * 468556 * 2
def baseEnd_468556 : Nat := 142574483880399411078611

theorem tailTrace_468556 : CollatzResearch.WordTrace tailWord_468556 prefixEnd_468556 142574483880399411078611 := by
  unfold tailWord_468556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544820645254554919476761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11393094193672739892635681 8544820645254554919476761)
  ·
    refine ⟨6408615483940916189607571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8544820645254554919476761 6408615483940916189607571)
    ·
      refine ⟨9612923225911374284411357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6408615483940916189607571 9612923225911374284411357)
      ·
        refine ⟨3604846209716765356654259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9612923225911374284411357 3604846209716765356654259)
        ·
          refine ⟨5407269314575148034981389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3604846209716765356654259 5407269314575148034981389)
          ·
            refine ⟨2027725992965680513118021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5407269314575148034981389 2027725992965680513118021)
            ·
              refine ⟨380198623681065096209629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2027725992965680513118021 380198623681065096209629)
              ·
                refine ⟨142574483880399411078611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380198623681065096209629 142574483880399411078611)
                ·
                  rfl

theorem cell19_468556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_468556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468556 prefixEnd_468556 := by exact prefixLift 468556
  have htrace : WordTrace (prefixWord ++ tailWord_468556) baseStart_468556 baseEnd_468556 := by
    simpa [prefixWord, tailWord_468556, baseEnd_468556] using wordTrace_append hprefix tailTrace_468556
  have hstable : (prefixWord ++ tailWord_468556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468556).length < 2 ^ (prefixWord ++ tailWord_468556).sum := by decide
  have hdescent : baseEnd_468556 < baseStart_468556 := by decide
  rcases family_descends (prefixWord ++ tailWord_468556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468594 : List Nat := [3, 2, 1, 2, 3, 2, 2, 4]
def baseStart_468594 : Nat := 118140960795 + 468594 * 2 ^ 59
def prefixEnd_468594 : Nat := 4983230072969 + 3 ^ 40 * 468594 * 2
def baseEnd_468594 : Nat := 142586046704026582234063

theorem tailTrace_468594 : CollatzResearch.WordTrace tailWord_468594 prefixEnd_468594 142586046704026582234063 := by
  unfold tailWord_468594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4272756816092860582209209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11394018176247628219224557 4272756816092860582209209)
  ·
    refine ⟨3204567612069645436656907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4272756816092860582209209 3204567612069645436656907)
    ·
      refine ⟨4806851418104468154985361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3204567612069645436656907 4806851418104468154985361)
      ·
        refine ⟨3605138563578351116239021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4806851418104468154985361 3605138563578351116239021)
        ·
          refine ⟨1351926961341881668589633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3605138563578351116239021 1351926961341881668589633)
          ·
            refine ⟨1013945221006411251442225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1351926961341881668589633 1013945221006411251442225)
            ·
              refine ⟨760458915754808438581669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1013945221006411251442225 760458915754808438581669)
              ·
                refine ⟨142586046704026582234063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 760458915754808438581669 142586046704026582234063)
                ·
                  rfl

theorem cell19_468594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_468594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468594 prefixEnd_468594 := by exact prefixLift 468594
  have htrace : WordTrace (prefixWord ++ tailWord_468594) baseStart_468594 baseEnd_468594 := by
    simpa [prefixWord, tailWord_468594, baseEnd_468594] using wordTrace_append hprefix tailTrace_468594
  have hstable : (prefixWord ++ tailWord_468594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468594).length < 2 ^ (prefixWord ++ tailWord_468594).sum := by decide
  have hdescent : baseEnd_468594 < baseStart_468594 := by decide
  rcases family_descends (prefixWord ++ tailWord_468594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468615 : List Nat := [1, 1, 4, 2, 1, 3, 2, 5]
def baseStart_468615 : Nat := 118140960795 + 468615 * 2 ^ 59
def prefixEnd_468615 : Nat := 4983230072969 + 3 ^ 40 * 468615 * 2
def baseEnd_468615 : Nat := 142592436685504755767339

theorem tailTrace_468615 : CollatzResearch.WordTrace tailWord_468615 prefixEnd_468615 142592436685504755767339 := by
  unfold tailWord_468615
  simp only [CollatzResearch.WordTrace]
  refine ⟨17091793197295362915351299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11394528798196908610234199 17091793197295362915351299)
  ·
    refine ⟨25637689795943044373026949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17091793197295362915351299 25637689795943044373026949)
    ·
      refine ⟨4807066836739320819942553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25637689795943044373026949 4807066836739320819942553)
      ·
        refine ⟨3605300127554490614956915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4807066836739320819942553 3605300127554490614956915)
        ·
          refine ⟨5407950191331735922435373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605300127554490614956915 5407950191331735922435373)
          ·
            refine ⟨2027981321749400970913265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5407950191331735922435373 2027981321749400970913265)
            ·
              refine ⟨1520985991312050728184949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027981321749400970913265 1520985991312050728184949)
              ·
                refine ⟨142592436685504755767339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1520985991312050728184949 142592436685504755767339)
                ·
                  rfl

theorem cell19_468615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_468615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468615 prefixEnd_468615 := by exact prefixLift 468615
  have htrace : WordTrace (prefixWord ++ tailWord_468615) baseStart_468615 baseEnd_468615 := by
    simpa [prefixWord, tailWord_468615, baseEnd_468615] using wordTrace_append hprefix tailTrace_468615
  have hstable : (prefixWord ++ tailWord_468615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468615).length < 2 ^ (prefixWord ++ tailWord_468615).sum := by decide
  have hdescent : baseEnd_468615 < baseStart_468615 := by decide
  rcases family_descends (prefixWord ++ tailWord_468615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468767 : List Nat := [1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_468767 : Nat := 118140960795 + 468767 * 2 ^ 59
def prefixEnd_468767 : Nat := 4983230072969 + 3 ^ 40 * 468767 * 2
def baseEnd_468767 : Nat := 142638687980013440389147

theorem tailTrace_468767 : CollatzResearch.WordTrace tailWord_468767 prefixEnd_468767 142638687980013440389147 := by
  unfold tailWord_468767
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097337092744692874884555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11398224728496461916589703 17097337092744692874884555)
  ·
    refine ⟨25646005639117039312326833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17097337092744692874884555 25646005639117039312326833)
    ·
      refine ⟨19234504229337779484245125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25646005639117039312326833 19234504229337779484245125)
      ·
        refine ⟨3606469543000833653295961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19234504229337779484245125 3606469543000833653295961)
        ·
          refine ⟨2704852157250625239971971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3606469543000833653295961 2704852157250625239971971)
          ·
            refine ⟨4057278235875937859957957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704852157250625239971971 4057278235875937859957957)
            ·
              refine ⟨760739669226738348742117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4057278235875937859957957 760739669226738348742117)
              ·
                refine ⟨142638687980013440389147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 760739669226738348742117 142638687980013440389147)
                ·
                  rfl

theorem cell19_468767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_468767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468767 prefixEnd_468767 := by exact prefixLift 468767
  have htrace : WordTrace (prefixWord ++ tailWord_468767) baseStart_468767 baseEnd_468767 := by
    simpa [prefixWord, tailWord_468767, baseEnd_468767] using wordTrace_append hprefix tailTrace_468767
  have hstable : (prefixWord ++ tailWord_468767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468767).length < 2 ^ (prefixWord ++ tailWord_468767).sum := by decide
  have hdescent : baseEnd_468767 < baseStart_468767 := by decide
  rcases family_descends (prefixWord ++ tailWord_468767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468786 : List Nat := [3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_468786 : Nat := 118140960795 + 468786 * 2 ^ 59
def prefixEnd_468786 : Nat := 4983230072969 + 3 ^ 40 * 468786 * 2
def baseEnd_468786 : Nat := 142644469391827025966873

theorem tailTrace_468786 : CollatzResearch.WordTrace tailWord_468786 prefixEnd_468786 142644469391827025966873 := by
  unfold tailWord_468786
  simp only [CollatzResearch.WordTrace]
  refine ⟨4274507519918964779956553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11398686719783906079884141 4274507519918964779956553)
  ·
    refine ⟨3205880639939223584967415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4274507519918964779956553 3205880639939223584967415)
    ·
      refine ⟨4808820959908835377451123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205880639939223584967415 4808820959908835377451123)
      ·
        refine ⟨7213231439863253066176685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808820959908835377451123 7213231439863253066176685)
        ·
          refine ⟨2704961789948719899816257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7213231439863253066176685 2704961789948719899816257)
          ·
            refine ⟨2028721342461539924862193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704961789948719899816257 2028721342461539924862193)
            ·
              refine ⟨1521541006846154943646645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2028721342461539924862193 1521541006846154943646645)
              ·
                refine ⟨142644469391827025966873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1521541006846154943646645 142644469391827025966873)
                ·
                  rfl

theorem cell19_468786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_468786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468786 prefixEnd_468786 := by exact prefixLift 468786
  have htrace : WordTrace (prefixWord ++ tailWord_468786) baseStart_468786 baseEnd_468786 := by
    simpa [prefixWord, tailWord_468786, baseEnd_468786] using wordTrace_append hprefix tailTrace_468786
  have hstable : (prefixWord ++ tailWord_468786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468786).length < 2 ^ (prefixWord ++ tailWord_468786).sum := by decide
  have hdescent : baseEnd_468786 < baseStart_468786 := by decide
  rcases family_descends (prefixWord ++ tailWord_468786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468864 : List Nat := [2, 1, 1, 2, 1, 2, 10]
def baseStart_468864 : Nat := 118140960795 + 468864 * 2 ^ 59
def prefixEnd_468864 : Nat := 4983230072969 + 3 ^ 40 * 468864 * 2
def baseEnd_468864 : Nat := 47556067869581985411109

theorem tailTrace_468864 : CollatzResearch.WordTrace tailWord_468864 prefixEnd_468864 47556067869581985411109 := by
  unfold tailWord_468864
  simp only [CollatzResearch.WordTrace]
  refine ⟨8550437486696639220582823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11400583315595518960777097 8550437486696639220582823)
  ·
    refine ⟨12825656230044958830874235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8550437486696639220582823 12825656230044958830874235)
    ·
      refine ⟨19238484345067438246311353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12825656230044958830874235 19238484345067438246311353)
      ·
        refine ⟨14428863258800578684733515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19238484345067438246311353 14428863258800578684733515)
        ·
          refine ⟨21643294888200868027100273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14428863258800578684733515 21643294888200868027100273)
          ·
            refine ⟨16232471166150651020325205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21643294888200868027100273 16232471166150651020325205)
            ·
              refine ⟨47556067869581985411109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16232471166150651020325205 47556067869581985411109)
              ·
                rfl

theorem cell19_468864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_468864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468864 prefixEnd_468864 := by exact prefixLift 468864
  have htrace : WordTrace (prefixWord ++ tailWord_468864) baseStart_468864 baseEnd_468864 := by
    simpa [prefixWord, tailWord_468864, baseEnd_468864] using wordTrace_append hprefix tailTrace_468864
  have hstable : (prefixWord ++ tailWord_468864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468864).length < 2 ^ (prefixWord ++ tailWord_468864).sum := by decide
  have hdescent : baseEnd_468864 < baseStart_468864 := by decide
  rcases family_descends (prefixWord ++ tailWord_468864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468898 : List Nat := [3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_468898 : Nat := 118140960795 + 468898 * 2 ^ 59
def prefixEnd_468898 : Nat := 4983230072969 + 3 ^ 40 * 468898 * 2
def baseEnd_468898 : Nat := 142678549293043951477679

theorem tailTrace_468898 : CollatzResearch.WordTrace tailWord_468898 prefixEnd_468898 142678549293043951477679 := by
  unfold tailWord_468898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275528763817525561975837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11401410036846734831935565 4275528763817525561975837)
  ·
    refine ⟨1603323286431572085740939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4275528763817525561975837 1603323286431572085740939)
    ·
      refine ⟨2404984929647358128611409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603323286431572085740939 2404984929647358128611409)
      ·
        refine ⟨1803738697235518596458557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2404984929647358128611409 1803738697235518596458557)
        ·
          refine ⟨676402011463319473671959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1803738697235518596458557 676402011463319473671959)
          ·
            refine ⟨1014603017194979210507939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676402011463319473671959 1014603017194979210507939)
            ·
              refine ⟨1521904525792468815761909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014603017194979210507939 1521904525792468815761909)
              ·
                refine ⟨142678549293043951477679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1521904525792468815761909 142678549293043951477679)
                ·
                  rfl

theorem cell19_468898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_468898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468898 prefixEnd_468898 := by exact prefixLift 468898
  have htrace : WordTrace (prefixWord ++ tailWord_468898) baseStart_468898 baseEnd_468898 := by
    simpa [prefixWord, tailWord_468898, baseEnd_468898] using wordTrace_append hprefix tailTrace_468898
  have hstable : (prefixWord ++ tailWord_468898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468898).length < 2 ^ (prefixWord ++ tailWord_468898).sum := by decide
  have hdescent : baseEnd_468898 < baseStart_468898 := by decide
  rcases family_descends (prefixWord ++ tailWord_468898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468900 : List Nat := [2, 3, 1, 2, 1, 4, 1, 5]
def baseStart_468900 : Nat := 118140960795 + 468900 * 2 ^ 59
def prefixEnd_468900 : Nat := 4983230072969 + 3 ^ 40 * 468900 * 2
def baseEnd_468900 : Nat := 142679157862708539433229

theorem tailTrace_468900 : CollatzResearch.WordTrace tailWord_468900 prefixEnd_468900 142679157862708539433229 := by
  unfold tailWord_468900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8551094000631428294738077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11401458667508571059650769 8551094000631428294738077)
  ·
    refine ⟨3206660250236785610526779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8551094000631428294738077 3206660250236785610526779)
    ·
      refine ⟨4809990375355178415790169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3206660250236785610526779 4809990375355178415790169)
      ·
        refine ⟨3607492781516383811842627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4809990375355178415790169 3607492781516383811842627)
        ·
          refine ⟨5411239172274575717763941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607492781516383811842627 5411239172274575717763941)
          ·
            refine ⟨1014607344801482947080739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5411239172274575717763941 1014607344801482947080739)
            ·
              refine ⟨1521911017202224420621109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1014607344801482947080739 1521911017202224420621109)
              ·
                refine ⟨142679157862708539433229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1521911017202224420621109 142679157862708539433229)
                ·
                  rfl

theorem cell19_468900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_468900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468900 prefixEnd_468900 := by exact prefixLift 468900
  have htrace : WordTrace (prefixWord ++ tailWord_468900) baseStart_468900 baseEnd_468900 := by
    simpa [prefixWord, tailWord_468900, baseEnd_468900] using wordTrace_append hprefix tailTrace_468900
  have hstable : (prefixWord ++ tailWord_468900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468900).length < 2 ^ (prefixWord ++ tailWord_468900).sum := by decide
  have hdescent : baseEnd_468900 < baseStart_468900 := by decide
  rcases family_descends (prefixWord ++ tailWord_468900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_468978 : List Nat := [3, 2, 1, 13]
def baseStart_468978 : Nat := 118140960795 + 468978 * 2 ^ 59
def prefixEnd_468978 : Nat := 4983230072969 + 3 ^ 40 * 468978 * 2
def baseEnd_468978 : Nat := 1761764099748487280243

theorem tailTrace_468978 : CollatzResearch.WordTrace tailWord_468978 prefixEnd_468978 1761764099748487280243 := by
  unfold tailWord_468978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276258223745068977703897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11403355263320183940543725 4276258223745068977703897)
  ·
    refine ⟨3207193667808801733277923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4276258223745068977703897 3207193667808801733277923)
    ·
      refine ⟨4810790501713202599916885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3207193667808801733277923 4810790501713202599916885)
      ·
        refine ⟨1761764099748487280243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4810790501713202599916885 1761764099748487280243)
        ·
          rfl

theorem cell19_468978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 13].length) (baseStart_468978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_468978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_468978 prefixEnd_468978 := by exact prefixLift 468978
  have htrace : WordTrace (prefixWord ++ tailWord_468978) baseStart_468978 baseEnd_468978 := by
    simpa [prefixWord, tailWord_468978, baseEnd_468978] using wordTrace_append hprefix tailTrace_468978
  have hstable : (prefixWord ++ tailWord_468978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_468978).length < 2 ^ (prefixWord ++ tailWord_468978).sum := by decide
  have hdescent : baseEnd_468978 < baseStart_468978 := by decide
  rcases family_descends (prefixWord ++ tailWord_468978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469031 : List Nat := [1, 1, 7, 1, 2, 1, 6]
def baseStart_469031 : Nat := 118140960795 + 469031 * 2 ^ 59
def prefixEnd_469031 : Nat := 4983230072969 + 3 ^ 40 * 469031 * 2
def baseEnd_469031 : Nat := 47573006391913016840587

theorem tailTrace_469031 : CollatzResearch.WordTrace tailWord_469031 prefixEnd_469031 47573006391913016840587 := by
  unfold tailWord_469031
  simp only [CollatzResearch.WordTrace]
  refine ⟨17106965963788265962494947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11404643975858843974996631 17106965963788265962494947)
  ·
    refine ⟨25660448945682398943742421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17106965963788265962494947 25660448945682398943742421)
    ·
      refine ⟨601416772164431225243963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25660448945682398943742421 601416772164431225243963)
      ·
        refine ⟨902125158246646837865945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601416772164431225243963 902125158246646837865945)
        ·
          refine ⟨676593868684985128399459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 902125158246646837865945 676593868684985128399459)
          ·
            refine ⟨1014890803027477692599189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676593868684985128399459 1014890803027477692599189)
            ·
              refine ⟨47573006391913016840587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1014890803027477692599189 47573006391913016840587)
              ·
                rfl

theorem cell19_469031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_469031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469031 prefixEnd_469031 := by exact prefixLift 469031
  have htrace : WordTrace (prefixWord ++ tailWord_469031) baseStart_469031 baseEnd_469031 := by
    simpa [prefixWord, tailWord_469031, baseEnd_469031] using wordTrace_append hprefix tailTrace_469031
  have hstable : (prefixWord ++ tailWord_469031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469031).length < 2 ^ (prefixWord ++ tailWord_469031).sum := by decide
  have hdescent : baseEnd_469031 < baseStart_469031 := by decide
  rcases family_descends (prefixWord ++ tailWord_469031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469092 : List Nat := [2, 3, 1, 1, 2, 1, 9]
def baseStart_469092 : Nat := 118140960795 + 469092 * 2 ^ 59
def prefixEnd_469092 : Nat := 4983230072969 + 3 ^ 40 * 469092 * 2
def baseEnd_469092 : Nat := 47579193516836327722013

theorem tailTrace_469092 : CollatzResearch.WordTrace tailWord_469092 prefixEnd_469092 47579193516836327722013 := by
  unfold tailWord_469092
  simp only [CollatzResearch.WordTrace]
  refine ⟨8554595408283636690232765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11406127211044848920310353 8554595408283636690232765)
  ·
    refine ⟨3207973278106363758837287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8554595408283636690232765 3207973278106363758837287)
    ·
      refine ⟨4811959917159545638255931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3207973278106363758837287 4811959917159545638255931)
      ·
        refine ⟨7217939875739318457383897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811959917159545638255931 7217939875739318457383897)
        ·
          refine ⟨5413454906804488843037923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7217939875739318457383897 5413454906804488843037923)
          ·
            refine ⟨8120182360206733264556885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413454906804488843037923 8120182360206733264556885)
            ·
              refine ⟨47579193516836327722013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8120182360206733264556885 47579193516836327722013)
              ·
                rfl

theorem cell19_469092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 9].length) (baseStart_469092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469092 prefixEnd_469092 := by exact prefixLift 469092
  have htrace : WordTrace (prefixWord ++ tailWord_469092) baseStart_469092 baseEnd_469092 := by
    simpa [prefixWord, tailWord_469092, baseEnd_469092] using wordTrace_append hprefix tailTrace_469092
  have hstable : (prefixWord ++ tailWord_469092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469092).length < 2 ^ (prefixWord ++ tailWord_469092).sum := by decide
  have hdescent : baseEnd_469092 < baseStart_469092 := by decide
  rcases family_descends (prefixWord ++ tailWord_469092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469111 : List Nat := [1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_469111 : Nat := 118140960795 + 469111 * 2 ^ 59
def prefixEnd_469111 : Nat := 4983230072969 + 3 ^ 40 * 469111 * 2
def baseEnd_469111 : Nat := 142743361962322568743765

theorem tailTrace_469111 : CollatzResearch.WordTrace tailWord_469111 prefixEnd_469111 142743361962322568743765 := by
  unfold tailWord_469111
  simp only [CollatzResearch.WordTrace]
  refine ⟨17109883803498439625407187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11406589202332293083604791 17109883803498439625407187)
  ·
    refine ⟨25664825705247659438110781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17109883803498439625407187 25664825705247659438110781)
    ·
      refine ⟨9624309639467872289291543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25664825705247659438110781 9624309639467872289291543)
      ·
        refine ⟨14436464459201808433937315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9624309639467872289291543 14436464459201808433937315)
        ·
          refine ⟨21654696688802712650905973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14436464459201808433937315 21654696688802712650905973)
          ·
            refine ⟨2030127814575254311022435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21654696688802712650905973 2030127814575254311022435)
            ·
              refine ⟨3045191721862881466533653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030127814575254311022435 3045191721862881466533653)
              ·
                refine ⟨142743361962322568743765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3045191721862881466533653 142743361962322568743765)
                ·
                  rfl

theorem cell19_469111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_469111 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469111 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469111 prefixEnd_469111 := by exact prefixLift 469111
  have htrace : WordTrace (prefixWord ++ tailWord_469111) baseStart_469111 baseEnd_469111 := by
    simpa [prefixWord, tailWord_469111, baseEnd_469111] using wordTrace_append hprefix tailTrace_469111
  have hstable : (prefixWord ++ tailWord_469111).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469111).length < 2 ^ (prefixWord ++ tailWord_469111).sum := by decide
  have hdescent : baseEnd_469111 < baseStart_469111 := by decide
  rcases family_descends (prefixWord ++ tailWord_469111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469128 : List Nat := [2, 1, 3, 4, 1, 1, 2, 5]
def baseStart_469128 : Nat := 118140960795 + 469128 * 2 ^ 59
def prefixEnd_469128 : Nat := 4983230072969 + 3 ^ 40 * 469128 * 2
def baseEnd_469128 : Nat := 142748534804471566365941

theorem tailTrace_469128 : CollatzResearch.WordTrace tailWord_469128 prefixEnd_469128 142748534804471566365941 := by
  unfold tailWord_469128
  simp only [CollatzResearch.WordTrace]
  refine ⟨8555251922218425764388019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11407002562957901019184025 8555251922218425764388019)
  ·
    refine ⟨12832877883327638646582029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8555251922218425764388019 12832877883327638646582029)
    ·
      refine ⟨4812329206247864492468261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12832877883327638646582029 4812329206247864492468261)
      ·
        refine ⟨902311726171474592337799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4812329206247864492468261 902311726171474592337799)
        ·
          refine ⟨1353467589257211888506699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902311726171474592337799 1353467589257211888506699)
          ·
            refine ⟨2030201383885817832760049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353467589257211888506699 2030201383885817832760049)
            ·
              refine ⟨1522651037914363374570037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030201383885817832760049 1522651037914363374570037)
              ·
                refine ⟨142748534804471566365941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1522651037914363374570037 142748534804471566365941)
                ·
                  rfl

theorem cell19_469128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_469128 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469128 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469128 prefixEnd_469128 := by exact prefixLift 469128
  have htrace : WordTrace (prefixWord ++ tailWord_469128) baseStart_469128 baseEnd_469128 := by
    simpa [prefixWord, tailWord_469128, baseEnd_469128] using wordTrace_append hprefix tailTrace_469128
  have hstable : (prefixWord ++ tailWord_469128).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469128).length < 2 ^ (prefixWord ++ tailWord_469128).sum := by decide
  have hdescent : baseEnd_469128 < baseStart_469128 := by decide
  rcases family_descends (prefixWord ++ tailWord_469128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469149 : List Nat := [1, 4, 2, 1, 1, 10]
def baseStart_469149 : Nat := 118140960795 + 469149 * 2 ^ 59
def prefixEnd_469149 : Nat := 4983230072969 + 3 ^ 40 * 469149 * 2
def baseEnd_469149 : Nat := 15861658309549971099913

theorem tailTrace_469149 : CollatzResearch.WordTrace tailWord_469149 prefixEnd_469149 15861658309549971099913 := by
  unfold tailWord_469149
  simp only [CollatzResearch.WordTrace]
  refine ⟨17111269777360772115290501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11407513184907181410193667 17111269777360772115290501)
  ·
    refine ⟨3208363083255144771616969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17111269777360772115290501 3208363083255144771616969)
    ·
      refine ⟨2406272312441358578712727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3208363083255144771616969 2406272312441358578712727)
      ·
        refine ⟨3609408468662037868069091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406272312441358578712727 3609408468662037868069091)
        ·
          refine ⟨5414112702993056802103637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609408468662037868069091 5414112702993056802103637)
          ·
            refine ⟨15861658309549971099913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5414112702993056802103637 15861658309549971099913)
            ·
              rfl

theorem cell19_469149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 10].length) (baseStart_469149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469149 prefixEnd_469149 := by exact prefixLift 469149
  have htrace : WordTrace (prefixWord ++ tailWord_469149) baseStart_469149 baseEnd_469149 := by
    simpa [prefixWord, tailWord_469149, baseEnd_469149] using wordTrace_append hprefix tailTrace_469149
  have hstable : (prefixWord ++ tailWord_469149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469149).length < 2 ^ (prefixWord ++ tailWord_469149).sum := by decide
  have hdescent : baseEnd_469149 < baseStart_469149 := by decide
  rcases family_descends (prefixWord ++ tailWord_469149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469162 : List Nat := [3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_469162 : Nat := 118140960795 + 469162 * 2 ^ 59
def prefixEnd_469162 : Nat := 4983230072969 + 3 ^ 40 * 469162 * 2
def baseEnd_469162 : Nat := 142758880488769561610293

theorem tailTrace_469162 : CollatzResearch.WordTrace tailWord_469162 prefixEnd_469162 142758880488769561610293 := by
  unfold tailWord_469162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277935981578418833878435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11407829284209116890342493 4277935981578418833878435)
  ·
    refine ⟨6416903972367628250817653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4277935981578418833878435 6416903972367628250817653)
    ·
      refine ⟨601584747409465148514155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6416903972367628250817653 601584747409465148514155)
      ·
        refine ⟨902377121114197722771233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601584747409465148514155 902377121114197722771233)
        ·
          refine ⟨676782840835648292078425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 902377121114197722771233 676782840835648292078425)
          ·
            refine ⟨507587130626736219058819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676782840835648292078425 507587130626736219058819)
            ·
              refine ⟨761380695940104328588229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507587130626736219058819 761380695940104328588229)
              ·
                refine ⟨142758880488769561610293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 761380695940104328588229 142758880488769561610293)
                ·
                  rfl

theorem cell19_469162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_469162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469162 prefixEnd_469162 := by exact prefixLift 469162
  have htrace : WordTrace (prefixWord ++ tailWord_469162) baseStart_469162 baseEnd_469162 := by
    simpa [prefixWord, tailWord_469162, baseEnd_469162] using wordTrace_append hprefix tailTrace_469162
  have hstable : (prefixWord ++ tailWord_469162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469162).length < 2 ^ (prefixWord ++ tailWord_469162).sum := by decide
  have hdescent : baseEnd_469162 < baseStart_469162 := by decide
  rcases family_descends (prefixWord ++ tailWord_469162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469242 : List Nat := [3, 1, 1, 1, 1, 5, 4, 3]
def baseStart_469242 : Nat := 118140960795 + 469242 * 2 ^ 59
def prefixEnd_469242 : Nat := 4983230072969 + 3 ^ 40 * 469242 * 2
def baseEnd_469242 : Nat := 142783223275353079832297

theorem tailTrace_469242 : CollatzResearch.WordTrace tailWord_469242 prefixEnd_469242 142783223275353079832297 := by
  unfold tailWord_469242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278665441505962249606495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11409774510682565998950653 4278665441505962249606495)
  ·
    refine ⟨6417998162258943374409743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4278665441505962249606495 6417998162258943374409743)
    ·
      refine ⟨9626997243388415061614615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6417998162258943374409743 9626997243388415061614615)
      ·
        refine ⟨14440495865082622592421923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626997243388415061614615 14440495865082622592421923)
        ·
          refine ⟨21660743797623933888632885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14440495865082622592421923 21660743797623933888632885)
          ·
            refine ⟨2030694731027243802059333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21660743797623933888632885 2030694731027243802059333)
            ·
              refine ⟨380755262067608212886125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2030694731027243802059333 380755262067608212886125)
              ·
                refine ⟨142783223275353079832297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380755262067608212886125 142783223275353079832297)
                ·
                  rfl

theorem cell19_469242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_469242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469242 prefixEnd_469242 := by exact prefixLift 469242
  have htrace : WordTrace (prefixWord ++ tailWord_469242) baseStart_469242 baseEnd_469242 := by
    simpa [prefixWord, tailWord_469242, baseEnd_469242] using wordTrace_append hprefix tailTrace_469242
  have hstable : (prefixWord ++ tailWord_469242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469242).length < 2 ^ (prefixWord ++ tailWord_469242).sum := by decide
  have hdescent : baseEnd_469242 < baseStart_469242 := by decide
  rcases family_descends (prefixWord ++ tailWord_469242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469278 : List Nat := [4, 3, 2, 1, 1, 1, 1, 6]
def baseStart_469278 : Nat := 118140960795 + 469278 * 2 ^ 59
def prefixEnd_469278 : Nat := 4983230072969 + 3 ^ 40 * 469278 * 2
def baseEnd_469278 : Nat := 142794177529315663032199

theorem tailTrace_469278 : CollatzResearch.WordTrace tailWord_469278 prefixEnd_469278 142794177529315663032199 := by
  unfold tailWord_469278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2139496849236678393342061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11410649862595618097824325 2139496849236678393342061)
  ·
    refine ⟨802311318463754397503273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2139496849236678393342061 802311318463754397503273)
    ·
      refine ⟨601733488847815798127455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 802311318463754397503273 601733488847815798127455)
      ·
        refine ⟨902600233271723697191183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601733488847815798127455 902600233271723697191183)
        ·
          refine ⟨1353900349907585545786775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902600233271723697191183 1353900349907585545786775)
          ·
            refine ⟨2030850524861378318680163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353900349907585545786775 2030850524861378318680163)
            ·
              refine ⟨3046275787292067478020245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030850524861378318680163 3046275787292067478020245)
              ·
                refine ⟨142794177529315663032199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3046275787292067478020245 142794177529315663032199)
                ·
                  rfl

theorem cell19_469278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_469278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469278 prefixEnd_469278 := by exact prefixLift 469278
  have htrace : WordTrace (prefixWord ++ tailWord_469278) baseStart_469278 baseEnd_469278 := by
    simpa [prefixWord, tailWord_469278, baseEnd_469278] using wordTrace_append hprefix tailTrace_469278
  have hstable : (prefixWord ++ tailWord_469278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469278).length < 2 ^ (prefixWord ++ tailWord_469278).sum := by decide
  have hdescent : baseEnd_469278 < baseStart_469278 := by decide
  rcases family_descends (prefixWord ++ tailWord_469278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469280 : List Nat := [2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_469280 : Nat := 118140960795 + 469280 * 2 ^ 59
def prefixEnd_469280 : Nat := 4983230072969 + 3 ^ 40 * 469280 * 2
def baseEnd_469280 : Nat := 142794786098980250987749

theorem tailTrace_469280 : CollatzResearch.WordTrace tailWord_469280 prefixEnd_469280 142794786098980250987749 := by
  unfold tailWord_469280
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558023869943090744154647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11410698493257454325539529 8558023869943090744154647)
  ·
    refine ⟨12837035804914636116231971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8558023869943090744154647 12837035804914636116231971)
    ·
      refine ⟨19255553707371954174347957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12837035804914636116231971 19255553707371954174347957)
      ·
        refine ⟨1805208160066120703845121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19255553707371954174347957 1805208160066120703845121)
        ·
          refine ⟨1353906120049590527883841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1805208160066120703845121 1353906120049590527883841)
          ·
            refine ⟨1015429590037192895912881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353906120049590527883841 1015429590037192895912881)
            ·
              refine ⟨761572192527894671934661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015429590037192895912881 761572192527894671934661)
              ·
                refine ⟨142794786098980250987749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 761572192527894671934661 142794786098980250987749)
                ·
                  rfl

theorem cell19_469280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_469280 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469280 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469280 prefixEnd_469280 := by exact prefixLift 469280
  have htrace : WordTrace (prefixWord ++ tailWord_469280) baseStart_469280 baseEnd_469280 := by
    simpa [prefixWord, tailWord_469280, baseEnd_469280] using wordTrace_append hprefix tailTrace_469280
  have hstable : (prefixWord ++ tailWord_469280).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469280).length < 2 ^ (prefixWord ++ tailWord_469280).sum := by decide
  have hdescent : baseEnd_469280 < baseStart_469280 := by decide
  rcases family_descends (prefixWord ++ tailWord_469280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469301 : List Nat := [1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_469301 : Nat := 118140960795 + 469301 * 2 ^ 59
def prefixEnd_469301 : Nat := 4983230072969 + 3 ^ 40 * 469301 * 2
def baseEnd_469301 : Nat := 142801176080458424521025

theorem tailTrace_469301 : CollatzResearch.WordTrace tailWord_469301 prefixEnd_469301 142801176080458424521025 := by
  unfold tailWord_469301
  simp only [CollatzResearch.WordTrace]
  refine ⟨17116813672810102074823757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11411209115206734716549171 17116813672810102074823757)
  ·
    refine ⟨6418805127303788278058909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17116813672810102074823757 6418805127303788278058909)
    ·
      refine ⟨2407051922738920604272091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6418805127303788278058909 2407051922738920604272091)
      ·
        refine ⟨3610577884108380906408137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407051922738920604272091 3610577884108380906408137)
        ·
          refine ⟨2707933413081285679806103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3610577884108380906408137 2707933413081285679806103)
          ·
            refine ⟨4061900119621928519709155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707933413081285679806103 4061900119621928519709155)
            ·
              refine ⟨6092850179432892779563733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061900119621928519709155 6092850179432892779563733)
              ·
                refine ⟨142801176080458424521025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6092850179432892779563733 142801176080458424521025)
                ·
                  rfl

theorem cell19_469301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_469301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469301 prefixEnd_469301 := by exact prefixLift 469301
  have htrace : WordTrace (prefixWord ++ tailWord_469301) baseStart_469301 baseEnd_469301 := by
    simpa [prefixWord, tailWord_469301, baseEnd_469301] using wordTrace_append hprefix tailTrace_469301
  have hstable : (prefixWord ++ tailWord_469301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469301).length < 2 ^ (prefixWord ++ tailWord_469301).sum := by decide
  have hdescent : baseEnd_469301 < baseStart_469301 := by decide
  rcases family_descends (prefixWord ++ tailWord_469301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469316 : List Nat := [2, 3, 4, 1, 3, 6]
def baseStart_469316 : Nat := 118140960795 + 469316 * 2 ^ 59
def prefixEnd_469316 : Nat := 4983230072969 + 3 ^ 40 * 469316 * 2
def baseEnd_469316 : Nat := 15867304483660314909739

theorem tailTrace_469316 : CollatzResearch.WordTrace tailWord_469316 prefixEnd_469316 15867304483660314909739 := by
  unfold tailWord_469316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8558680383877879818309901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11411573845170506424413201 8558680383877879818309901)
  ·
    refine ⟨3209505143954204931866213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8558680383877879818309901 3209505143954204931866213)
    ·
      refine ⟨601782214491413424724915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3209505143954204931866213 601782214491413424724915)
      ·
        refine ⟨902673321737120137087373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601782214491413424724915 902673321737120137087373)
        ·
          refine ⟨338502495651420051407765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 902673321737120137087373 338502495651420051407765)
          ·
            refine ⟨15867304483660314909739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 338502495651420051407765 15867304483660314909739)
            ·
              rfl

theorem cell19_469316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 6].length) (baseStart_469316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469316 prefixEnd_469316 := by exact prefixLift 469316
  have htrace : WordTrace (prefixWord ++ tailWord_469316) baseStart_469316 baseEnd_469316 := by
    simpa [prefixWord, tailWord_469316, baseEnd_469316] using wordTrace_append hprefix tailTrace_469316
  have hstable : (prefixWord ++ tailWord_469316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469316).length < 2 ^ (prefixWord ++ tailWord_469316).sum := by decide
  have hdescent : baseEnd_469316 < baseStart_469316 := by decide
  rcases family_descends (prefixWord ++ tailWord_469316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469318 : List Nat := [6, 1, 1, 11]
def baseStart_469318 : Nat := 118140960795 + 469318 * 2 ^ 59
def prefixEnd_469318 : Nat := 4983230072969 + 3 ^ 40 * 469318 * 2
def baseEnd_469318 : Nat := 1763041344723548421521

theorem tailTrace_469318 : CollatzResearch.WordTrace tailWord_469318 prefixEnd_469318 1763041344723548421521 := by
  unfold tailWord_469318
  simp only [CollatzResearch.WordTrace]
  refine ⟨534919803554641061818519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11411622475832342652128405 534919803554641061818519)
  ·
    refine ⟨802379705331961592727779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 534919803554641061818519 802379705331961592727779)
    ·
      refine ⟨1203569557997942389091669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802379705331961592727779 1203569557997942389091669)
      ·
        refine ⟨1763041344723548421521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1203569557997942389091669 1763041344723548421521)
        ·
          rfl

theorem cell19_469318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 11].length) (baseStart_469318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469318 prefixEnd_469318 := by exact prefixLift 469318
  have htrace : WordTrace (prefixWord ++ tailWord_469318) baseStart_469318 baseEnd_469318 := by
    simpa [prefixWord, tailWord_469318, baseEnd_469318] using wordTrace_append hprefix tailTrace_469318
  have hstable : (prefixWord ++ tailWord_469318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469318).length < 2 ^ (prefixWord ++ tailWord_469318).sum := by decide
  have hdescent : baseEnd_469318 < baseStart_469318 := by decide
  rcases family_descends (prefixWord ++ tailWord_469318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469354 : List Nat := [3, 1, 3, 3, 1, 2, 3, 3]
def baseStart_469354 : Nat := 118140960795 + 469354 * 2 ^ 59
def prefixEnd_469354 : Nat := 4983230072969 + 3 ^ 40 * 469354 * 2
def baseEnd_469354 : Nat := 142817303176570005343103

theorem tailTrace_469354 : CollatzResearch.WordTrace tailWord_469354 prefixEnd_469354 142817303176570005343103 := by
  unfold tailWord_469354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4279686685404523031625779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11412497827745394751002077 4279686685404523031625779)
  ·
    refine ⟨6419530028106784547438669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4279686685404523031625779 6419530028106784547438669)
    ·
      refine ⟨2407323760540044205289501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6419530028106784547438669 2407323760540044205289501)
      ·
        refine ⟨902746410202516576983563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2407323760540044205289501 902746410202516576983563)
        ·
          refine ⟨1354119615303774865475345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902746410202516576983563 1354119615303774865475345)
          ·
            refine ⟨1015589711477831149106509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354119615303774865475345 1015589711477831149106509)
            ·
              refine ⟨380846141804186680914941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1015589711477831149106509 380846141804186680914941)
              ·
                refine ⟨142817303176570005343103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380846141804186680914941 142817303176570005343103)
                ·
                  rfl

theorem cell19_469354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_469354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469354 prefixEnd_469354 := by exact prefixLift 469354
  have htrace : WordTrace (prefixWord ++ tailWord_469354) baseStart_469354 baseEnd_469354 := by
    simpa [prefixWord, tailWord_469354, baseEnd_469354] using wordTrace_append hprefix tailTrace_469354
  have hstable : (prefixWord ++ tailWord_469354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469354).length < 2 ^ (prefixWord ++ tailWord_469354).sum := by decide
  have hdescent : baseEnd_469354 < baseStart_469354 := by decide
  rcases family_descends (prefixWord ++ tailWord_469354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469409 : List Nat := [1, 2, 3, 5, 1, 2, 2, 3]
def baseStart_469409 : Nat := 118140960795 + 469409 * 2 ^ 59
def prefixEnd_469409 : Nat := 4983230072969 + 3 ^ 40 * 469409 * 2
def baseEnd_469409 : Nat := 142834038842346174120731

theorem tailTrace_469409 : CollatzResearch.WordTrace tailWord_469409 prefixEnd_469409 142834038842346174120731 := by
  unfold tailWord_469409
  simp only [CollatzResearch.WordTrace]
  refine ⟨17120752756418836519755281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11413835170945891013170187 17120752756418836519755281)
  ·
    refine ⟨12840564567314127389816461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17120752756418836519755281 12840564567314127389816461)
    ·
      refine ⟨4815211712742797771181173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12840564567314127389816461 4815211712742797771181173)
      ·
        refine ⟨451426098069637291048235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4815211712742797771181173 451426098069637291048235)
        ·
          refine ⟨677139147104455936572353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451426098069637291048235 677139147104455936572353)
          ·
            refine ⟨507854360328341952429265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677139147104455936572353 507854360328341952429265)
            ·
              refine ⟨380890770246256464321949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507854360328341952429265 380890770246256464321949)
              ·
                refine ⟨142834038842346174120731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380890770246256464321949 142834038842346174120731)
                ·
                  rfl

theorem cell19_469409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_469409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469409 prefixEnd_469409 := by exact prefixLift 469409
  have htrace : WordTrace (prefixWord ++ tailWord_469409) baseStart_469409 baseEnd_469409 := by
    simpa [prefixWord, tailWord_469409, baseEnd_469409] using wordTrace_append hprefix tailTrace_469409
  have hstable : (prefixWord ++ tailWord_469409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469409).length < 2 ^ (prefixWord ++ tailWord_469409).sum := by decide
  have hdescent : baseEnd_469409 < baseStart_469409 := by decide
  rcases family_descends (prefixWord ++ tailWord_469409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469428 : List Nat := [2, 5, 2, 2, 1, 2, 5]
def baseStart_469428 : Nat := 118140960795 + 469428 * 2 ^ 59
def prefixEnd_469428 : Nat := 4983230072969 + 3 ^ 40 * 469428 * 2
def baseEnd_469428 : Nat := 47613273418053253232819

theorem tailTrace_469428 : CollatzResearch.WordTrace tailWord_469428 prefixEnd_469428 47613273418053253232819 := by
  unfold tailWord_469428
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560722871675001382348469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11414297162233335176464625 8560722871675001382348469)
  ·
    refine ⟨802567769219531379595169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8560722871675001382348469 802567769219531379595169)
    ·
      refine ⟨601925826914648534696377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 802567769219531379595169 601925826914648534696377)
      ·
        refine ⟨451444370185986401022283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601925826914648534696377 451444370185986401022283)
        ·
          refine ⟨677166555278979601533425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451444370185986401022283 677166555278979601533425)
          ·
            refine ⟨507874916459234701150069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677166555278979601533425 507874916459234701150069)
            ·
              refine ⟨47613273418053253232819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 507874916459234701150069 47613273418053253232819)
              ·
                rfl

theorem cell19_469428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 5].length) (baseStart_469428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469428 prefixEnd_469428 := by exact prefixLift 469428
  have htrace : WordTrace (prefixWord ++ tailWord_469428) baseStart_469428 baseEnd_469428 := by
    simpa [prefixWord, tailWord_469428, baseEnd_469428] using wordTrace_append hprefix tailTrace_469428
  have hstable : (prefixWord ++ tailWord_469428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469428).length < 2 ^ (prefixWord ++ tailWord_469428).sum := by decide
  have hdescent : baseEnd_469428 < baseStart_469428 := by decide
  rcases family_descends (prefixWord ++ tailWord_469428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469508 : List Nat := [2, 3, 2, 3, 1, 1, 3, 4]
def baseStart_469508 : Nat := 118140960795 + 469508 * 2 ^ 59
def prefixEnd_469508 : Nat := 4983230072969 + 3 ^ 40 * 469508 * 2
def baseEnd_469508 : Nat := 142864163040743277920461

theorem tailTrace_469508 : CollatzResearch.WordTrace tailWord_469508 prefixEnd_469508 142864163040743277920461 := by
  unfold tailWord_469508
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562181791530088213804589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11416242388706784285072785 8562181791530088213804589)
  ·
    refine ⟨3210818171823783080176721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8562181791530088213804589 3210818171823783080176721)
    ·
      refine ⟨2408113628867837310132541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3210818171823783080176721 2408113628867837310132541)
      ·
        refine ⟨903042610825438991299703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2408113628867837310132541 903042610825438991299703)
        ·
          refine ⟨1354563916238158486949555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903042610825438991299703 1354563916238158486949555)
          ·
            refine ⟨2031845874357237730424333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354563916238158486949555 2031845874357237730424333)
            ·
              refine ⟨761942202883964148909125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2031845874357237730424333 761942202883964148909125)
              ·
                refine ⟨142864163040743277920461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 761942202883964148909125 142864163040743277920461)
                ·
                  rfl

theorem cell19_469508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_469508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469508 prefixEnd_469508 := by exact prefixLift 469508
  have htrace : WordTrace (prefixWord ++ tailWord_469508) baseStart_469508 baseEnd_469508 := by
    simpa [prefixWord, tailWord_469508, baseEnd_469508] using wordTrace_append hprefix tailTrace_469508
  have hstable : (prefixWord ++ tailWord_469508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469508).length < 2 ^ (prefixWord ++ tailWord_469508).sum := by decide
  have hdescent : baseEnd_469508 < baseStart_469508 := by decide
  rcases family_descends (prefixWord ++ tailWord_469508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469586 : List Nat := [3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_469586 : Nat := 118140960795 + 469586 * 2 ^ 59
def prefixEnd_469586 : Nat := 4983230072969 + 3 ^ 40 * 469586 * 2
def baseEnd_469586 : Nat := 142887897257662208186915

theorem tailTrace_469586 : CollatzResearch.WordTrace tailWord_469586 prefixEnd_469586 142887897257662208186915 := by
  unfold tailWord_469586
  simp only [CollatzResearch.WordTrace]
  refine ⟨4281802119194398937237153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11418138984518397165965741 4281802119194398937237153)
  ·
    refine ⟨3211351589395799202927865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4281802119194398937237153 3211351589395799202927865)
    ·
      refine ⟨2408513692046849402195899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3211351589395799202927865 2408513692046849402195899)
      ·
        refine ⟨3612770538070274103293849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408513692046849402195899 3612770538070274103293849)
        ·
          refine ⟨2709577903552705577470387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3612770538070274103293849 2709577903552705577470387)
          ·
            refine ⟨4064366855329058366205581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709577903552705577470387 4064366855329058366205581)
            ·
              refine ⟨1524137570748396887327093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4064366855329058366205581 1524137570748396887327093)
              ·
                refine ⟨142887897257662208186915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1524137570748396887327093 142887897257662208186915)
                ·
                  rfl

theorem cell19_469586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_469586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469586 prefixEnd_469586 := by exact prefixLift 469586
  have htrace : WordTrace (prefixWord ++ tailWord_469586) baseStart_469586 baseEnd_469586 := by
    simpa [prefixWord, tailWord_469586, baseEnd_469586] using wordTrace_append hprefix tailTrace_469586
  have hstable : (prefixWord ++ tailWord_469586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469586).length < 2 ^ (prefixWord ++ tailWord_469586).sum := by decide
  have hdescent : baseEnd_469586 < baseStart_469586 := by decide
  rcases family_descends (prefixWord ++ tailWord_469586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469664 : List Nat := [2, 1, 1, 4, 11]
def baseStart_469664 : Nat := 118140960795 + 469664 * 2 ^ 59
def prefixEnd_469664 : Nat := 4983230072969 + 3 ^ 40 * 469664 * 2
def baseEnd_469664 : Nat := 5293023387947449572347

theorem tailTrace_469664 : CollatzResearch.WordTrace tailWord_469664 prefixEnd_469664 5293023387947449572347 := by
  unfold tailWord_469664
  simp only [CollatzResearch.WordTrace]
  refine ⟨8565026685247507535144023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11420035580330010046858697 8565026685247507535144023)
  ·
    refine ⟨12847540027871261302716035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8565026685247507535144023 12847540027871261302716035)
    ·
      refine ⟨19271310041806891954074053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12847540027871261302716035 19271310041806891954074053)
      ·
        refine ⟨3613370632838792241388885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19271310041806891954074053 3613370632838792241388885)
        ·
          refine ⟨5293023387947449572347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3613370632838792241388885 5293023387947449572347)
          ·
            rfl

theorem cell19_469664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 11].length) (baseStart_469664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469664 prefixEnd_469664 := by exact prefixLift 469664
  have htrace : WordTrace (prefixWord ++ tailWord_469664) baseStart_469664 baseEnd_469664 := by
    simpa [prefixWord, tailWord_469664, baseEnd_469664] using wordTrace_append hprefix tailTrace_469664
  have hstable : (prefixWord ++ tailWord_469664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469664).length < 2 ^ (prefixWord ++ tailWord_469664).sum := by decide
  have hdescent : baseEnd_469664 < baseStart_469664 := by decide
  rcases family_descends (prefixWord ++ tailWord_469664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469717 : List Nat := [1, 3, 2, 5, 1, 1, 6]
def baseStart_469717 : Nat := 118140960795 + 469717 * 2 ^ 59
def prefixEnd_469717 : Nat := 4983230072969 + 3 ^ 40 * 469717 * 2
def baseEnd_469717 : Nat := 47642586190230906425149

theorem tailTrace_469717 : CollatzResearch.WordTrace tailWord_469717 prefixEnd_469717 47642586190230906425149 := by
  unfold tailWord_469717
  simp only [CollatzResearch.WordTrace]
  refine ⟨17131986439303005121967405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11421324292868670081311603 17131986439303005121967405)
  ·
    refine ⟨6424494914738626920737777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17131986439303005121967405 6424494914738626920737777)
    ·
      refine ⟨4818371186053970190553333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6424494914738626920737777 4818371186053970190553333)
      ·
        refine ⟨451722298692559705364375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4818371186053970190553333 451722298692559705364375)
        ·
          refine ⟨677583448038839558046563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451722298692559705364375 677583448038839558046563)
          ·
            refine ⟨1016375172058259337069845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677583448038839558046563 1016375172058259337069845)
            ·
              refine ⟨47642586190230906425149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1016375172058259337069845 47642586190230906425149)
              ·
                rfl

theorem cell19_469717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_469717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469717 prefixEnd_469717 := by exact prefixLift 469717
  have htrace : WordTrace (prefixWord ++ tailWord_469717) baseStart_469717 baseEnd_469717 := by
    simpa [prefixWord, tailWord_469717, baseEnd_469717] using wordTrace_append hprefix tailTrace_469717
  have hstable : (prefixWord ++ tailWord_469717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469717).length < 2 ^ (prefixWord ++ tailWord_469717).sum := by decide
  have hdescent : baseEnd_469717 < baseStart_469717 := by decide
  rcases family_descends (prefixWord ++ tailWord_469717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469721 : List Nat := [1, 2, 1, 2, 3, 2, 8]
def baseStart_469721 : Nat := 118140960795 + 469721 * 2 ^ 59
def prefixEnd_469721 : Nat := 4983230072969 + 3 ^ 40 * 469721 * 2
def baseEnd_469721 : Nat := 47642991903340631728849

theorem tailTrace_469721 : CollatzResearch.WordTrace tailWord_469721 prefixEnd_469721 47642991903340631728849 := by
  unfold tailWord_469721
  simp only [CollatzResearch.WordTrace]
  refine ⟨17132132331288513805113017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11421421554192342536742011 17132132331288513805113017)
  ·
    refine ⟨12849099248466385353834763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17132132331288513805113017 12849099248466385353834763)
    ·
      refine ⟨19273648872699578030752145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12849099248466385353834763 19273648872699578030752145)
      ·
        refine ⟨14455236654524683523064109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19273648872699578030752145 14455236654524683523064109)
        ·
          refine ⟨5420713745446756321149041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14455236654524683523064109 5420713745446756321149041)
          ·
            refine ⟨4065535309085067240861781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5420713745446756321149041 4065535309085067240861781)
            ·
              refine ⟨47642991903340631728849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4065535309085067240861781 47642991903340631728849)
              ·
                rfl

theorem cell19_469721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_469721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469721 prefixEnd_469721 := by exact prefixLift 469721
  have htrace : WordTrace (prefixWord ++ tailWord_469721) baseStart_469721 baseEnd_469721 := by
    simpa [prefixWord, tailWord_469721, baseEnd_469721] using wordTrace_append hprefix tailTrace_469721
  have hstable : (prefixWord ++ tailWord_469721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469721).length < 2 ^ (prefixWord ++ tailWord_469721).sum := by decide
  have hdescent : baseEnd_469721 < baseStart_469721 := by decide
  rcases family_descends (prefixWord ++ tailWord_469721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469740 : List Nat := [2, 2, 1, 1, 2, 2, 1, 8]
def baseStart_469740 : Nat := 118140960795 + 469740 * 2 ^ 59
def prefixEnd_469740 : Nat := 4983230072969 + 3 ^ 40 * 469740 * 2
def baseEnd_469740 : Nat := 142934757121835480764273

theorem tailTrace_469740 : CollatzResearch.WordTrace tailWord_469740 prefixEnd_469740 142934757121835480764273 := by
  unfold tailWord_469740
  simp only [CollatzResearch.WordTrace]
  refine ⟨8566412659109840025027337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11421883545479786700036449 8566412659109840025027337)
  ·
    refine ⟨6424809494332380018770503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8566412659109840025027337 6424809494332380018770503)
    ·
      refine ⟨9637214241498570028155755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6424809494332380018770503 9637214241498570028155755)
      ·
        refine ⟨14455821362247855042233633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9637214241498570028155755 14455821362247855042233633)
        ·
          refine ⟨10841866021685891281675225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14455821362247855042233633 10841866021685891281675225)
          ·
            refine ⟨8131399516264418461256419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10841866021685891281675225 8131399516264418461256419)
            ·
              refine ⟨12197099274396627691884629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131399516264418461256419 12197099274396627691884629)
              ·
                refine ⟨142934757121835480764273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12197099274396627691884629 142934757121835480764273)
                ·
                  rfl

theorem cell19_469740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_469740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469740 prefixEnd_469740 := by exact prefixLift 469740
  have htrace : WordTrace (prefixWord ++ tailWord_469740) baseStart_469740 baseEnd_469740 := by
    simpa [prefixWord, tailWord_469740, baseEnd_469740] using wordTrace_append hprefix tailTrace_469740
  have hstable : (prefixWord ++ tailWord_469740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469740).length < 2 ^ (prefixWord ++ tailWord_469740).sum := by decide
  have hdescent : baseEnd_469740 < baseStart_469740 := by decide
  rcases family_descends (prefixWord ++ tailWord_469740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469749 : List Nat := [1, 3, 6, 1, 1, 2, 2, 3]
def baseStart_469749 : Nat := 118140960795 + 469749 * 2 ^ 59
def prefixEnd_469749 : Nat := 4983230072969 + 3 ^ 40 * 469749 * 2
def baseEnd_469749 : Nat := 142937495685326126564249

theorem tailTrace_469749 : CollatzResearch.WordTrace tailWord_469749 prefixEnd_469749 142937495685326126564249 := by
  unfold tailWord_469749
  simp only [CollatzResearch.WordTrace]
  refine ⟨17133153575187074587132301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11422102383458049724754867 17133153575187074587132301)
  ·
    refine ⟨6424932590695152970174613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17133153575187074587132301 6424932590695152970174613)
    ·
      refine ⟨301168715188835295476935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6424932590695152970174613 301168715188835295476935)
      ·
        refine ⟨451753072783252943215403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301168715188835295476935 451753072783252943215403)
        ·
          refine ⟨677629609174879414823105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451753072783252943215403 677629609174879414823105)
          ·
            refine ⟨508222206881159561117329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677629609174879414823105 508222206881159561117329)
            ·
              refine ⟨381166655160869670837997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508222206881159561117329 381166655160869670837997)
              ·
                refine ⟨142937495685326126564249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381166655160869670837997 142937495685326126564249)
                ·
                  rfl

theorem cell19_469749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 3].length) (baseStart_469749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469749 prefixEnd_469749 := by exact prefixLift 469749
  have htrace : WordTrace (prefixWord ++ tailWord_469749) baseStart_469749 baseEnd_469749 := by
    simpa [prefixWord, tailWord_469749, baseEnd_469749] using wordTrace_append hprefix tailTrace_469749
  have hstable : (prefixWord ++ tailWord_469749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469749).length < 2 ^ (prefixWord ++ tailWord_469749).sum := by decide
  have hdescent : baseEnd_469749 < baseStart_469749 := by decide
  rcases family_descends (prefixWord ++ tailWord_469749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469816 : List Nat := [2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_469816 : Nat := 118140960795 + 469816 * 2 ^ 59
def prefixEnd_469816 : Nat := 4983230072969 + 3 ^ 40 * 469816 * 2
def baseEnd_469816 : Nat := 142957882769089823075177

theorem tailTrace_469816 : CollatzResearch.WordTrace tailWord_469816 prefixEnd_469816 142957882769089823075177 := by
  unfold tailWord_469816
  simp only [CollatzResearch.WordTrace]
  refine ⟨8567798632972172514910651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11423731510629563353214201 8567798632972172514910651)
  ·
    refine ⟨12851697949458258772365977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8567798632972172514910651 12851697949458258772365977)
    ·
      refine ⟨9638773462093694079274483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12851697949458258772365977 9638773462093694079274483)
      ·
        refine ⟨14458160193140541118911725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9638773462093694079274483 14458160193140541118911725)
        ·
          refine ⟨5421810072427702919591897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14458160193140541118911725 5421810072427702919591897)
          ·
            refine ⟨4066357554320777189693923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5421810072427702919591897 4066357554320777189693923)
            ·
              refine ⟨6099536331481165784540885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066357554320777189693923 6099536331481165784540885)
              ·
                refine ⟨142957882769089823075177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6099536331481165784540885 142957882769089823075177)
                ·
                  rfl

theorem cell19_469816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_469816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469816 prefixEnd_469816 := by exact prefixLift 469816
  have htrace : WordTrace (prefixWord ++ tailWord_469816) baseStart_469816 baseEnd_469816 := by
    simpa [prefixWord, tailWord_469816, baseEnd_469816] using wordTrace_append hprefix tailTrace_469816
  have hstable : (prefixWord ++ tailWord_469816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469816).length < 2 ^ (prefixWord ++ tailWord_469816).sum := by decide
  have hdescent : baseEnd_469816 < baseStart_469816 := by decide
  rcases family_descends (prefixWord ++ tailWord_469816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469911 : List Nat := [1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_469911 : Nat := 118140960795 + 469911 * 2 ^ 59
def prefixEnd_469911 : Nat := 4983230072969 + 3 ^ 40 * 469911 * 2
def baseEnd_469911 : Nat := 142986789828157750963807

theorem tailTrace_469911 : CollatzResearch.WordTrace tailWord_469911 prefixEnd_469911 142986789828157750963807 := by
  unfold tailWord_469911
  simp only [CollatzResearch.WordTrace]
  refine ⟨17139062200600176254529587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11426041467066784169686391 17139062200600176254529587)
  ·
    refine ⟨25708593300900264381794381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17139062200600176254529587 25708593300900264381794381)
    ·
      refine ⟨9640722487837599143172893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25708593300900264381794381 9640722487837599143172893)
      ·
        refine ⟨3615270932939099678689835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9640722487837599143172893 3615270932939099678689835)
        ·
          refine ⟨5422906399408649518034753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615270932939099678689835 5422906399408649518034753)
          ·
            refine ⟨4067179799556487138526065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5422906399408649518034753 4067179799556487138526065)
            ·
              refine ⟨3050384849667365353894549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4067179799556487138526065 3050384849667365353894549)
              ·
                refine ⟨142986789828157750963807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3050384849667365353894549 142986789828157750963807)
                ·
                  rfl

theorem cell19_469911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_469911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469911 prefixEnd_469911 := by exact prefixLift 469911
  have htrace : WordTrace (prefixWord ++ tailWord_469911) baseStart_469911 baseEnd_469911 := by
    simpa [prefixWord, tailWord_469911, baseEnd_469911] using wordTrace_append hprefix tailTrace_469911
  have hstable : (prefixWord ++ tailWord_469911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469911).length < 2 ^ (prefixWord ++ tailWord_469911).sum := by decide
  have hdescent : baseEnd_469911 < baseStart_469911 := by decide
  rcases family_descends (prefixWord ++ tailWord_469911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469958 : List Nat := [6, 1, 3, 1, 1, 1, 2, 4]
def baseStart_469958 : Nat := 118140960795 + 469958 * 2 ^ 59
def prefixEnd_469958 : Nat := 4983230072969 + 3 ^ 40 * 469958 * 2
def baseEnd_469958 : Nat := 143001091215275567919235

theorem tailTrace_469958 : CollatzResearch.WordTrace tailWord_469958 prefixEnd_469958 143001091215275567919235 := by
  unfold tailWord_469958
  simp only [CollatzResearch.WordTrace]
  refine ⟨535649263482184477546579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11427184287619935520993685 535649263482184477546579)
  ·
    refine ⟨803473895223276716319869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535649263482184477546579 803473895223276716319869)
    ·
      refine ⟨301302710708728768619951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 803473895223276716319869 301302710708728768619951)
      ·
        refine ⟨451954066063093152929927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301302710708728768619951 451954066063093152929927)
        ·
          refine ⟨677931099094639729394891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451954066063093152929927 677931099094639729394891)
          ·
            refine ⟨1016896648641959594092337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677931099094639729394891 1016896648641959594092337)
            ·
              refine ⟨762672486481469695569253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016896648641959594092337 762672486481469695569253)
              ·
                refine ⟨143001091215275567919235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 762672486481469695569253 143001091215275567919235)
                ·
                  rfl

theorem cell19_469958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_469958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469958 prefixEnd_469958 := by exact prefixLift 469958
  have htrace : WordTrace (prefixWord ++ tailWord_469958) baseStart_469958 baseEnd_469958 := by
    simpa [prefixWord, tailWord_469958, baseEnd_469958] using wordTrace_append hprefix tailTrace_469958
  have hstable : (prefixWord ++ tailWord_469958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469958).length < 2 ^ (prefixWord ++ tailWord_469958).sum := by decide
  have hdescent : baseEnd_469958 < baseStart_469958 := by decide
  rcases family_descends (prefixWord ++ tailWord_469958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469966 : List Nat := [4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_469966 : Nat := 118140960795 + 469966 * 2 ^ 59
def prefixEnd_469966 : Nat := 4983230072969 + 3 ^ 40 * 469966 * 2
def baseEnd_469966 : Nat := 143003525493933919741435

theorem tailTrace_469966 : CollatzResearch.WordTrace tailWord_469966 prefixEnd_469966 143003525493933919741435 := by
  unfold tailWord_469966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142633526925115080972719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11427378810267280431854501 2142633526925115080972719)
  ·
    refine ⟨3213950290387672621459079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2142633526925115080972719 3213950290387672621459079)
    ·
      refine ⟨4820925435581508932188619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3213950290387672621459079 4820925435581508932188619)
      ·
        refine ⟨7231388153372263398282929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4820925435581508932188619 7231388153372263398282929)
        ·
          refine ⟨5423541115029197548712197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7231388153372263398282929 5423541115029197548712197)
          ·
            refine ⟨1016913959067974540383537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5423541115029197548712197 1016913959067974540383537)
            ·
              refine ⟨762685469300980905287653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016913959067974540383537 762685469300980905287653)
              ·
                refine ⟨143003525493933919741435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 762685469300980905287653 143003525493933919741435)
                ·
                  rfl

theorem cell19_469966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_469966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469966 prefixEnd_469966 := by exact prefixLift 469966
  have htrace : WordTrace (prefixWord ++ tailWord_469966) baseStart_469966 baseEnd_469966 := by
    simpa [prefixWord, tailWord_469966, baseEnd_469966] using wordTrace_append hprefix tailTrace_469966
  have hstable : (prefixWord ++ tailWord_469966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469966).length < 2 ^ (prefixWord ++ tailWord_469966).sum := by decide
  have hdescent : baseEnd_469966 < baseStart_469966 := by decide
  rcases family_descends (prefixWord ++ tailWord_469966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_469987 : List Nat := [1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_469987 : Nat := 118140960795 + 469987 * 2 ^ 59
def prefixEnd_469987 : Nat := 4983230072969 + 3 ^ 40 * 469987 * 2
def baseEnd_469987 : Nat := 143009915475412093274711

theorem tailTrace_469987 : CollatzResearch.WordTrace tailWord_469987 prefixEnd_469987 143009915475412093274711 := by
  unfold tailWord_469987
  simp only [CollatzResearch.WordTrace]
  refine ⟨17141834148324841234296215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11427889432216560822864143 17141834148324841234296215)
  ·
    refine ⟨25712751222487261851444323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17141834148324841234296215 25712751222487261851444323)
    ·
      refine ⟨38569126833730892777166485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25712751222487261851444323 38569126833730892777166485)
      ·
        refine ⟨1807927820331135598929679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38569126833730892777166485 1807927820331135598929679)
        ·
          refine ⟨2711891730496703398394519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807927820331135598929679 2711891730496703398394519)
          ·
            refine ⟨4067837595745055097591779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711891730496703398394519 4067837595745055097591779)
            ·
              refine ⟨6101756393617582646387669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067837595745055097591779 6101756393617582646387669)
              ·
                refine ⟨143009915475412093274711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6101756393617582646387669 143009915475412093274711)
                ·
                  rfl

theorem cell19_469987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_469987 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_469987 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_469987 prefixEnd_469987 := by exact prefixLift 469987
  have htrace : WordTrace (prefixWord ++ tailWord_469987) baseStart_469987 baseEnd_469987 := by
    simpa [prefixWord, tailWord_469987, baseEnd_469987] using wordTrace_append hprefix tailTrace_469987
  have hstable : (prefixWord ++ tailWord_469987).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_469987).length < 2 ^ (prefixWord ++ tailWord_469987).sum := by decide
  have hdescent : baseEnd_469987 < baseStart_469987 := by decide
  rcases family_descends (prefixWord ++ tailWord_469987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470002 : List Nat := [3, 2, 1, 5, 2, 6]
def baseStart_470002 : Nat := 118140960795 + 470002 * 2 ^ 59
def prefixEnd_470002 : Nat := 4983230072969 + 3 ^ 40 * 470002 * 2
def baseEnd_470002 : Nat := 15890497749766278104593

theorem tailTrace_470002 : CollatzResearch.WordTrace tailWord_470002 prefixEnd_470002 15890497749766278104593 := by
  unfold tailWord_470002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285595310817624699023065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11428254162180332530728173 4285595310817624699023065)
  ·
    refine ⟨3214196483113218524267299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4285595310817624699023065 3214196483113218524267299)
    ·
      refine ⟨4821294724669827786400949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3214196483113218524267299 4821294724669827786400949)
      ·
        refine ⟨451996380437796354975089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4821294724669827786400949 451996380437796354975089)
        ·
          refine ⟨338997285328347266231317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451996380437796354975089 338997285328347266231317)
          ·
            refine ⟨15890497749766278104593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 338997285328347266231317 15890497749766278104593)
            ·
              rfl

theorem cell19_470002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 6].length) (baseStart_470002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470002 prefixEnd_470002 := by exact prefixLift 470002
  have htrace : WordTrace (prefixWord ++ tailWord_470002) baseStart_470002 baseEnd_470002 := by
    simpa [prefixWord, tailWord_470002, baseEnd_470002] using wordTrace_append hprefix tailTrace_470002
  have hstable : (prefixWord ++ tailWord_470002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470002).length < 2 ^ (prefixWord ++ tailWord_470002).sum := by decide
  have hdescent : baseEnd_470002 < baseStart_470002 := by decide
  rcases family_descends (prefixWord ++ tailWord_470002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470042 : List Nat := [3, 1, 1, 3, 1, 2, 5, 3]
def baseStart_470042 : Nat := 118140960795 + 470042 * 2 ^ 59
def prefixEnd_470042 : Nat := 4983230072969 + 3 ^ 40 * 470042 * 2
def baseEnd_470042 : Nat := 143026651141188262052339

theorem tailTrace_470042 : CollatzResearch.WordTrace tailWord_470042 prefixEnd_470042 143026651141188262052339 := by
  unfold tailWord_470042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285960040781396406887095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11429226775417057085032253 4285960040781396406887095)
  ·
    refine ⟨6428940061172094610330643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4285960040781396406887095 6428940061172094610330643)
    ·
      refine ⟨9643410091758141915495965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428940061172094610330643 9643410091758141915495965)
      ·
        refine ⟨3616278784409303218310987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9643410091758141915495965 3616278784409303218310987)
        ·
          refine ⟨5424418176613954827466481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616278784409303218310987 5424418176613954827466481)
          ·
            refine ⟨4068313632460466120599861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5424418176613954827466481 4068313632460466120599861)
            ·
              refine ⟨381404403043168698806237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4068313632460466120599861 381404403043168698806237)
              ·
                refine ⟨143026651141188262052339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381404403043168698806237 143026651141188262052339)
                ·
                  rfl

theorem cell19_470042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_470042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470042 prefixEnd_470042 := by exact prefixLift 470042
  have htrace : WordTrace (prefixWord ++ tailWord_470042) baseStart_470042 baseEnd_470042 := by
    simpa [prefixWord, tailWord_470042, baseEnd_470042] using wordTrace_append hprefix tailTrace_470042
  have hstable : (prefixWord ++ tailWord_470042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470042).length < 2 ^ (prefixWord ++ tailWord_470042).sum := by decide
  have hdescent : baseEnd_470042 < baseStart_470042 := by decide
  rcases family_descends (prefixWord ++ tailWord_470042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470101 : List Nat := [1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_470101 : Nat := 118140960795 + 470101 * 2 ^ 59
def prefixEnd_470101 : Nat := 4983230072969 + 3 ^ 40 * 470101 * 2
def baseEnd_470101 : Nat := 143044603946293606741067

theorem tailTrace_470101 : CollatzResearch.WordTrace tailWord_470101 prefixEnd_470101 143044603946293606741067 := by
  unfold tailWord_470101
  simp only [CollatzResearch.WordTrace]
  refine ⟨17145992069911838703946157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11430661379941225802630771 17145992069911838703946157)
  ·
    refine ⟨6429747026216939513979809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17145992069911838703946157 6429747026216939513979809)
    ·
      refine ⟨4822310269662704635484857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6429747026216939513979809 4822310269662704635484857)
      ·
        refine ⟨3616732702247028476613643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4822310269662704635484857 3616732702247028476613643)
        ·
          refine ⟨5425099053370542714920465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616732702247028476613643 5425099053370542714920465)
          ·
            refine ⟨4068824290027907036190349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5425099053370542714920465 4068824290027907036190349)
            ·
              refine ⟨1525809108760465138571381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4068824290027907036190349 1525809108760465138571381)
              ·
                refine ⟨143044603946293606741067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1525809108760465138571381 143044603946293606741067)
                ·
                  rfl

theorem cell19_470101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_470101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470101 prefixEnd_470101 := by exact prefixLift 470101
  have htrace : WordTrace (prefixWord ++ tailWord_470101) baseStart_470101 baseEnd_470101 := by
    simpa [prefixWord, tailWord_470101, baseEnd_470101] using wordTrace_append hprefix tailTrace_470101
  have hstable : (prefixWord ++ tailWord_470101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470101).length < 2 ^ (prefixWord ++ tailWord_470101).sum := by decide
  have hdescent : baseEnd_470101 < baseStart_470101 := by decide
  rcases family_descends (prefixWord ++ tailWord_470101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470137 : List Nat := [1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_470137 : Nat := 118140960795 + 470137 * 2 ^ 59
def prefixEnd_470137 : Nat := 4983230072969 + 3 ^ 40 * 470137 * 2
def baseEnd_470137 : Nat := 143055558200256189940969

theorem tailTrace_470137 : CollatzResearch.WordTrace tailWord_470137 prefixEnd_470137 143055558200256189940969 := by
  unfold tailWord_470137
  simp only [CollatzResearch.WordTrace]
  refine ⟨17147305097781416852256665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11431536731854277901504443 17147305097781416852256665)
  ·
    refine ⟨12860478823336062639192499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17147305097781416852256665 12860478823336062639192499)
    ·
      refine ⟨19290718235004093958788749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12860478823336062639192499 19290718235004093958788749)
      ·
        refine ⟨7234019338126535234545781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19290718235004093958788749 7234019338126535234545781)
        ·
          refine ⟨678189312949362678238667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7234019338126535234545781 678189312949362678238667)
          ·
            refine ⟨1017283969424044017358001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678189312949362678238667 1017283969424044017358001)
            ·
              refine ⟨762962977068033013018501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017283969424044017358001 762962977068033013018501)
              ·
                refine ⟨143055558200256189940969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 762962977068033013018501 143055558200256189940969)
                ·
                  rfl

theorem cell19_470137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_470137 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470137 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470137 prefixEnd_470137 := by exact prefixLift 470137
  have htrace : WordTrace (prefixWord ++ tailWord_470137) baseStart_470137 baseEnd_470137 := by
    simpa [prefixWord, tailWord_470137, baseEnd_470137] using wordTrace_append hprefix tailTrace_470137
  have hstable : (prefixWord ++ tailWord_470137).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470137).length < 2 ^ (prefixWord ++ tailWord_470137).sum := by decide
  have hdescent : baseEnd_470137 < baseStart_470137 := by decide
  rcases family_descends (prefixWord ++ tailWord_470137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470175 : List Nat := [1, 1, 2, 6, 3, 6]
def baseStart_470175 : Nat := 118140960795 + 470175 * 2 ^ 59
def prefixEnd_470175 : Nat := 4983230072969 + 3 ^ 40 * 470175 * 2
def baseEnd_470175 : Nat := 15896346780431484566269

theorem tailTrace_470175 : CollatzResearch.WordTrace tailWord_470175 prefixEnd_470175 15896346780431484566269 := by
  unfold tailWord_470175
  simp only [CollatzResearch.WordTrace]
  refine ⟨17148691071643749342139979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11432460714429166228093319 17148691071643749342139979)
  ·
    refine ⟨25723036607465624013209969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17148691071643749342139979 25723036607465624013209969)
    ·
      refine ⟨19292277455599218009907477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25723036607465624013209969 19292277455599218009907477)
      ·
        refine ⟨904325505731213344214413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19292277455599218009907477 904325505731213344214413)
        ·
          refine ⟨339122064649205004080405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 904325505731213344214413 339122064649205004080405)
          ·
            refine ⟨15896346780431484566269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 339122064649205004080405 15896346780431484566269)
            ·
              rfl

theorem cell19_470175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 6].length) (baseStart_470175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470175 prefixEnd_470175 := by exact prefixLift 470175
  have htrace : WordTrace (prefixWord ++ tailWord_470175) baseStart_470175 baseEnd_470175 := by
    simpa [prefixWord, tailWord_470175, baseEnd_470175] using wordTrace_append hprefix tailTrace_470175
  have hstable : (prefixWord ++ tailWord_470175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470175).length < 2 ^ (prefixWord ++ tailWord_470175).sum := by decide
  have hdescent : baseEnd_470175 < baseStart_470175 := by decide
  rcases family_descends (prefixWord ++ tailWord_470175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470194 : List Nat := [3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_470194 : Nat := 118140960795 + 470194 * 2 ^ 59
def prefixEnd_470194 : Nat := 4983230072969 + 3 ^ 40 * 470194 * 2
def baseEnd_470194 : Nat := 143072902435696946674147

theorem tailTrace_470194 : CollatzResearch.WordTrace tailWord_470194 prefixEnd_470194 143072902435696946674147 := by
  unfold tailWord_470194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287346014643728896770409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11432922705716610391387757 4287346014643728896770409)
  ·
    refine ⟨3215509510982796672577807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4287346014643728896770409 3215509510982796672577807)
    ·
      refine ⟨4823264266474195008866711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3215509510982796672577807 4823264266474195008866711)
      ·
        refine ⟨7234896399711292513300067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823264266474195008866711 7234896399711292513300067)
        ·
          refine ⟨10852344599566938769950101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7234896399711292513300067 10852344599566938769950101)
          ·
            refine ⟨508703653104700254841411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10852344599566938769950101 508703653104700254841411)
            ·
              refine ⟨763055479657050382262117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508703653104700254841411 763055479657050382262117)
              ·
                refine ⟨143072902435696946674147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 763055479657050382262117 143072902435696946674147)
                ·
                  rfl

theorem cell19_470194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_470194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470194 prefixEnd_470194 := by exact prefixLift 470194
  have htrace : WordTrace (prefixWord ++ tailWord_470194) baseStart_470194 baseEnd_470194 := by
    simpa [prefixWord, tailWord_470194, baseEnd_470194] using wordTrace_append hprefix tailTrace_470194
  have hstable : (prefixWord ++ tailWord_470194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470194).length < 2 ^ (prefixWord ++ tailWord_470194).sum := by decide
  have hdescent : baseEnd_470194 < baseStart_470194 := by decide
  rcases family_descends (prefixWord ++ tailWord_470194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470230 : List Nat := [5, 2, 1, 2, 2, 1, 6]
def baseStart_470230 : Nat := 118140960795 + 470230 * 2 ^ 59
def prefixEnd_470230 : Nat := 4983230072969 + 3 ^ 40 * 470230 * 2
def baseEnd_470230 : Nat := 47694618896553176624683

theorem tailTrace_470230 : CollatzResearch.WordTrace tailWord_470230 prefixEnd_470230 47694618896553176624683 := by
  unfold tailWord_470230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071918567902780858462009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11433798057629662490261429 1071918567902780858462009)
  ·
    refine ⟨803938925927085643846507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1071918567902780858462009 803938925927085643846507)
    ·
      refine ⟨1205908388890628465769761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803938925927085643846507 1205908388890628465769761)
      ·
        refine ⟨904431291667971349327321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1205908388890628465769761 904431291667971349327321)
        ·
          refine ⟨678323468750978511995491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904431291667971349327321 678323468750978511995491)
          ·
            refine ⟨1017485203126467767993237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678323468750978511995491 1017485203126467767993237)
            ·
              refine ⟨47694618896553176624683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1017485203126467767993237 47694618896553176624683)
              ·
                rfl

theorem cell19_470230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_470230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470230 prefixEnd_470230 := by exact prefixLift 470230
  have htrace : WordTrace (prefixWord ++ tailWord_470230) baseStart_470230 baseEnd_470230 := by
    simpa [prefixWord, tailWord_470230, baseEnd_470230] using wordTrace_append hprefix tailTrace_470230
  have hstable : (prefixWord ++ tailWord_470230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470230).length < 2 ^ (prefixWord ++ tailWord_470230).sum := by decide
  have hdescent : baseEnd_470230 < baseStart_470230 := by decide
  rcases family_descends (prefixWord ++ tailWord_470230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470268 : List Nat := [2, 2, 2, 1, 5, 2, 2, 3]
def baseStart_470268 : Nat := 118140960795 + 470268 * 2 ^ 59
def prefixEnd_470268 : Nat := 4983230072969 + 3 ^ 40 * 470268 * 2
def baseEnd_470268 : Nat := 143095419513286701029501

theorem tailTrace_470268 : CollatzResearch.WordTrace tailWord_470268 prefixEnd_470268 143095419513286701029501 := by
  unfold tailWord_470268
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576041530153413112637729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11434722040204550816850305 8576041530153413112637729)
  ·
    refine ⟨6432031147615059834478297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8576041530153413112637729 6432031147615059834478297)
    ·
      refine ⟨4824023360711294875858723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6432031147615059834478297 4824023360711294875858723)
      ·
        refine ⟨7236035041066942313788085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4824023360711294875858723 7236035041066942313788085)
        ·
          refine ⟨678378285100025841917633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7236035041066942313788085 678378285100025841917633)
          ·
            refine ⟨508783713825019381438225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678378285100025841917633 508783713825019381438225)
            ·
              refine ⟨381587785368764536078669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508783713825019381438225 381587785368764536078669)
              ·
                refine ⟨143095419513286701029501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381587785368764536078669 143095419513286701029501)
                ·
                  rfl

theorem cell19_470268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_470268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470268 prefixEnd_470268 := by exact prefixLift 470268
  have htrace : WordTrace (prefixWord ++ tailWord_470268) baseStart_470268 baseEnd_470268 := by
    simpa [prefixWord, tailWord_470268, baseEnd_470268] using wordTrace_append hprefix tailTrace_470268
  have hstable : (prefixWord ++ tailWord_470268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470268).length < 2 ^ (prefixWord ++ tailWord_470268).sum := by decide
  have hdescent : baseEnd_470268 < baseStart_470268 := by decide
  rcases family_descends (prefixWord ++ tailWord_470268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470270 : List Nat := [4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_470270 : Nat := 118140960795 + 470270 * 2 ^ 59
def prefixEnd_470270 : Nat := 4983230072969 + 3 ^ 40 * 470270 * 2
def baseEnd_470270 : Nat := 143096028082951288985051

theorem tailTrace_470270 : CollatzResearch.WordTrace tailWord_470270 prefixEnd_470270 143096028082951288985051 := by
  unfold tailWord_470270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144019500787447570856033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11434770670866387044565509 2144019500787447570856033)
  ·
    refine ⟨1608014625590585678142025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2144019500787447570856033 1608014625590585678142025)
    ·
      refine ⟨1206010969192939258606519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1608014625590585678142025 1206010969192939258606519)
      ·
        refine ⟨1809016453789408887909779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206010969192939258606519 1809016453789408887909779)
        ·
          refine ⟨2713524680684113331864669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809016453789408887909779 2713524680684113331864669)
          ·
            refine ⟨1017571755256542499449251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2713524680684113331864669 1017571755256542499449251)
            ·
              refine ⟨1526357632884813749173877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017571755256542499449251 1526357632884813749173877)
              ·
                refine ⟨143096028082951288985051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1526357632884813749173877 143096028082951288985051)
                ·
                  rfl

theorem cell19_470270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_470270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470270 prefixEnd_470270 := by exact prefixLift 470270
  have htrace : WordTrace (prefixWord ++ tailWord_470270) baseStart_470270 baseEnd_470270 := by
    simpa [prefixWord, tailWord_470270, baseEnd_470270] using wordTrace_append hprefix tailTrace_470270
  have hstable : (prefixWord ++ tailWord_470270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470270).length < 2 ^ (prefixWord ++ tailWord_470270).sum := by decide
  have hdescent : baseEnd_470270 < baseStart_470270 := by decide
  rcases family_descends (prefixWord ++ tailWord_470270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470342 : List Nat := [6, 1, 1, 3, 2, 6]
def baseStart_470342 : Nat := 118140960795 + 470342 * 2 ^ 59
def prefixEnd_470342 : Nat := 4983230072969 + 3 ^ 40 * 470342 * 2
def baseEnd_470342 : Nat := 15901992954541828376095

theorem tailTrace_470342 : CollatzResearch.WordTrace tailWord_470342 prefixEnd_470342 15901992954541828376095 := by
  unfold tailWord_470342
  simp only [CollatzResearch.WordTrace]
  refine ⟨536086939438710526983415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11436521374692491242312853 536086939438710526983415)
  ·
    refine ⟨804130409158065790475123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536086939438710526983415 804130409158065790475123)
    ·
      refine ⟨1206195613737098685712685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 804130409158065790475123 1206195613737098685712685)
      ·
        refine ⟨452323355151412007142257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1206195613737098685712685 452323355151412007142257)
        ·
          refine ⟨339242516363559005356693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452323355151412007142257 339242516363559005356693)
          ·
            refine ⟨15901992954541828376095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 339242516363559005356693 15901992954541828376095)
            ·
              rfl

theorem cell19_470342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 6].length) (baseStart_470342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470342 prefixEnd_470342 := by exact prefixLift 470342
  have htrace : WordTrace (prefixWord ++ tailWord_470342) baseStart_470342 baseEnd_470342 := by
    simpa [prefixWord, tailWord_470342, baseEnd_470342] using wordTrace_append hprefix tailTrace_470342
  have hstable : (prefixWord ++ tailWord_470342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470342).length < 2 ^ (prefixWord ++ tailWord_470342).sum := by decide
  have hdescent : baseEnd_470342 < baseStart_470342 := by decide
  rcases family_descends (prefixWord ++ tailWord_470342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470460 : List Nat := [2, 2, 2, 4, 2, 2, 5]
def baseStart_470460 : Nat := 118140960795 + 470460 * 2 ^ 59
def prefixEnd_470460 : Nat := 4983230072969 + 3 ^ 40 * 470460 * 2
def baseEnd_470460 : Nat := 47717947400362381587437

theorem tailTrace_470460 : CollatzResearch.WordTrace tailWord_470460 prefixEnd_470460 47717947400362381587437 := by
  unfold tailWord_470460
  simp only [CollatzResearch.WordTrace]
  refine ⟨8579542937805621508132417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11439390583740828677509889 8579542937805621508132417)
  ·
    refine ⟨6434657203354216131099313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8579542937805621508132417 6434657203354216131099313)
    ·
      refine ⟨4825992902515662098324485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6434657203354216131099313 4825992902515662098324485)
      ·
        refine ⟨904873669221686643435841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4825992902515662098324485 904873669221686643435841)
        ·
          refine ⟨678655251916264982576881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904873669221686643435841 678655251916264982576881)
          ·
            refine ⟨508991438937198736932661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678655251916264982576881 508991438937198736932661)
            ·
              refine ⟨47717947400362381587437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 508991438937198736932661 47717947400362381587437)
              ·
                rfl

theorem cell19_470460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_470460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470460 prefixEnd_470460 := by exact prefixLift 470460
  have htrace : WordTrace (prefixWord ++ tailWord_470460) baseStart_470460 baseEnd_470460 := by
    simpa [prefixWord, tailWord_470460, baseEnd_470460] using wordTrace_append hprefix tailTrace_470460
  have hstable : (prefixWord ++ tailWord_470460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470460).length < 2 ^ (prefixWord ++ tailWord_470460).sum := by decide
  have hdescent : baseEnd_470460 < baseStart_470460 := by decide
  rcases family_descends (prefixWord ++ tailWord_470460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470464 : List Nat := [2, 1, 1, 2, 3, 1, 9]
def baseStart_470464 : Nat := 118140960795 + 470464 * 2 ^ 59
def prefixEnd_470464 : Nat := 4983230072969 + 3 ^ 40 * 470464 * 2
def baseEnd_470464 : Nat := 47718353113472106891137

theorem tailTrace_470464 : CollatzResearch.WordTrace tailWord_470464 prefixEnd_470464 47718353113472106891137 := by
  unfold tailWord_470464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8579615883798375849705223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11439487845064501132940297 8579615883798375849705223)
  ·
    refine ⟨12869423825697563774557835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8579615883798375849705223 12869423825697563774557835)
    ·
      refine ⟨19304135738546345661836753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12869423825697563774557835 19304135738546345661836753)
      ·
        refine ⟨14478101803909759246377565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19304135738546345661836753 14478101803909759246377565)
        ·
          refine ⟨5429288176466159717391587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14478101803909759246377565 5429288176466159717391587)
          ·
            refine ⟨8143932264699239576087381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5429288176466159717391587 8143932264699239576087381)
            ·
              refine ⟨47718353113472106891137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8143932264699239576087381 47718353113472106891137)
              ·
                rfl

theorem cell19_470464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_470464 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470464 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470464 prefixEnd_470464 := by exact prefixLift 470464
  have htrace : WordTrace (prefixWord ++ tailWord_470464) baseStart_470464 baseEnd_470464 := by
    simpa [prefixWord, tailWord_470464, baseEnd_470464] using wordTrace_append hprefix tailTrace_470464
  have hstable : (prefixWord ++ tailWord_470464).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470464).length < 2 ^ (prefixWord ++ tailWord_470464).sum := by decide
  have hdescent : baseEnd_470464 < baseStart_470464 := by decide
  rcases family_descends (prefixWord ++ tailWord_470464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470538 : List Nat := [3, 1, 2, 2, 2, 2, 3, 4]
def baseStart_470538 : Nat := 118140960795 + 470538 * 2 ^ 59
def prefixEnd_470538 : Nat := 4983230072969 + 3 ^ 40 * 470538 * 2
def baseEnd_470538 : Nat := 143177576418006075028765

theorem tailTrace_470538 : CollatzResearch.WordTrace tailWord_470538 prefixEnd_470538 143177576418006075028765 := by
  unfold tailWord_470538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4290482692332165584401067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11441287179552441558402845 4290482692332165584401067)
  ·
    refine ⟨6435724038498248376601601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4290482692332165584401067 6435724038498248376601601)
    ·
      refine ⟨4826793028873686282451201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6435724038498248376601601 4826793028873686282451201)
      ·
        refine ⟨3620094771655264711838401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4826793028873686282451201 3620094771655264711838401)
        ·
          refine ⟨2715071078741448533878801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3620094771655264711838401 2715071078741448533878801)
          ·
            refine ⟨2036303309056086400409101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715071078741448533878801 2036303309056086400409101)
            ·
              refine ⟨763613740896032400153413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2036303309056086400409101 763613740896032400153413)
              ·
                refine ⟨143177576418006075028765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 763613740896032400153413 143177576418006075028765)
                ·
                  rfl

theorem cell19_470538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_470538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470538 prefixEnd_470538 := by exact prefixLift 470538
  have htrace : WordTrace (prefixWord ++ tailWord_470538) baseStart_470538 baseEnd_470538 := by
    simpa [prefixWord, tailWord_470538, baseEnd_470538] using wordTrace_append hprefix tailTrace_470538
  have hstable : (prefixWord ++ tailWord_470538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470538).length < 2 ^ (prefixWord ++ tailWord_470538).sum := by decide
  have hdescent : baseEnd_470538 < baseStart_470538 := by decide
  rcases family_descends (prefixWord ++ tailWord_470538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470559 : List Nat := [1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_470559 : Nat := 118140960795 + 470559 * 2 ^ 59
def prefixEnd_470559 : Nat := 4983230072969 + 3 ^ 40 * 470559 * 2
def baseEnd_470559 : Nat := 143183966399484248562041

theorem tailTrace_470559 : CollatzResearch.WordTrace tailWord_470559 prefixEnd_470559 143183966399484248562041 := by
  unfold tailWord_470559
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162696702252582924118731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11441797801501721949412487 17162696702252582924118731)
  ·
    refine ⟨25744045053378874386178097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17162696702252582924118731 25744045053378874386178097)
    ·
      refine ⟨19308033790034155789633573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25744045053378874386178097 19308033790034155789633573)
      ·
        refine ⟨3620256335631404210556295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19308033790034155789633573 3620256335631404210556295)
        ·
          refine ⟨5430384503447106315834443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620256335631404210556295 5430384503447106315834443)
          ·
            refine ⟨8145576755170659473751665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430384503447106315834443 8145576755170659473751665)
            ·
              refine ⟨6109182566377994605313749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8145576755170659473751665 6109182566377994605313749)
              ·
                refine ⟨143183966399484248562041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6109182566377994605313749 143183966399484248562041)
                ·
                  rfl

theorem cell19_470559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_470559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470559 prefixEnd_470559 := by exact prefixLift 470559
  have htrace : WordTrace (prefixWord ++ tailWord_470559) baseStart_470559 baseEnd_470559 := by
    simpa [prefixWord, tailWord_470559, baseEnd_470559] using wordTrace_append hprefix tailTrace_470559
  have hstable : (prefixWord ++ tailWord_470559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470559).length < 2 ^ (prefixWord ++ tailWord_470559).sum := by decide
  have hdescent : baseEnd_470559 < baseStart_470559 := by decide
  rcases family_descends (prefixWord ++ tailWord_470559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470597 : List Nat := [1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_470597 : Nat := 118140960795 + 470597 * 2 ^ 59
def prefixEnd_470597 : Nat := 4983230072969 + 3 ^ 40 * 470597 * 2
def baseEnd_470597 : Nat := 143195529223111419717493

theorem tailTrace_470597 : CollatzResearch.WordTrace tailWord_470597 prefixEnd_470597 143195529223111419717493 := by
  unfold tailWord_470597
  simp only [CollatzResearch.WordTrace]
  refine ⟨17164082676114915414002045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11442721784076610276001363 17164082676114915414002045)
  ·
    refine ⟨6436531003543093280250767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17164082676114915414002045 6436531003543093280250767)
    ·
      refine ⟨9654796505314639920376151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6436531003543093280250767 9654796505314639920376151)
      ·
        refine ⟨14482194757971959880564227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654796505314639920376151 14482194757971959880564227)
        ·
          refine ⟨21723292136957939820846341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14482194757971959880564227 21723292136957939820846341)
          ·
            refine ⟨4073117275679613716408689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21723292136957939820846341 4073117275679613716408689)
            ·
              refine ⟨3054837956759710287306517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4073117275679613716408689 3054837956759710287306517)
              ·
                refine ⟨143195529223111419717493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3054837956759710287306517 143195529223111419717493)
                ·
                  rfl

theorem cell19_470597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_470597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470597 prefixEnd_470597 := by exact prefixLift 470597
  have htrace : WordTrace (prefixWord ++ tailWord_470597) baseStart_470597 baseEnd_470597 := by
    simpa [prefixWord, tailWord_470597, baseEnd_470597] using wordTrace_append hprefix tailTrace_470597
  have hstable : (prefixWord ++ tailWord_470597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470597).length < 2 ^ (prefixWord ++ tailWord_470597).sum := by decide
  have hdescent : baseEnd_470597 < baseStart_470597 := by decide
  rcases family_descends (prefixWord ++ tailWord_470597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470690 : List Nat := [3, 3, 1, 4, 8]
def baseStart_470690 : Nat := 118140960795 + 470690 * 2 ^ 59
def prefixEnd_470690 : Nat := 4983230072969 + 3 ^ 40 * 470690 * 2
def baseEnd_470690 : Nat := 5304586211574620727799

theorem tailTrace_470690 : CollatzResearch.WordTrace tailWord_470690 prefixEnd_470690 5304586211574620727799 := by
  unfold tailWord_470690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291868666194498074284381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11444983109851994864758349 4291868666194498074284381)
  ·
    refine ⟨1609450749822936777856643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4291868666194498074284381 1609450749822936777856643)
    ·
      refine ⟨2414176124734405166784965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1609450749822936777856643 2414176124734405166784965)
      ·
        refine ⟨452658023387700968772181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2414176124734405166784965 452658023387700968772181)
        ·
          refine ⟨5304586211574620727799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 452658023387700968772181 5304586211574620727799)
          ·
            rfl

theorem cell19_470690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 8].length) (baseStart_470690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470690 prefixEnd_470690 := by exact prefixLift 470690
  have htrace : WordTrace (prefixWord ++ tailWord_470690) baseStart_470690 baseEnd_470690 := by
    simpa [prefixWord, tailWord_470690, baseEnd_470690] using wordTrace_append hprefix tailTrace_470690
  have hstable : (prefixWord ++ tailWord_470690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470690).length < 2 ^ (prefixWord ++ tailWord_470690).sum := by decide
  have hdescent : baseEnd_470690 < baseStart_470690 := by decide
  rcases family_descends (prefixWord ++ tailWord_470690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470692 : List Nat := [2, 3, 1, 2, 2, 9]
def baseStart_470692 : Nat := 118140960795 + 470692 * 2 ^ 59
def prefixEnd_470692 : Nat := 4983230072969 + 3 ^ 40 * 470692 * 2
def baseEnd_470692 : Nat := 15913826253575483067347

theorem tailTrace_470692 : CollatzResearch.WordTrace tailWord_470692 prefixEnd_470692 15913826253575483067347 := by
  unfold tailWord_470692
  simp only [CollatzResearch.WordTrace]
  refine ⟨8583773805385373319355165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11445031740513831092473553 8583773805385373319355165)
  ·
    refine ⟨3218915177019514994758187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8583773805385373319355165 3218915177019514994758187)
    ·
      refine ⟨4828372765529272492137281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3218915177019514994758187 4828372765529272492137281)
      ·
        refine ⟨3621279574146954369102961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4828372765529272492137281 3621279574146954369102961)
        ·
          refine ⟨2715959680610215776827221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3621279574146954369102961 2715959680610215776827221)
          ·
            refine ⟨15913826253575483067347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2715959680610215776827221 15913826253575483067347)
            ·
              rfl

theorem cell19_470692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 9].length) (baseStart_470692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470692 prefixEnd_470692 := by exact prefixLift 470692
  have htrace : WordTrace (prefixWord ++ tailWord_470692) baseStart_470692 baseEnd_470692 := by
    simpa [prefixWord, tailWord_470692, baseEnd_470692] using wordTrace_append hprefix tailTrace_470692
  have hstable : (prefixWord ++ tailWord_470692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470692).length < 2 ^ (prefixWord ++ tailWord_470692).sum := by decide
  have hdescent : baseEnd_470692 < baseStart_470692 := by decide
  rcases family_descends (prefixWord ++ tailWord_470692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470728 : List Nat := [2, 1, 3, 1, 2, 2, 5, 3]
def baseStart_470728 : Nat := 118140960795 + 470728 * 2 ^ 59
def prefixEnd_470728 : Nat := 4983230072969 + 3 ^ 40 * 470728 * 2
def baseEnd_470728 : Nat := 143235390536141930806025

theorem tailTrace_470728 : CollatzResearch.WordTrace tailWord_470728 prefixEnd_470728 143235390536141930806025 := by
  unfold tailWord_470728
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584430319320162393510419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11445907092426883191347225 8584430319320162393510419)
  ·
    refine ⟨12876645478980243590265629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8584430319320162393510419 12876645478980243590265629)
    ·
      refine ⟨4828742054617591346349611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12876645478980243590265629 4828742054617591346349611)
      ·
        refine ⟨7243113081926387019524417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4828742054617591346349611 7243113081926387019524417)
        ·
          refine ⟨5432334811444790264643313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7243113081926387019524417 5432334811444790264643313)
          ·
            refine ⟨4074251108583592698482485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5432334811444790264643313 4074251108583592698482485)
            ·
              refine ⟨381961041429711815482733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4074251108583592698482485 381961041429711815482733)
              ·
                refine ⟨143235390536141930806025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381961041429711815482733 143235390536141930806025)
                ·
                  rfl

theorem cell19_470728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_470728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470728 prefixEnd_470728 := by exact prefixLift 470728
  have htrace : WordTrace (prefixWord ++ tailWord_470728) baseStart_470728 baseEnd_470728 := by
    simpa [prefixWord, tailWord_470728, baseEnd_470728] using wordTrace_append hprefix tailTrace_470728
  have hstable : (prefixWord ++ tailWord_470728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470728).length < 2 ^ (prefixWord ++ tailWord_470728).sum := by decide
  have hdescent : baseEnd_470728 < baseStart_470728 := by decide
  rcases family_descends (prefixWord ++ tailWord_470728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470785 : List Nat := [1, 2, 4, 1, 1, 1, 6, 3]
def baseStart_470785 : Nat := 118140960795 + 470785 * 2 ^ 59
def prefixEnd_470785 : Nat := 4983230072969 + 3 ^ 40 * 470785 * 2
def baseEnd_470785 : Nat := 143252734771582687539203

theorem tailTrace_470785 : CollatzResearch.WordTrace tailWord_470785 prefixEnd_470785 143252734771582687539203 := by
  unfold tailWord_470785
  simp only [CollatzResearch.WordTrace]
  refine ⟨17170939599433823521845809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11447293066289215681230539 17170939599433823521845809)
  ·
    refine ⟨12878204699575367641384357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17170939599433823521845809 12878204699575367641384357)
    ·
      refine ⟨2414663381170381432759567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12878204699575367641384357 2414663381170381432759567)
      ·
        refine ⟨3621995071755572149139351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414663381170381432759567 3621995071755572149139351)
        ·
          refine ⟨5432992607633358223709027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621995071755572149139351 5432992607633358223709027)
          ·
            refine ⟨8149488911450037335563541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432992607633358223709027 8149488911450037335563541)
            ·
              refine ⟨382007292724220500104541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8149488911450037335563541 382007292724220500104541)
              ·
                refine ⟨143252734771582687539203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382007292724220500104541 143252734771582687539203)
                ·
                  rfl

theorem cell19_470785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_470785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470785 prefixEnd_470785 := by exact prefixLift 470785
  have htrace : WordTrace (prefixWord ++ tailWord_470785) baseStart_470785 baseEnd_470785 := by
    simpa [prefixWord, tailWord_470785, baseEnd_470785] using wordTrace_append hprefix tailTrace_470785
  have hstable : (prefixWord ++ tailWord_470785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470785).length < 2 ^ (prefixWord ++ tailWord_470785).sum := by decide
  have hdescent : baseEnd_470785 < baseStart_470785 := by decide
  rcases family_descends (prefixWord ++ tailWord_470785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470802 : List Nat := [3, 2, 4, 1, 1, 3, 5]
def baseStart_470802 : Nat := 118140960795 + 470802 * 2 ^ 59
def prefixEnd_470802 : Nat := 4983230072969 + 3 ^ 40 * 470802 * 2
def baseEnd_470802 : Nat := 47752635871243895053793

theorem tailTrace_470802 : CollatzResearch.WordTrace tailWord_470802 prefixEnd_470802 47752635871243895053793 := by
  unfold tailWord_470802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292889910093058856303665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11447706426914823616809773 4292889910093058856303665)
  ·
    refine ⟨3219667432569794142227749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4292889910093058856303665 3219667432569794142227749)
    ·
      refine ⟨603687643606836401667703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3219667432569794142227749 603687643606836401667703)
      ·
        refine ⟨905531465410254602501555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603687643606836401667703 905531465410254602501555)
        ·
          refine ⟨1358297198115381903752333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905531465410254602501555 1358297198115381903752333)
          ·
            refine ⟨509361449293268213907125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1358297198115381903752333 509361449293268213907125)
            ·
              refine ⟨47752635871243895053793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509361449293268213907125 47752635871243895053793)
              ·
                rfl

theorem cell19_470802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_470802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470802 prefixEnd_470802 := by exact prefixLift 470802
  have htrace : WordTrace (prefixWord ++ tailWord_470802) baseStart_470802 baseEnd_470802 := by
    simpa [prefixWord, tailWord_470802, baseEnd_470802] using wordTrace_append hprefix tailTrace_470802
  have hstable : (prefixWord ++ tailWord_470802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470802).length < 2 ^ (prefixWord ++ tailWord_470802).sum := by decide
  have hdescent : baseEnd_470802 < baseStart_470802 := by decide
  rcases family_descends (prefixWord ++ tailWord_470802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470844 : List Nat := [2, 2, 2, 2, 1, 1, 4, 5]
def baseStart_470844 : Nat := 118140960795 + 470844 * 2 ^ 59
def prefixEnd_470844 : Nat := 4983230072969 + 3 ^ 40 * 470844 * 2
def baseEnd_470844 : Nat := 143270687576688032227931

theorem tailTrace_470844 : CollatzResearch.WordTrace tailWord_470844 prefixEnd_470844 143270687576688032227931 := by
  unfold tailWord_470844
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586545753110038299121793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11448727670813384398829057 8586545753110038299121793)
  ·
    refine ⟨6439909314832528724341345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8586545753110038299121793 6439909314832528724341345)
    ·
      refine ⟨4829931986124396543256009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6439909314832528724341345 4829931986124396543256009)
      ·
        refine ⟨3622448989593297407442007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4829931986124396543256009 3622448989593297407442007)
        ·
          refine ⟨5433673484389946111163011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622448989593297407442007 5433673484389946111163011)
          ·
            refine ⟨8150510226584919166744517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433673484389946111163011 8150510226584919166744517)
            ·
              refine ⟨1528220667484672343764597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8150510226584919166744517 1528220667484672343764597)
              ·
                refine ⟨143270687576688032227931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1528220667484672343764597 143270687576688032227931)
                ·
                  rfl

theorem cell19_470844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_470844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470844 prefixEnd_470844 := by exact prefixLift 470844
  have htrace : WordTrace (prefixWord ++ tailWord_470844) baseStart_470844 baseEnd_470844 := by
    simpa [prefixWord, tailWord_470844, baseEnd_470844] using wordTrace_append hprefix tailTrace_470844
  have hstable : (prefixWord ++ tailWord_470844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470844).length < 2 ^ (prefixWord ++ tailWord_470844).sum := by decide
  have hdescent : baseEnd_470844 < baseStart_470844 := by decide
  rcases family_descends (prefixWord ++ tailWord_470844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470861 : List Nat := [1, 6, 1, 2, 1, 8]
def baseStart_470861 : Nat := 118140960795 + 470861 * 2 ^ 59
def prefixEnd_470861 : Nat := 4983230072969 + 3 ^ 40 * 470861 * 2
def baseEnd_470861 : Nat := 15919540046537447761123

theorem tailTrace_470861 : CollatzResearch.WordTrace tailWord_470861 prefixEnd_470861 15919540046537447761123 := by
  unfold tailWord_470861
  simp only [CollatzResearch.WordTrace]
  refine ⟨17173711547158488501612437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11449141031438992334408291 17173711547158488501612437)
  ·
    refine ⟨805017728773054148513083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17173711547158488501612437 805017728773054148513083)
    ·
      refine ⟨1207526593159581222769625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805017728773054148513083 1207526593159581222769625)
      ·
        refine ⟨905644944869685917077219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1207526593159581222769625 905644944869685917077219)
        ·
          refine ⟨1358467417304528875615829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905644944869685917077219 1358467417304528875615829)
          ·
            refine ⟨15919540046537447761123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1358467417304528875615829 15919540046537447761123)
            ·
              rfl

theorem cell19_470861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 8].length) (baseStart_470861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470861 prefixEnd_470861 := by exact prefixLift 470861
  have htrace : WordTrace (prefixWord ++ tailWord_470861) baseStart_470861 baseEnd_470861 := by
    simpa [prefixWord, tailWord_470861, baseEnd_470861] using wordTrace_append hprefix tailTrace_470861
  have hstable : (prefixWord ++ tailWord_470861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470861).length < 2 ^ (prefixWord ++ tailWord_470861).sum := by decide
  have hdescent : baseEnd_470861 < baseStart_470861 := by decide
  rcases family_descends (prefixWord ++ tailWord_470861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470876 : List Nat := [2, 2, 4, 2, 3, 1, 1, 4]
def baseStart_470876 : Nat := 118140960795 + 470876 * 2 ^ 59
def prefixEnd_470876 : Nat := 4983230072969 + 3 ^ 40 * 470876 * 2
def baseEnd_470876 : Nat := 143280424691321439516733

theorem tailTrace_470876 : CollatzResearch.WordTrace tailWord_470876 prefixEnd_470876 143280424691321439516733 := by
  unfold tailWord_470876
  simp only [CollatzResearch.WordTrace]
  refine ⟨8587129321052073031704241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11449505761402764042272321 8587129321052073031704241)
  ·
    refine ⟨6440346990789054773778181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8587129321052073031704241 6440346990789054773778181)
    ·
      refine ⟨1207565060772947770083409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6440346990789054773778181 1207565060772947770083409)
      ·
        refine ⟨905673795579710827562557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1207565060772947770083409 905673795579710827562557)
        ·
          refine ⟨339627673342391560335959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 905673795579710827562557 339627673342391560335959)
          ·
            refine ⟨509441510013587340503939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339627673342391560335959 509441510013587340503939)
            ·
              refine ⟨764162265020381010755909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509441510013587340503939 764162265020381010755909)
              ·
                refine ⟨143280424691321439516733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 764162265020381010755909 143280424691321439516733)
                ·
                  rfl

theorem cell19_470876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_470876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470876 prefixEnd_470876 := by exact prefixLift 470876
  have htrace : WordTrace (prefixWord ++ tailWord_470876) baseStart_470876 baseEnd_470876 := by
    simpa [prefixWord, tailWord_470876, baseEnd_470876] using wordTrace_append hprefix tailTrace_470876
  have hstable : (prefixWord ++ tailWord_470876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470876).length < 2 ^ (prefixWord ++ tailWord_470876).sum := by decide
  have hdescent : baseEnd_470876 < baseStart_470876 := by decide
  rcases family_descends (prefixWord ++ tailWord_470876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_470880 : List Nat := [2, 1, 1, 3, 3, 4, 1, 4]
def baseStart_470880 : Nat := 118140960795 + 470880 * 2 ^ 59
def prefixEnd_470880 : Nat := 4983230072969 + 3 ^ 40 * 470880 * 2
def baseEnd_470880 : Nat := 143281641830650615427833

theorem tailTrace_470880 : CollatzResearch.WordTrace tailWord_470880 prefixEnd_470880 143281641830650615427833 := by
  unfold tailWord_470880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8587202267044827373277047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11449603022726436497702729 8587202267044827373277047)
  ·
    refine ⟨12880803400567241059915571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8587202267044827373277047 12880803400567241059915571)
    ·
      refine ⟨19321205100850861589873357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12880803400567241059915571 19321205100850861589873357)
      ·
        refine ⟨7245451912819073096202509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19321205100850861589873357 7245451912819073096202509)
        ·
          refine ⟨2717044467307152411075941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7245451912819073096202509 2717044467307152411075941)
          ·
            refine ⟨509445837620091077076739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2717044467307152411075941 509445837620091077076739)
            ·
              refine ⟨764168756430136615615109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509445837620091077076739 764168756430136615615109)
              ·
                refine ⟨143281641830650615427833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 764168756430136615615109 143281641830650615427833)
                ·
                  rfl

theorem cell19_470880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_470880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_470880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_470880 prefixEnd_470880 := by exact prefixLift 470880
  have htrace : WordTrace (prefixWord ++ tailWord_470880) baseStart_470880 baseEnd_470880 := by
    simpa [prefixWord, tailWord_470880, baseEnd_470880] using wordTrace_append hprefix tailTrace_470880
  have hstable : (prefixWord ++ tailWord_470880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_470880).length < 2 ^ (prefixWord ++ tailWord_470880).sum := by decide
  have hdescent : baseEnd_470880 < baseStart_470880 := by decide
  rcases family_descends (prefixWord ++ tailWord_470880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471146 : List Nat := [3, 1, 3, 2, 3, 2, 5]
def baseStart_471146 : Nat := 118140960795 + 471146 * 2 ^ 59
def prefixEnd_471146 : Nat := 4983230072969 + 3 ^ 40 * 471146 * 2
def baseEnd_471146 : Nat := 47787527198680271171999

theorem tailTrace_471146 : CollatzResearch.WordTrace tailWord_471146 prefixEnd_471146 47787527198680271171999 := by
  unfold tailWord_471146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296026587781495543934323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11456070900750654783824861 4296026587781495543934323)
  ·
    refine ⟨6444039881672243315901485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4296026587781495543934323 6444039881672243315901485)
    ·
      refine ⟨2416514955627091243463057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6444039881672243315901485 2416514955627091243463057)
      ·
        refine ⟨1812386216720318432597293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2416514955627091243463057 1812386216720318432597293)
        ·
          refine ⟨679644831270119412223985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1812386216720318432597293 679644831270119412223985)
          ·
            refine ⟨509733623452589559167989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679644831270119412223985 509733623452589559167989)
            ·
              refine ⟨47787527198680271171999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509733623452589559167989 47787527198680271171999)
              ·
                rfl

theorem cell19_471146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_471146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471146 prefixEnd_471146 := by exact prefixLift 471146
  have htrace : WordTrace (prefixWord ++ tailWord_471146) baseStart_471146 baseEnd_471146 := by
    simpa [prefixWord, tailWord_471146, baseEnd_471146] using wordTrace_append hprefix tailTrace_471146
  have hstable : (prefixWord ++ tailWord_471146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471146).length < 2 ^ (prefixWord ++ tailWord_471146).sum := by decide
  have hdescent : baseEnd_471146 < baseStart_471146 := by decide
  rcases family_descends (prefixWord ++ tailWord_471146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471148 : List Nat := [2, 2, 1, 1, 3, 5, 5]
def baseStart_471148 : Nat := 118140960795 + 471148 * 2 ^ 59
def prefixEnd_471148 : Nat := 4983230072969 + 3 ^ 40 * 471148 * 2
def baseEnd_471148 : Nat := 47787730055235133823849

theorem tailTrace_471148 : CollatzResearch.WordTrace tailWord_471148 prefixEnd_471148 47787730055235133823849 := by
  unfold tailWord_471148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8592089648559368258655049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11456119531412491011540065 8592089648559368258655049)
  ·
    refine ⟨6444067236419526193991287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8592089648559368258655049 6444067236419526193991287)
    ·
      refine ⟨9666100854629289290986931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6444067236419526193991287 9666100854629289290986931)
      ·
        refine ⟨14499151281943933936480397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9666100854629289290986931 14499151281943933936480397)
        ·
          refine ⟨5437181730728975226180149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14499151281943933936480397 5437181730728975226180149)
          ·
            refine ⟨509735787255841427454389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5437181730728975226180149 509735787255841427454389)
            ·
              refine ⟨47787730055235133823849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509735787255841427454389 47787730055235133823849)
              ·
                rfl

theorem cell19_471148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_471148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471148 prefixEnd_471148 := by exact prefixLift 471148
  have htrace : WordTrace (prefixWord ++ tailWord_471148) baseStart_471148 baseEnd_471148 := by
    simpa [prefixWord, tailWord_471148, baseEnd_471148] using wordTrace_append hprefix tailTrace_471148
  have hstable : (prefixWord ++ tailWord_471148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471148).length < 2 ^ (prefixWord ++ tailWord_471148).sum := by decide
  have hdescent : baseEnd_471148 < baseStart_471148 := by decide
  rcases family_descends (prefixWord ++ tailWord_471148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471186 : List Nat := [3, 2, 3, 1, 1, 1, 1, 7]
def baseStart_471186 : Nat := 118140960795 + 471186 * 2 ^ 59
def prefixEnd_471186 : Nat := 4983230072969 + 3 ^ 40 * 471186 * 2
def baseEnd_471186 : Nat := 143374752989332572626999

theorem tailTrace_471186 : CollatzResearch.WordTrace tailWord_471186 prefixEnd_471186 143374752989332572626999 := by
  unfold tailWord_471186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296391317745267251798353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11457043513987379338128941 4296391317745267251798353)
  ·
    refine ⟨3222293488308950438848765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4296391317745267251798353 3222293488308950438848765)
    ·
      refine ⟨1208360058115856414568287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3222293488308950438848765 1208360058115856414568287)
      ·
        refine ⟨1812540087173784621852431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208360058115856414568287 1812540087173784621852431)
        ·
          refine ⟨2718810130760676932778647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812540087173784621852431 2718810130760676932778647)
          ·
            refine ⟨4078215196141015399167971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718810130760676932778647 4078215196141015399167971)
            ·
              refine ⟨6117322794211523098751957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078215196141015399167971 6117322794211523098751957)
              ·
                refine ⟨143374752989332572626999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6117322794211523098751957 143374752989332572626999)
                ·
                  rfl

theorem cell19_471186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_471186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471186 prefixEnd_471186 := by exact prefixLift 471186
  have htrace : WordTrace (prefixWord ++ tailWord_471186) baseStart_471186 baseEnd_471186 := by
    simpa [prefixWord, tailWord_471186, baseEnd_471186] using wordTrace_append hprefix tailTrace_471186
  have hstable : (prefixWord ++ tailWord_471186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471186).length < 2 ^ (prefixWord ++ tailWord_471186).sum := by decide
  have hdescent : baseEnd_471186 < baseStart_471186 := by decide
  rcases family_descends (prefixWord ++ tailWord_471186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471243 : List Nat := [1, 1, 1, 1, 3, 2, 7, 3]
def baseStart_471243 : Nat := 118140960795 + 471243 * 2 ^ 59
def prefixEnd_471243 : Nat := 4983230072969 + 3 ^ 40 * 471243 * 2
def baseEnd_471243 : Nat := 143392097224773329360177

theorem tailTrace_471243 : CollatzResearch.WordTrace tailWord_471243 prefixEnd_471243 143392097224773329360177 := by
  unfold tailWord_471243
  simp only [CollatzResearch.WordTrace]
  refine ⟨17187644231774567742018383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11458429487849711828012255 17187644231774567742018383)
  ·
    refine ⟨25781466347661851613027575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17187644231774567742018383 25781466347661851613027575)
    ·
      refine ⟨38672199521492777419541363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25781466347661851613027575 38672199521492777419541363)
      ·
        refine ⟨58008299282239166129312045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38672199521492777419541363 58008299282239166129312045)
        ·
          refine ⟨21753112230839687298492017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58008299282239166129312045 21753112230839687298492017)
          ·
            refine ⟨16314834173129765473869013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21753112230839687298492017 16314834173129765473869013)
            ·
              refine ⟨382378925932728878293805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16314834173129765473869013 382378925932728878293805)
              ·
                refine ⟨143392097224773329360177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382378925932728878293805 143392097224773329360177)
                ·
                  rfl

theorem cell19_471243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_471243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471243 prefixEnd_471243 := by exact prefixLift 471243
  have htrace : WordTrace (prefixWord ++ tailWord_471243) baseStart_471243 baseEnd_471243 := by
    simpa [prefixWord, tailWord_471243, baseEnd_471243] using wordTrace_append hprefix tailTrace_471243
  have hstable : (prefixWord ++ tailWord_471243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471243).length < 2 ^ (prefixWord ++ tailWord_471243).sum := by decide
  have hdescent : baseEnd_471243 < baseStart_471243 := by decide
  rcases family_descends (prefixWord ++ tailWord_471243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471264 : List Nat := [2, 1, 1, 3, 1, 3, 8]
def baseStart_471264 : Nat := 118140960795 + 471264 * 2 ^ 59
def prefixEnd_471264 : Nat := 4983230072969 + 3 ^ 40 * 471264 * 2
def baseEnd_471264 : Nat := 47799495735417167631151

theorem tailTrace_471264 : CollatzResearch.WordTrace tailWord_471264 prefixEnd_471264 47799495735417167631151 := by
  unfold tailWord_471264
  simp only [CollatzResearch.WordTrace]
  refine ⟨8594205082349244164266423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11458940109798992219021897 8594205082349244164266423)
  ·
    refine ⟨12891307623523866246399635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8594205082349244164266423 12891307623523866246399635)
    ·
      refine ⟨19336961435285799369599453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12891307623523866246399635 19336961435285799369599453)
      ·
        refine ⟨7251360538232174763599795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19336961435285799369599453 7251360538232174763599795)
        ·
          refine ⟨10877040807348262145399693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7251360538232174763599795 10877040807348262145399693)
          ·
            refine ⟨4078890302755598304524885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10877040807348262145399693 4078890302755598304524885)
            ·
              refine ⟨47799495735417167631151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4078890302755598304524885 47799495735417167631151)
              ·
                rfl

theorem cell19_471264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_471264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471264 prefixEnd_471264 := by exact prefixLift 471264
  have htrace : WordTrace (prefixWord ++ tailWord_471264) baseStart_471264 baseEnd_471264 := by
    simpa [prefixWord, tailWord_471264, baseEnd_471264] using wordTrace_append hprefix tailTrace_471264
  have hstable : (prefixWord ++ tailWord_471264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471264).length < 2 ^ (prefixWord ++ tailWord_471264).sum := by decide
  have hdescent : baseEnd_471264 < baseStart_471264 := by decide
  rcases family_descends (prefixWord ++ tailWord_471264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471283 : List Nat := [1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_471283 : Nat := 118140960795 + 471283 * 2 ^ 59
def prefixEnd_471283 : Nat := 4983230072969 + 3 ^ 40 * 471283 * 2
def baseEnd_471283 : Nat := 143404268618065088471179

theorem tailTrace_471283 : CollatzResearch.WordTrace tailWord_471283 prefixEnd_471283 143404268618065088471179 := by
  unfold tailWord_471283
  simp only [CollatzResearch.WordTrace]
  refine ⟨17189103151629654573474503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11459402101086436382316335 17189103151629654573474503)
  ·
    refine ⟨25783654727444481860211755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17189103151629654573474503 25783654727444481860211755)
    ·
      refine ⟨38675482091166722790317633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25783654727444481860211755 38675482091166722790317633)
      ·
        refine ⟨29006611568375042092738225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38675482091166722790317633 29006611568375042092738225)
        ·
          refine ⟨21754958676281281569553669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29006611568375042092738225 21754958676281281569553669)
          ·
            refine ⟨4079054751802740294291313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21754958676281281569553669 4079054751802740294291313)
            ·
              refine ⟨3059291063852055220718485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4079054751802740294291313 3059291063852055220718485)
              ·
                refine ⟨143404268618065088471179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3059291063852055220718485 143404268618065088471179)
                ·
                  rfl

theorem cell19_471283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_471283 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471283 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471283 prefixEnd_471283 := by exact prefixLift 471283
  have htrace : WordTrace (prefixWord ++ tailWord_471283) baseStart_471283 baseEnd_471283 := by
    simpa [prefixWord, tailWord_471283, baseEnd_471283] using wordTrace_append hprefix tailTrace_471283
  have hstable : (prefixWord ++ tailWord_471283).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471283).length < 2 ^ (prefixWord ++ tailWord_471283).sum := by decide
  have hdescent : baseEnd_471283 < baseStart_471283 := by decide
  rcases family_descends (prefixWord ++ tailWord_471283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471298 : List Nat := [3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_471298 : Nat := 118140960795 + 471298 * 2 ^ 59
def prefixEnd_471298 : Nat := 4983230072969 + 3 ^ 40 * 471298 * 2
def baseEnd_471298 : Nat := 143408832890549498137805

theorem tailTrace_471298 : CollatzResearch.WordTrace tailWord_471298 prefixEnd_471298 143408832890549498137805 := by
  unfold tailWord_471298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4297412561643828033817637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11459766831050208090180365 4297412561643828033817637)
  ·
    refine ⟨805764855308217756340807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4297412561643828033817637 805764855308217756340807)
    ·
      refine ⟨1208647282962326634511211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805764855308217756340807 1208647282962326634511211)
      ·
        refine ⟨1812970924443489951766817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208647282962326634511211 1812970924443489951766817)
        ·
          refine ⟨1359728193332617463825113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812970924443489951766817 1359728193332617463825113)
          ·
            refine ⟨1019796144999463097868835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1359728193332617463825113 1019796144999463097868835)
            ·
              refine ⟨1529694217499194646803253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019796144999463097868835 1529694217499194646803253)
              ·
                refine ⟨143408832890549498137805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1529694217499194646803253 143408832890549498137805)
                ·
                  rfl

theorem cell19_471298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_471298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471298 prefixEnd_471298 := by exact prefixLift 471298
  have htrace : WordTrace (prefixWord ++ tailWord_471298) baseStart_471298 baseEnd_471298 := by
    simpa [prefixWord, tailWord_471298, baseEnd_471298] using wordTrace_append hprefix tailTrace_471298
  have hstable : (prefixWord ++ tailWord_471298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471298).length < 2 ^ (prefixWord ++ tailWord_471298).sum := by decide
  have hdescent : baseEnd_471298 < baseStart_471298 := by decide
  rcases family_descends (prefixWord ++ tailWord_471298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471319 : List Nat := [1, 1, 3, 4, 1, 4, 5]
def baseStart_471319 : Nat := 118140960795 + 471319 * 2 ^ 59
def prefixEnd_471319 : Nat := 4983230072969 + 3 ^ 40 * 471319 * 2
def baseEnd_471319 : Nat := 47805074290675890557027

theorem tailTrace_471319 : CollatzResearch.WordTrace tailWord_471319 prefixEnd_471319 47805074290675890557027 := by
  unfold tailWord_471319
  simp only [CollatzResearch.WordTrace]
  refine ⟨17190416179499232721785011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11460277452999488481190007 17190416179499232721785011)
  ·
    refine ⟨25785624269248849082677517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17190416179499232721785011 25785624269248849082677517)
    ·
      refine ⟨9669609100968318406004069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25785624269248849082677517 9669609100968318406004069)
      ·
        refine ⟨1813051706431559701125763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9669609100968318406004069 1813051706431559701125763)
        ·
          refine ⟨2719577559647339551688645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813051706431559701125763 2719577559647339551688645)
          ·
            refine ⟨509920792433876165941621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2719577559647339551688645 509920792433876165941621)
            ·
              refine ⟨47805074290675890557027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509920792433876165941621 47805074290675890557027)
              ·
                rfl

theorem cell19_471319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_471319 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471319 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471319 prefixEnd_471319 := by exact prefixLift 471319
  have htrace : WordTrace (prefixWord ++ tailWord_471319) baseStart_471319 baseEnd_471319 := by
    simpa [prefixWord, tailWord_471319, baseEnd_471319] using wordTrace_append hprefix tailTrace_471319
  have hstable : (prefixWord ++ tailWord_471319).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471319).length < 2 ^ (prefixWord ++ tailWord_471319).sum := by decide
  have hdescent : baseEnd_471319 < baseStart_471319 := by decide
  rcases family_descends (prefixWord ++ tailWord_471319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471336 : List Nat := [2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_471336 : Nat := 118140960795 + 471336 * 2 ^ 59
def prefixEnd_471336 : Nat := 4983230072969 + 3 ^ 40 * 471336 * 2
def baseEnd_471336 : Nat := 143420395714176669293257

theorem tailTrace_471336 : CollatzResearch.WordTrace tailWord_471336 prefixEnd_471336 143420395714176669293257 := by
  unfold tailWord_471336
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595518110218822312576931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11460690813625096416769241 8595518110218822312576931)
  ·
    refine ⟨12893277165328233468865397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8595518110218822312576931 12893277165328233468865397)
    ·
      refine ⟨1208744734249521887706131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12893277165328233468865397 1208744734249521887706131)
      ·
        refine ⟨1813117101374282831559197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1208744734249521887706131 1813117101374282831559197)
        ·
          refine ⟨679918913015356061834699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1813117101374282831559197 679918913015356061834699)
          ·
            refine ⟨1019878369523034092752049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679918913015356061834699 1019878369523034092752049)
            ·
              refine ⟨764908777142275569564037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019878369523034092752049 764908777142275569564037)
              ·
                refine ⟨143420395714176669293257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 764908777142275569564037 143420395714176669293257)
                ·
                  rfl

theorem cell19_471336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_471336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471336 prefixEnd_471336 := by exact prefixLift 471336
  have htrace : WordTrace (prefixWord ++ tailWord_471336) baseStart_471336 baseEnd_471336 := by
    simpa [prefixWord, tailWord_471336, baseEnd_471336] using wordTrace_append hprefix tailTrace_471336
  have hstable : (prefixWord ++ tailWord_471336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471336).length < 2 ^ (prefixWord ++ tailWord_471336).sum := by decide
  have hdescent : baseEnd_471336 < baseStart_471336 := by decide
  rcases family_descends (prefixWord ++ tailWord_471336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471340 : List Nat := [2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_471340 : Nat := 118140960795 + 471340 * 2 ^ 59
def prefixEnd_471340 : Nat := 4983230072969 + 3 ^ 40 * 471340 * 2
def baseEnd_471340 : Nat := 143421612853505845204357

theorem tailTrace_471340 : CollatzResearch.WordTrace tailWord_471340 prefixEnd_471340 143421612853505845204357 := by
  unfold tailWord_471340
  simp only [CollatzResearch.WordTrace]
  refine ⟨8595591056211576654149737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11460788074948768872199649 8595591056211576654149737)
  ·
    refine ⟨6446693292158682490612303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8595591056211576654149737 6446693292158682490612303)
    ·
      refine ⟨9670039938238023735918455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6446693292158682490612303 9670039938238023735918455)
      ·
        refine ⟨14505059907357035603877683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9670039938238023735918455 14505059907357035603877683)
        ·
          refine ⟨21757589861035553405816525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14505059907357035603877683 21757589861035553405816525)
          ·
            refine ⟨8159096197888332527181197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21757589861035553405816525 8159096197888332527181197)
            ·
              refine ⟨3059661074208124697692949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8159096197888332527181197 3059661074208124697692949)
              ·
                refine ⟨143421612853505845204357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3059661074208124697692949 143421612853505845204357)
                ·
                  rfl

theorem cell19_471340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_471340 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471340 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471340 prefixEnd_471340 := by exact prefixLift 471340
  have htrace : WordTrace (prefixWord ++ tailWord_471340) baseStart_471340 baseEnd_471340 := by
    simpa [prefixWord, tailWord_471340, baseEnd_471340] using wordTrace_append hprefix tailTrace_471340
  have hstable : (prefixWord ++ tailWord_471340).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471340).length < 2 ^ (prefixWord ++ tailWord_471340).sum := by decide
  have hdescent : baseEnd_471340 < baseStart_471340 := by decide
  rcases family_descends (prefixWord ++ tailWord_471340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471359 : List Nat := [1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_471359 : Nat := 118140960795 + 471359 * 2 ^ 59
def prefixEnd_471359 : Nat := 4983230072969 + 3 ^ 40 * 471359 * 2
def baseEnd_471359 : Nat := 143427394265319430782083

theorem tailTrace_471359 : CollatzResearch.WordTrace tailWord_471359 prefixEnd_471359 143427394265319430782083 := by
  unfold tailWord_471359
  simp only [CollatzResearch.WordTrace]
  refine ⟨17191875099354319553241131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11461250066236213035494087 17191875099354319553241131)
  ·
    refine ⟨25787812649031479329861697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17191875099354319553241131 25787812649031479329861697)
    ·
      refine ⟨19340859486773609497396273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25787812649031479329861697 19340859486773609497396273)
      ·
        refine ⟨14505644615080207123047205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19340859486773609497396273 14505644615080207123047205)
        ·
          refine ⟨2719808365327538835571351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14505644615080207123047205 2719808365327538835571351)
          ·
            refine ⟨4079712547991308253357027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719808365327538835571351 4079712547991308253357027)
            ·
              refine ⟨6119568821986962380035541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4079712547991308253357027 6119568821986962380035541)
              ·
                refine ⟨143427394265319430782083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6119568821986962380035541 143427394265319430782083)
                ·
                  rfl

theorem cell19_471359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_471359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471359 prefixEnd_471359 := by exact prefixLift 471359
  have htrace : WordTrace (prefixWord ++ tailWord_471359) baseStart_471359 baseEnd_471359 := by
    simpa [prefixWord, tailWord_471359, baseEnd_471359] using wordTrace_append hprefix tailTrace_471359
  have hstable : (prefixWord ++ tailWord_471359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471359).length < 2 ^ (prefixWord ++ tailWord_471359).sum := by decide
  have hdescent : baseEnd_471359 < baseStart_471359 := by decide
  rcases family_descends (prefixWord ++ tailWord_471359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471435 : List Nat := [1, 1, 1, 1, 4, 5, 6]
def baseStart_471435 : Nat := 118140960795 + 471435 * 2 ^ 59
def prefixEnd_471435 : Nat := 4983230072969 + 3 ^ 40 * 471435 * 2
def baseEnd_471435 : Nat := 47816839970857924364329

theorem tailTrace_471435 : CollatzResearch.WordTrace tailWord_471435 prefixEnd_471435 47816839970857924364329 := by
  unfold tailWord_471435
  simp only [CollatzResearch.WordTrace]
  refine ⟨17194647047078984533007759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11463098031385989688671839 17194647047078984533007759)
  ·
    refine ⟨25791970570618476799511639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17194647047078984533007759 25791970570618476799511639)
    ·
      refine ⟨38687955855927715199267459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25791970570618476799511639 38687955855927715199267459)
      ·
        refine ⟨58031933783891572798901189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38687955855927715199267459 58031933783891572798901189)
        ·
          refine ⟨10880987584479669899793973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58031933783891572798901189 10880987584479669899793973)
          ·
            refine ⟨1020092586044969053105685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10880987584479669899793973 1020092586044969053105685)
            ·
              refine ⟨47816839970857924364329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1020092586044969053105685 47816839970857924364329)
              ·
                rfl

theorem cell19_471435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_471435 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471435 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471435 prefixEnd_471435 := by exact prefixLift 471435
  have htrace : WordTrace (prefixWord ++ tailWord_471435) baseStart_471435 baseEnd_471435 := by
    simpa [prefixWord, tailWord_471435, baseEnd_471435] using wordTrace_append hprefix tailTrace_471435
  have hstable : (prefixWord ++ tailWord_471435).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471435).length < 2 ^ (prefixWord ++ tailWord_471435).sum := by decide
  have hdescent : baseEnd_471435 < baseStart_471435 := by decide
  rcases family_descends (prefixWord ++ tailWord_471435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471469 : List Nat := [1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_471469 : Nat := 118140960795 + 471469 * 2 ^ 59
def prefixEnd_471469 : Nat := 4983230072969 + 3 ^ 40 * 471469 * 2
def baseEnd_471469 : Nat := 143460865596871768337339

theorem tailTrace_471469 : CollatzResearch.WordTrace tailWord_471469 prefixEnd_471469 143460865596871768337339 := by
  unfold tailWord_471469
  simp only [CollatzResearch.WordTrace]
  refine ⟨17195887128955808339745461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11463924752637205559830307 17195887128955808339745461)
  ·
    refine ⟨1612114418339607031851137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17195887128955808339745461 1612114418339607031851137)
    ·
      refine ⟨1209085813754705273888353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1612114418339607031851137 1209085813754705273888353)
      ·
        refine ⟨906814360316028955416265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1209085813754705273888353 906814360316028955416265)
        ·
          refine ⟨680110770237021716562199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906814360316028955416265 680110770237021716562199)
          ·
            refine ⟨1020166155355532574843299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680110770237021716562199 1020166155355532574843299)
            ·
              refine ⟨1530249233033298862264949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020166155355532574843299 1530249233033298862264949)
              ·
                refine ⟨143460865596871768337339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1530249233033298862264949 143460865596871768337339)
                ·
                  rfl

theorem cell19_471469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_471469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471469 prefixEnd_471469 := by exact prefixLift 471469
  have htrace : WordTrace (prefixWord ++ tailWord_471469) baseStart_471469 baseEnd_471469 := by
    simpa [prefixWord, tailWord_471469, baseEnd_471469] using wordTrace_append hprefix tailTrace_471469
  have hstable : (prefixWord ++ tailWord_471469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471469).length < 2 ^ (prefixWord ++ tailWord_471469).sum := by decide
  have hdescent : baseEnd_471469 < baseStart_471469 := by decide
  rcases family_descends (prefixWord ++ tailWord_471469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471509 : List Nat := [1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_471509 : Nat := 118140960795 + 471509 * 2 ^ 59
def prefixEnd_471509 : Nat := 4983230072969 + 3 ^ 40 * 471509 * 2
def baseEnd_471509 : Nat := 143473036990163527448341

theorem tailTrace_471509 : CollatzResearch.WordTrace tailWord_471509 prefixEnd_471509 143473036990163527448341 := by
  unfold tailWord_471509
  simp only [CollatzResearch.WordTrace]
  refine ⟨17197346048810895171201581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11464897365873930114134387 17197346048810895171201581)
  ·
    refine ⟨6449004768304085689200593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17197346048810895171201581 6449004768304085689200593)
    ·
      refine ⟨4836753576228064266900445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6449004768304085689200593 4836753576228064266900445)
      ·
        refine ⟨1813782591085524100087667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4836753576228064266900445 1813782591085524100087667)
        ·
          refine ⟨2720673886628286150131501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813782591085524100087667 2720673886628286150131501)
          ·
            refine ⟨1020252707485607306299313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2720673886628286150131501 1020252707485607306299313)
            ·
              refine ⟨765189530614205479724485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020252707485607306299313 765189530614205479724485)
              ·
                refine ⟨143473036990163527448341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765189530614205479724485 143473036990163527448341)
                ·
                  rfl

theorem cell19_471509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_471509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471509 prefixEnd_471509 := by exact prefixLift 471509
  have htrace : WordTrace (prefixWord ++ tailWord_471509) baseStart_471509 baseEnd_471509 := by
    simpa [prefixWord, tailWord_471509, baseEnd_471509] using wordTrace_append hprefix tailTrace_471509
  have hstable : (prefixWord ++ tailWord_471509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471509).length < 2 ^ (prefixWord ++ tailWord_471509).sum := by decide
  have hdescent : baseEnd_471509 < baseStart_471509 := by decide
  rcases family_descends (prefixWord ++ tailWord_471509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471566 : List Nat := [4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_471566 : Nat := 118140960795 + 471566 * 2 ^ 59
def prefixEnd_471566 : Nat := 4983230072969 + 3 ^ 40 * 471566 * 2
def baseEnd_471566 : Nat := 143490381225604284181519

theorem tailTrace_471566 : CollatzResearch.WordTrace tailWord_471566 prefixEnd_471566 143490381225604284181519 := by
  unfold tailWord_471566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149928126200549238253319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11466283339736262604017701 2149928126200549238253319)
  ·
    refine ⟨3224892189300823857379979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149928126200549238253319 3224892189300823857379979)
    ·
      refine ⟨4837338283951235786069969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3224892189300823857379979 4837338283951235786069969)
      ·
        refine ⟨3628003712963426839552477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4837338283951235786069969 3628003712963426839552477)
        ·
          refine ⟨1360501392361285064832179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3628003712963426839552477 1360501392361285064832179)
          ·
            refine ⟨2040752088541927597248269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360501392361285064832179 2040752088541927597248269)
            ·
              refine ⟨765282033203222848968101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2040752088541927597248269 765282033203222848968101)
              ·
                refine ⟨143490381225604284181519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765282033203222848968101 143490381225604284181519)
                ·
                  rfl

theorem cell19_471566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_471566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471566 prefixEnd_471566 := by exact prefixLift 471566
  have htrace : WordTrace (prefixWord ++ tailWord_471566) baseStart_471566 baseEnd_471566 := by
    simpa [prefixWord, tailWord_471566, baseEnd_471566] using wordTrace_append hprefix tailTrace_471566
  have hstable : (prefixWord ++ tailWord_471566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471566).length < 2 ^ (prefixWord ++ tailWord_471566).sum := by decide
  have hdescent : baseEnd_471566 < baseStart_471566 := by decide
  rcases family_descends (prefixWord ++ tailWord_471566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471585 : List Nat := [1, 2, 3, 2, 2, 1, 5, 3]
def baseStart_471585 : Nat := 118140960795 + 471585 * 2 ^ 59
def prefixEnd_471585 : Nat := 4983230072969 + 3 ^ 40 * 471585 * 2
def baseEnd_471585 : Nat := 143496162637417869759245

theorem tailTrace_471585 : CollatzResearch.WordTrace tailWord_471585 prefixEnd_471585 143496162637417869759245 := by
  unfold tailWord_471585
  simp only [CollatzResearch.WordTrace]
  refine ⟨17200117996535560150968209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11466745331023706767312139 17200117996535560150968209)
  ·
    refine ⟨12900088497401670113226157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17200117996535560150968209 12900088497401670113226157)
    ·
      refine ⟨4837533186525626292459809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12900088497401670113226157 4837533186525626292459809)
      ·
        refine ⟨3628149889894219719344857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4837533186525626292459809 3628149889894219719344857)
        ·
          refine ⟨2721112417420664789508643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3628149889894219719344857 2721112417420664789508643)
          ·
            refine ⟨4081668626130997184262965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721112417420664789508643 4081668626130997184262965)
            ·
              refine ⟨382656433699780986024653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4081668626130997184262965 382656433699780986024653)
              ·
                refine ⟨143496162637417869759245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382656433699780986024653 143496162637417869759245)
                ·
                  rfl

theorem cell19_471585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_471585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471585 prefixEnd_471585 := by exact prefixLift 471585
  have htrace : WordTrace (prefixWord ++ tailWord_471585) baseStart_471585 baseEnd_471585 := by
    simpa [prefixWord, tailWord_471585, baseEnd_471585] using wordTrace_append hprefix tailTrace_471585
  have hstable : (prefixWord ++ tailWord_471585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471585).length < 2 ^ (prefixWord ++ tailWord_471585).sum := by decide
  have hdescent : baseEnd_471585 < baseStart_471585 := by decide
  rcases family_descends (prefixWord ++ tailWord_471585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471661 : List Nat := [1, 5, 1, 1, 3, 3, 5]
def baseStart_471661 : Nat := 118140960795 + 471661 * 2 ^ 59
def prefixEnd_471661 : Nat := 4983230072969 + 3 ^ 40 * 471661 * 2
def baseEnd_471661 : Nat := 47839762761557404023383

theorem tailTrace_471661 : CollatzResearch.WordTrace tailWord_471661 prefixEnd_471661 47839762761557404023383 := by
  unfold tailWord_471661
  simp only [CollatzResearch.WordTrace]
  refine ⟨17202889944260225130734837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11468593296173483420489891 17202889944260225130734837)
  ·
    refine ⟨1612770932274396106006391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17202889944260225130734837 1612770932274396106006391)
    ·
      refine ⟨2419156398411594159009587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612770932274396106006391 2419156398411594159009587)
      ·
        refine ⟨3628734597617391238514381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419156398411594159009587 3628734597617391238514381)
        ·
          refine ⟨1360775474106521714442893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3628734597617391238514381 1360775474106521714442893)
          ·
            refine ⟨510290802789945642916085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1360775474106521714442893 510290802789945642916085)
            ·
              refine ⟨47839762761557404023383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 510290802789945642916085 47839762761557404023383)
              ·
                rfl

theorem cell19_471661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_471661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471661 prefixEnd_471661 := by exact prefixLift 471661
  have htrace : WordTrace (prefixWord ++ tailWord_471661) baseStart_471661 baseEnd_471661 := by
    simpa [prefixWord, tailWord_471661, baseEnd_471661] using wordTrace_append hprefix tailTrace_471661
  have hstable : (prefixWord ++ tailWord_471661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471661).length < 2 ^ (prefixWord ++ tailWord_471661).sum := by decide
  have hdescent : baseEnd_471661 < baseStart_471661 := by decide
  rcases family_descends (prefixWord ++ tailWord_471661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471735 : List Nat := [1, 1, 3, 1, 7, 1, 1, 4]
def baseStart_471735 : Nat := 118140960795 + 471735 * 2 ^ 59
def prefixEnd_471735 : Nat := 4983230072969 + 3 ^ 40 * 471735 * 2
def baseEnd_471735 : Nat := 143541805362261966425503

theorem tailTrace_471735 : CollatzResearch.WordTrace tailWord_471735 prefixEnd_471735 143541805362261966425503 := by
  unfold tailWord_471735
  simp only [CollatzResearch.WordTrace]
  refine ⟨17205588945992135768928659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11470392630661423845952439 17205588945992135768928659)
  ·
    refine ⟨25808383418988203653392989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17205588945992135768928659 25808383418988203653392989)
    ·
      refine ⟨9678143782120576370022371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25808383418988203653392989 9678143782120576370022371)
      ·
        refine ⟨14517215673180864555033557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9678143782120576370022371 14517215673180864555033557)
        ·
          refine ⟨340247242340176513008599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14517215673180864555033557 340247242340176513008599)
          ·
            refine ⟨510370863510264769512899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340247242340176513008599 510370863510264769512899)
            ·
              refine ⟨765556295265397154269349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510370863510264769512899 765556295265397154269349)
              ·
                refine ⟨143541805362261966425503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765556295265397154269349 143541805362261966425503)
                ·
                  rfl

theorem cell19_471735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 4].length) (baseStart_471735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471735 prefixEnd_471735 := by exact prefixLift 471735
  have htrace : WordTrace (prefixWord ++ tailWord_471735) baseStart_471735 baseEnd_471735 := by
    simpa [prefixWord, tailWord_471735, baseEnd_471735] using wordTrace_append hprefix tailTrace_471735
  have hstable : (prefixWord ++ tailWord_471735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471735).length < 2 ^ (prefixWord ++ tailWord_471735).sum := by decide
  have hdescent : baseEnd_471735 < baseStart_471735 := by decide
  rcases family_descends (prefixWord ++ tailWord_471735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471750 : List Nat := [6, 1, 2, 1, 2, 1, 3, 3]
def baseStart_471750 : Nat := 118140960795 + 471750 * 2 ^ 59
def prefixEnd_471750 : Nat := 4983230072969 + 3 ^ 40 * 471750 * 2
def baseEnd_471750 : Nat := 143546369634746376092129

theorem tailTrace_471750 : CollatzResearch.WordTrace tailWord_471750 prefixEnd_471750 143546369634746376092129 := by
  unfold tailWord_471750
  simp only [CollatzResearch.WordTrace]
  refine ⟨537691751279306041585147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11470757360625195553816469 537691751279306041585147)
  ·
    refine ⟨806537626918959062377721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 537691751279306041585147 806537626918959062377721)
    ·
      refine ⟨604903220189219296783291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 806537626918959062377721 604903220189219296783291)
      ·
        refine ⟨907354830283828945174937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604903220189219296783291 907354830283828945174937)
        ·
          refine ⟨680516122712871708881203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 907354830283828945174937 680516122712871708881203)
          ·
            refine ⟨1020774184069307563321805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680516122712871708881203 1020774184069307563321805)
            ·
              refine ⟨382790319025990336245677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1020774184069307563321805 382790319025990336245677)
              ·
                refine ⟨143546369634746376092129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 382790319025990336245677 143546369634746376092129)
                ·
                  rfl

theorem cell19_471750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_471750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471750 prefixEnd_471750 := by exact prefixLift 471750
  have htrace : WordTrace (prefixWord ++ tailWord_471750) baseStart_471750 baseEnd_471750 := by
    simpa [prefixWord, tailWord_471750, baseEnd_471750] using wordTrace_append hprefix tailTrace_471750
  have hstable : (prefixWord ++ tailWord_471750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471750).length < 2 ^ (prefixWord ++ tailWord_471750).sum := by decide
  have hdescent : baseEnd_471750 < baseStart_471750 := by decide
  rcases family_descends (prefixWord ++ tailWord_471750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471777 : List Nat := [1, 2, 3, 1, 4, 2, 6]
def baseStart_471777 : Nat := 118140960795 + 471777 * 2 ^ 59
def prefixEnd_471777 : Nat := 4983230072969 + 3 ^ 40 * 471777 * 2
def baseEnd_471777 : Nat := 47851528441739437830685

theorem tailTrace_471777 : CollatzResearch.WordTrace tailWord_471777 prefixEnd_471777 47851528441739437830685 := by
  unfold tailWord_471777
  simp only [CollatzResearch.WordTrace]
  refine ⟨17207120811839976941957585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11471413874559984627971723 17207120811839976941957585)
  ·
    refine ⟨12905340608879982706468189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17207120811839976941957585 12905340608879982706468189)
    ·
      refine ⟨4839502728329993514925571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12905340608879982706468189 4839502728329993514925571)
      ·
        refine ⟨7259254092494990272388357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4839502728329993514925571 7259254092494990272388357)
        ·
          refine ⟨1361110142342810676072817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7259254092494990272388357 1361110142342810676072817)
          ·
            refine ⟨1020832606757108007054613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361110142342810676072817 1020832606757108007054613)
            ·
              refine ⟨47851528441739437830685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1020832606757108007054613 47851528441739437830685)
              ·
                rfl

theorem cell19_471777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_471777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471777 prefixEnd_471777 := by exact prefixLift 471777
  have htrace : WordTrace (prefixWord ++ tailWord_471777) baseStart_471777 baseEnd_471777 := by
    simpa [prefixWord, tailWord_471777, baseEnd_471777] using wordTrace_append hprefix tailTrace_471777
  have hstable : (prefixWord ++ tailWord_471777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471777).length < 2 ^ (prefixWord ++ tailWord_471777).sum := by decide
  have hdescent : baseEnd_471777 < baseStart_471777 := by decide
  rcases family_descends (prefixWord ++ tailWord_471777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471906 : List Nat := [3, 3, 2, 1, 3, 2, 1, 4]
def baseStart_471906 : Nat := 118140960795 + 471906 * 2 ^ 59
def prefixEnd_471906 : Nat := 4983230072969 + 3 ^ 40 * 471906 * 2
def baseEnd_471906 : Nat := 143593838068584236625037

theorem tailTrace_471906 : CollatzResearch.WordTrace tailWord_471906 prefixEnd_471906 143593838068584236625037 := by
  unfold tailWord_471906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4302956457093157993350893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11474550552248421315602381 4302956457093157993350893)
  ·
    refine ⟨1613608671409934247506585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4302956457093157993350893 1613608671409934247506585)
    ·
      refine ⟨1210206503557450685629939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1613608671409934247506585 1210206503557450685629939)
      ·
        refine ⟨1815309755336176028444909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210206503557450685629939 1815309755336176028444909)
        ·
          refine ⟨680741158251066010666841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1815309755336176028444909 680741158251066010666841)
          ·
            refine ⟨510555868688299508000131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680741158251066010666841 510555868688299508000131)
            ·
              refine ⟨765833803032449262000197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510555868688299508000131 765833803032449262000197)
              ·
                refine ⟨143593838068584236625037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765833803032449262000197 143593838068584236625037)
                ·
                  rfl

theorem cell19_471906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_471906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471906 prefixEnd_471906 := by exact prefixLift 471906
  have htrace : WordTrace (prefixWord ++ tailWord_471906) baseStart_471906 baseEnd_471906 := by
    simpa [prefixWord, tailWord_471906, baseEnd_471906] using wordTrace_append hprefix tailTrace_471906
  have hstable : (prefixWord ++ tailWord_471906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471906).length < 2 ^ (prefixWord ++ tailWord_471906).sum := by decide
  have hdescent : baseEnd_471906 < baseStart_471906 := by decide
  rcases family_descends (prefixWord ++ tailWord_471906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_471908 : List Nat := [2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_471908 : Nat := 118140960795 + 471908 * 2 ^ 59
def prefixEnd_471908 : Nat := 4983230072969 + 3 ^ 40 * 471908 * 2
def baseEnd_471908 : Nat := 143594446638248824580587

theorem tailTrace_471908 : CollatzResearch.WordTrace tailWord_471908 prefixEnd_471908 143594446638248824580587 := by
  unfold tailWord_471908
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605949387182693157488189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11474599182910257543317585 8605949387182693157488189)
  ·
    refine ⟨3227231020193509934058071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8605949387182693157488189 3227231020193509934058071)
    ·
      refine ⟨4840846530290264901087107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3227231020193509934058071 4840846530290264901087107)
      ·
        refine ⟨7261269795435397351630661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4840846530290264901087107 7261269795435397351630661)
        ·
          refine ⟨1361488086644137003430749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7261269795435397351630661 1361488086644137003430749)
          ·
            refine ⟨510558032491551376286531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1361488086644137003430749 510558032491551376286531)
            ·
              refine ⟨765837048737327064429797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510558032491551376286531 765837048737327064429797)
              ·
                refine ⟨143594446638248824580587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765837048737327064429797 143594446638248824580587)
                ·
                  rfl

theorem cell19_471908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_471908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_471908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_471908 prefixEnd_471908 := by exact prefixLift 471908
  have htrace : WordTrace (prefixWord ++ tailWord_471908) baseStart_471908 baseEnd_471908 := by
    simpa [prefixWord, tailWord_471908, baseEnd_471908] using wordTrace_append hprefix tailTrace_471908
  have hstable : (prefixWord ++ tailWord_471908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_471908).length < 2 ^ (prefixWord ++ tailWord_471908).sum := by decide
  have hdescent : baseEnd_471908 < baseStart_471908 := by decide
  rcases family_descends (prefixWord ++ tailWord_471908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
