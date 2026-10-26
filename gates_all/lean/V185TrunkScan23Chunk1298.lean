import V185TrunkScan23Chunk1297

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7688012 : List Nat := [2, 2, 1, 3, 4, 1, 2, 3, 1, 2, 2]
def baseStart_7688012 : Nat := 118140960795 + 7688012 * 2 ^ 59
def prefixEnd_7688012 : Nat := 4983230072969 + 3 ^ 40 * 7688012 * 2
def baseEnd_7688012 : Nat := 3947645433533879851393483

theorem tailTrace_7688012 : CollatzResearch.WordTrace tailWord_7688012 prefixEnd_7688012 3947645433533879851393483 := by
  unfold tailWord_7688012
  simp only [CollatzResearch.WordTrace]
  refine ⟨140202416911826503380405145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186936555882435337840540193 140202416911826503380405145)
  ·
    refine ⟨105151812683869877535303859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140202416911826503380405145 105151812683869877535303859)
    ·
      refine ⟨157727719025804816302955789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105151812683869877535303859 157727719025804816302955789)
      ·
        refine ⟨59147894634676806113608421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157727719025804816302955789 59147894634676806113608421)
        ·
          refine ⟨11090230244001901146301579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59147894634676806113608421 11090230244001901146301579)
          ·
            refine ⟨16635345366002851719452369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090230244001901146301579 16635345366002851719452369)
            ·
              refine ⟨12476509024502138789589277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16635345366002851719452369 12476509024502138789589277)
              ·
                refine ⟨4678690884188302046095979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12476509024502138789589277 4678690884188302046095979)
                ·
                  refine ⟨7018036326282453069143969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678690884188302046095979 7018036326282453069143969)
                  ·
                    refine ⟨5263527244711839801857977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7018036326282453069143969 5263527244711839801857977)
                    ·
                      refine ⟨3947645433533879851393483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263527244711839801857977 3947645433533879851393483)
                      ·
                        rfl

theorem cell23_7688012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_7688012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688012 prefixEnd_7688012 := by exact prefixLift 7688012
  have htrace : WordTrace (prefixWord ++ tailWord_7688012) baseStart_7688012 baseEnd_7688012 := by
    simpa [prefixWord, tailWord_7688012, baseEnd_7688012] using wordTrace_append hprefix tailTrace_7688012
  have hstable : (prefixWord ++ tailWord_7688012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688012).length < 2 ^ (prefixWord ++ tailWord_7688012).sum := by decide
  have hdescent : baseEnd_7688012 < baseStart_7688012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688044 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_7688044 : Nat := 118140960795 + 7688044 * 2 ^ 59
def prefixEnd_7688044 : Nat := 4983230072969 + 3 ^ 40 * 7688044 * 2
def baseEnd_7688044 : Nat := 1315887288304941242064445

theorem tailTrace_7688044 : CollatzResearch.WordTrace tailWord_7688044 prefixEnd_7688044 1315887288304941242064445 := by
  unfold tailWord_7688044
  simp only [CollatzResearch.WordTrace]
  refine ⟨140203000479768538112987593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186937333973024717483983457 140203000479768538112987593)
  ·
    refine ⟨105152250359826403584740695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140203000479768538112987593 105152250359826403584740695)
    ·
      refine ⟨157728375539739605377111043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105152250359826403584740695 157728375539739605377111043)
      ·
        refine ⟨236592563309609408065666565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157728375539739605377111043 236592563309609408065666565)
        ·
          refine ⟨44361105620551764012312481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236592563309609408065666565 44361105620551764012312481)
          ·
            refine ⟨33270829215413823009234361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44361105620551764012312481 33270829215413823009234361)
            ·
              refine ⟨24953121911560367256925771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33270829215413823009234361 24953121911560367256925771)
              ·
                refine ⟨37429682867340550885388657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24953121911560367256925771 37429682867340550885388657)
                ·
                  refine ⟨28072262150505413164041493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37429682867340550885388657 28072262150505413164041493)
                  ·
                    refine ⟨1315887288304941242064445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28072262150505413164041493 1315887288304941242064445)
                    ·
                      rfl

theorem cell23_7688044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_7688044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688044 prefixEnd_7688044 := by exact prefixLift 7688044
  have htrace : WordTrace (prefixWord ++ tailWord_7688044) baseStart_7688044 baseEnd_7688044 := by
    simpa [prefixWord, tailWord_7688044, baseEnd_7688044] using wordTrace_append hprefix tailTrace_7688044
  have hstable : (prefixWord ++ tailWord_7688044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688044).length < 2 ^ (prefixWord ++ tailWord_7688044).sum := by decide
  have hdescent : baseEnd_7688044 < baseStart_7688044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688068 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_7688068 : Nat := 118140960795 + 7688068 * 2 ^ 59
def prefixEnd_7688068 : Nat := 4983230072969 + 3 ^ 40 * 7688068 * 2
def baseEnd_7688068 : Nat := 3947674188450531632293225

theorem tailTrace_7688068 : CollatzResearch.WordTrace tailWord_7688068 prefixEnd_7688068 3947674188450531632293225 := by
  unfold tailWord_7688068
  simp only [CollatzResearch.WordTrace]
  refine ⟨140203438155725064162424429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186937917540966752216565905 140203438155725064162424429)
  ·
    refine ⟨52576289308396899060909161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140203438155725064162424429 52576289308396899060909161)
    ·
      refine ⟨39432216981297674295681871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52576289308396899060909161 39432216981297674295681871)
      ·
        refine ⟨59148325471946511443522807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39432216981297674295681871 59148325471946511443522807)
        ·
          refine ⟨88722488207919767165284211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59148325471946511443522807 88722488207919767165284211)
          ·
            refine ⟨133083732311879650747926317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88722488207919767165284211 133083732311879650747926317)
            ·
              refine ⟨49906399616954869030472369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133083732311879650747926317 49906399616954869030472369)
              ·
                refine ⟨37429799712716151772854277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49906399616954869030472369 37429799712716151772854277)
                ·
                  refine ⟨7018087446134278457410177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37429799712716151772854277 7018087446134278457410177)
                  ·
                    refine ⟨5263565584600708843057633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7018087446134278457410177 5263565584600708843057633)
                    ·
                      refine ⟨3947674188450531632293225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263565584600708843057633 3947674188450531632293225)
                      ·
                        rfl

theorem cell23_7688068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_7688068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688068 prefixEnd_7688068 := by exact prefixLift 7688068
  have htrace : WordTrace (prefixWord ++ tailWord_7688068) baseStart_7688068 baseEnd_7688068 := by
    simpa [prefixWord, tailWord_7688068, baseEnd_7688068] using wordTrace_append hprefix tailTrace_7688068
  have hstable : (prefixWord ++ tailWord_7688068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688068).length < 2 ^ (prefixWord ++ tailWord_7688068).sum := by decide
  have hdescent : baseEnd_7688068 < baseStart_7688068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688071 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_7688071 : Nat := 118140960795 + 7688071 * 2 ^ 59
def prefixEnd_7688071 : Nat := 4983230072969 + 3 ^ 40 * 7688071 * 2
def baseEnd_7688071 : Nat := 3947675728892495120555711

theorem tailTrace_7688071 : CollatzResearch.WordTrace tailWord_7688071 prefixEnd_7688071 3947675728892495120555711 := by
  unfold tailWord_7688071
  simp only [CollatzResearch.WordTrace]
  refine ⟨280406985730439259837208067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186937990486959506558138711 280406985730439259837208067)
  ·
    refine ⟨420610478595658889755812101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280406985730439259837208067 420610478595658889755812101)
    ·
      refine ⟨78864464736686041829214769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420610478595658889755812101 78864464736686041829214769)
      ·
        refine ⟨59148348552514531371911077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78864464736686041829214769 59148348552514531371911077)
        ·
          refine ⟨11090315353596474632233327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59148348552514531371911077 11090315353596474632233327)
          ·
            refine ⟨16635473030394711948349991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090315353596474632233327 16635473030394711948349991)
            ·
              refine ⟨24953209545592067922524987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16635473030394711948349991 24953209545592067922524987)
              ·
                refine ⟨37429814318388101883787481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24953209545592067922524987 37429814318388101883787481)
                ·
                  refine ⟨28072360738791076412840611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37429814318388101883787481 28072360738791076412840611)
                  ·
                    refine ⟨42108541108186614619260917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28072360738791076412840611 42108541108186614619260917)
                    ·
                      refine ⟨3947675728892495120555711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42108541108186614619260917 3947675728892495120555711)
                      ·
                        rfl

theorem cell23_7688071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_7688071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688071 prefixEnd_7688071 := by exact prefixLift 7688071
  have htrace : WordTrace (prefixWord ++ tailWord_7688071) baseStart_7688071 baseEnd_7688071 := by
    simpa [prefixWord, tailWord_7688071, baseEnd_7688071] using wordTrace_append hprefix tailTrace_7688071
  have hstable : (prefixWord ++ tailWord_7688071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688071).length < 2 ^ (prefixWord ++ tailWord_7688071).sum := by decide
  have hdescent : baseEnd_7688071 < baseStart_7688071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688121 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 2, 5]
def baseStart_7688121 : Nat := 118140960795 + 7688121 * 2 ^ 59
def prefixEnd_7688121 : Nat := 4983230072969 + 3 ^ 40 * 7688121 * 2
def baseEnd_7688121 : Nat := 1315900467641739974976827

theorem tailTrace_7688121 : CollatzResearch.WordTrace tailWord_7688121 prefixEnd_7688121 1315900467641739974976827 := by
  unfold tailWord_7688121
  simp only [CollatzResearch.WordTrace]
  refine ⟨280408809380258118376528217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186939206253505412251018811 280408809380258118376528217)
  ·
    refine ⟨210306607035193588782396163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280408809380258118376528217 210306607035193588782396163)
    ·
      refine ⟨315459910552790383173594245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210306607035193588782396163 315459910552790383173594245)
      ·
        refine ⟨59148733228648196845048921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315459910552790383173594245 59148733228648196845048921)
        ·
          refine ⟨44361549921486147633786691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59148733228648196845048921 44361549921486147633786691)
          ·
            refine ⟨66542324882229221450680037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44361549921486147633786691 66542324882229221450680037)
            ·
              refine ⟨12476685915417979022002507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66542324882229221450680037 12476685915417979022002507)
              ·
                refine ⟨18715028873126968533003761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12476685915417979022002507 18715028873126968533003761)
                ·
                  refine ⟨14036271654845226399752821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18715028873126968533003761 14036271654845226399752821)
                  ·
                    refine ⟨1315900467641739974976827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14036271654845226399752821 1315900467641739974976827)
                    ·
                      rfl

theorem cell23_7688121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_7688121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688121 prefixEnd_7688121 := by exact prefixLift 7688121
  have htrace : WordTrace (prefixWord ++ tailWord_7688121) baseStart_7688121 baseEnd_7688121 := by
    simpa [prefixWord, tailWord_7688121, baseEnd_7688121] using wordTrace_append hprefix tailTrace_7688121
  have hstable : (prefixWord ++ tailWord_7688121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688121).length < 2 ^ (prefixWord ++ tailWord_7688121).sum := by decide
  have hdescent : baseEnd_7688121 < baseStart_7688121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688151 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 3, 4]
def baseStart_7688151 : Nat := 118140960795 + 7688151 * 2 ^ 59
def prefixEnd_7688151 : Nat := 4983230072969 + 3 ^ 40 * 7688151 * 2
def baseEnd_7688151 : Nat := 1315905602448284935851781

theorem tailTrace_7688151 : CollatzResearch.WordTrace tailWord_7688151 prefixEnd_7688151 1315905602448284935851781 := by
  unfold tailWord_7688151
  simp only [CollatzResearch.WordTrace]
  refine ⟨280409903570149433500120307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186939935713432955666746871 280409903570149433500120307)
  ·
    refine ⟨420614855355224150250180461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280409903570149433500120307 420614855355224150250180461)
    ·
      refine ⟨157730570758209056343817673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420614855355224150250180461 157730570758209056343817673)
      ·
        refine ⟨118297928068656792257863255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157730570758209056343817673 118297928068656792257863255)
        ·
          refine ⟨177446892102985188386794883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118297928068656792257863255 177446892102985188386794883)
          ·
            refine ⟨266170338154477782580192325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177446892102985188386794883 266170338154477782580192325)
            ·
              refine ⟨49906938403964584233786061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266170338154477782580192325 49906938403964584233786061)
              ·
                refine ⟨18715101901486719087669773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49906938403964584233786061 18715101901486719087669773)
                ·
                  refine ⟨7018163213057519657876165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18715101901486719087669773 7018163213057519657876165)
                  ·
                    refine ⟨1315905602448284935851781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7018163213057519657876165 1315905602448284935851781)
                    ·
                      rfl

theorem cell23_7688151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_7688151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688151 prefixEnd_7688151 := by exact prefixLift 7688151
  have htrace : WordTrace (prefixWord ++ tailWord_7688151) baseStart_7688151 baseEnd_7688151 := by
    simpa [prefixWord, tailWord_7688151, baseEnd_7688151] using wordTrace_append hprefix tailTrace_7688151
  have hstable : (prefixWord ++ tailWord_7688151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688151).length < 2 ^ (prefixWord ++ tailWord_7688151).sum := by decide
  have hdescent : baseEnd_7688151 < baseStart_7688151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688161 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_7688161 : Nat := 118140960795 + 7688161 * 2 ^ 59
def prefixEnd_7688161 : Nat := 4983230072969 + 3 ^ 40 * 7688161 * 2
def baseEnd_7688161 : Nat := 3947721942151399768430297

theorem tailTrace_7688161 : CollatzResearch.WordTrace tailWord_7688161 prefixEnd_7688161 3947721942151399768430297 := by
  unfold tailWord_7688161
  simp only [CollatzResearch.WordTrace]
  refine ⟨280410268300113205207984337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186940178866742136805322891 280410268300113205207984337)
  ·
    refine ⟨210307701225084903905988253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280410268300113205207984337 210307701225084903905988253)
    ·
      refine ⟨78865387959406838964745595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210307701225084903905988253 78865387959406838964745595)
      ·
        refine ⟨118298081939110258447118393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78865387959406838964745595 118298081939110258447118393)
        ·
          refine ⟨88723561454332693835338795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118298081939110258447118393 88723561454332693835338795)
          ·
            refine ⟨133085342181499040753008193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88723561454332693835338795 133085342181499040753008193)
            ·
              refine ⟨99814006636124280564756145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133085342181499040753008193 99814006636124280564756145)
              ·
                refine ⟨74860504977093210423567109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99814006636124280564756145 74860504977093210423567109)
                ·
                  refine ⟨14036344683204976954418833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74860504977093210423567109 14036344683204976954418833)
                  ·
                    refine ⟨10527258512403732715814125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14036344683204976954418833 10527258512403732715814125)
                    ·
                      refine ⟨3947721942151399768430297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10527258512403732715814125 3947721942151399768430297)
                      ·
                        rfl

theorem cell23_7688161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_7688161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688161 prefixEnd_7688161 := by exact prefixLift 7688161
  have htrace : WordTrace (prefixWord ++ tailWord_7688161) baseStart_7688161 baseEnd_7688161 := by
    simpa [prefixWord, tailWord_7688161, baseEnd_7688161] using wordTrace_append hprefix tailTrace_7688161
  have hstable : (prefixWord ++ tailWord_7688161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688161).length < 2 ^ (prefixWord ++ tailWord_7688161).sum := by decide
  have hdescent : baseEnd_7688161 < baseStart_7688161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688185 : List Nat := [1, 2, 1, 3, 1, 5, 2, 3, 1, 4]
def baseStart_7688185 : Nat := 118140960795 + 7688185 * 2 ^ 59
def prefixEnd_7688185 : Nat := 4983230072969 + 3 ^ 40 * 7688185 * 2
def baseEnd_7688185 : Nat := 1315911421895702558176729

theorem tailTrace_7688185 : CollatzResearch.WordTrace tailWord_7688185 prefixEnd_7688185 1315911421895702558176729 := by
  unfold tailWord_7688185
  simp only [CollatzResearch.WordTrace]
  refine ⟨280411143652026257306858009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186940762434684171537905339 280411143652026257306858009)
  ·
    refine ⟨210308357739019692980143507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280411143652026257306858009 210308357739019692980143507)
    ·
      refine ⟨315462536608529539470215261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210308357739019692980143507 315462536608529539470215261)
      ·
        refine ⟨118298451228198577301330723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315462536608529539470215261 118298451228198577301330723)
        ·
          refine ⟨177447676842297865951996085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118298451228198577301330723 177447676842297865951996085)
          ·
            refine ⟨16635719703965424932999633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177447676842297865951996085 16635719703965424932999633)
            ·
              refine ⟨12476789777974068699749725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16635719703965424932999633 12476789777974068699749725)
              ·
                refine ⟨4678796166740275762406147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12476789777974068699749725 4678796166740275762406147)
                ·
                  refine ⟨7018194250110413643609221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678796166740275762406147 7018194250110413643609221)
                  ·
                    refine ⟨1315911421895702558176729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7018194250110413643609221 1315911421895702558176729)
                    ·
                      rfl

theorem cell23_7688185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 4].length) (baseStart_7688185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688185 prefixEnd_7688185 := by exact prefixLift 7688185
  have htrace : WordTrace (prefixWord ++ tailWord_7688185) baseStart_7688185 baseEnd_7688185 := by
    simpa [prefixWord, tailWord_7688185, baseEnd_7688185] using wordTrace_append hprefix tailTrace_7688185
  have hstable : (prefixWord ++ tailWord_7688185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688185).length < 2 ^ (prefixWord ++ tailWord_7688185).sum := by decide
  have hdescent : baseEnd_7688185 < baseStart_7688185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688215 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 6]
def baseStart_7688215 : Nat := 118140960795 + 7688215 * 2 ^ 59
def prefixEnd_7688215 : Nat := 4983230072969 + 3 ^ 40 * 7688215 * 2
def baseEnd_7688215 : Nat := 438638852234082506350561

theorem tailTrace_7688215 : CollatzResearch.WordTrace tailWord_7688215 prefixEnd_7688215 438638852234082506350561 := by
  unfold tailWord_7688215
  simp only [CollatzResearch.WordTrace]
  refine ⟨280412237841917572430450099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186941491894611714953633399 280412237841917572430450099)
  ·
    refine ⟨420618356762876358645675149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280412237841917572430450099 420618356762876358645675149)
    ·
      refine ⟨157731883786078634492128181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420618356762876358645675149 157731883786078634492128181)
      ·
        refine ⟨14787364104944871983637017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157731883786078634492128181 14787364104944871983637017)
        ·
          refine ⟨11090523078708653987727763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14787364104944871983637017 11090523078708653987727763)
          ·
            refine ⟨16635784618062980981591645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090523078708653987727763 16635784618062980981591645)
            ·
              refine ⟨6238419231773617868096867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16635784618062980981591645 6238419231773617868096867)
              ·
                refine ⟨9357628847660426802145301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238419231773617868096867 9357628847660426802145301)
                ·
                  refine ⟨438638852234082506350561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9357628847660426802145301 438638852234082506350561)
                  ·
                    rfl

theorem cell23_7688215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 6].length) (baseStart_7688215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688215 prefixEnd_7688215 := by exact prefixLift 7688215
  have htrace : WordTrace (prefixWord ++ tailWord_7688215) baseStart_7688215 baseEnd_7688215 := by
    simpa [prefixWord, tailWord_7688215, baseEnd_7688215] using wordTrace_append hprefix tailTrace_7688215
  have hstable : (prefixWord ++ tailWord_7688215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688215).length < 2 ^ (prefixWord ++ tailWord_7688215).sum := by decide
  have hdescent : baseEnd_7688215 < baseStart_7688215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688218 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2]
def baseStart_7688218 : Nat := 118140960795 + 7688218 * 2 ^ 59
def prefixEnd_7688218 : Nat := 4983230072969 + 3 ^ 40 * 7688218 * 2
def baseEnd_7688218 : Nat := 3947751210548706045417535

theorem tailTrace_7688218 : CollatzResearch.WordTrace tailWord_7688218 prefixEnd_7688218 3947751210548706045417535 := by
  unfold tailWord_7688218
  simp only [CollatzResearch.WordTrace]
  refine ⟨70103086815226675985702327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186941564840604469295206205 70103086815226675985702327)
  ·
    refine ⟨105154630222840013978553491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70103086815226675985702327 105154630222840013978553491)
    ·
      refine ⟨157731945334260020967830237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105154630222840013978553491 157731945334260020967830237)
      ·
        refine ⟨59149479500347507862936339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157731945334260020967830237 59149479500347507862936339)
        ·
          refine ⟨88724219250521261794404509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59149479500347507862936339 88724219250521261794404509)
          ·
            refine ⟨33271582218945473172901691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88724219250521261794404509 33271582218945473172901691)
            ·
              refine ⟨49907373328418209759352537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33271582218945473172901691 49907373328418209759352537)
              ·
                refine ⟨37430529996313657319514403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49907373328418209759352537 37430529996313657319514403)
                ·
                  refine ⟨56145794994470485979271605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37430529996313657319514403 56145794994470485979271605)
                  ·
                    refine ⟨5263668280731608060556713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56145794994470485979271605 5263668280731608060556713)
                    ·
                      refine ⟨3947751210548706045417535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263668280731608060556713 3947751210548706045417535)
                      ·
                        rfl

theorem cell23_7688218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_7688218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688218 prefixEnd_7688218 := by exact prefixLift 7688218
  have htrace : WordTrace (prefixWord ++ tailWord_7688218) baseStart_7688218 baseEnd_7688218 := by
    simpa [prefixWord, tailWord_7688218, baseEnd_7688218] using wordTrace_append hprefix tailTrace_7688218
  have hstable : (prefixWord ++ tailWord_7688218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688218).length < 2 ^ (prefixWord ++ tailWord_7688218).sum := by decide
  have hdescent : baseEnd_7688218 < baseStart_7688218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688242 : List Nat := [3, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3]
def baseStart_7688242 : Nat := 118140960795 + 7688242 * 2 ^ 59
def prefixEnd_7688242 : Nat := 4983230072969 + 3 ^ 40 * 7688242 * 2
def baseEnd_7688242 : Nat := 3947763534084413951517425

theorem tailTrace_7688242 : CollatzResearch.WordTrace tailWord_7688242 prefixEnd_7688242 3947763534084413951517425 := by
  unfold tailWord_7688242
  simp only [CollatzResearch.WordTrace]
  refine ⟨70103305653204939010420745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186942148408546504027788653 70103305653204939010420745)
  ·
    refine ⟨52577479239903704257815559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70103305653204939010420745 52577479239903704257815559)
    ·
      refine ⟨78866218859855556386723339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52577479239903704257815559 78866218859855556386723339)
      ·
        refine ⟨118299328289783334580085009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78866218859855556386723339 118299328289783334580085009)
        ·
          refine ⟨88724496217337500935063757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118299328289783334580085009 88724496217337500935063757)
          ·
            refine ⟨33271686081501562850648909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88724496217337500935063757 33271686081501562850648909)
            ·
              refine ⟨12476882280563086068993341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33271686081501562850648909 12476882280563086068993341)
              ·
                refine ⟨4678830855211157275872503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12476882280563086068993341 4678830855211157275872503)
                ·
                  refine ⟨7018246282816735913808755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678830855211157275872503 7018246282816735913808755)
                  ·
                    refine ⟨10527369424225103870713133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7018246282816735913808755 10527369424225103870713133)
                    ·
                      refine ⟨3947763534084413951517425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10527369424225103870713133 3947763534084413951517425)
                      ·
                        rfl

theorem cell23_7688242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_7688242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688242 prefixEnd_7688242 := by exact prefixLift 7688242
  have htrace : WordTrace (prefixWord ++ tailWord_7688242) baseStart_7688242 baseEnd_7688242 := by
    simpa [prefixWord, tailWord_7688242, baseEnd_7688242] using wordTrace_append hprefix tailTrace_7688242
  have hstable : (prefixWord ++ tailWord_7688242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688242).length < 2 ^ (prefixWord ++ tailWord_7688242).sum := by decide
  have hdescent : baseEnd_7688242 < baseStart_7688242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688286 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_7688286 : Nat := 118140960795 + 7688286 * 2 ^ 59
def prefixEnd_7688286 : Nat := 4983230072969 + 3 ^ 40 * 7688286 * 2
def baseEnd_7688286 : Nat := 3947786127233211779367223

theorem tailTrace_7688286 : CollatzResearch.WordTrace tailWord_7688286 prefixEnd_7688286 3947786127233211779367223 := by
  unfold tailWord_7688286
  simp only [CollatzResearch.WordTrace]
  refine ⟨35051853428082543944535589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186943218283106901037523141 35051853428082543944535589)
  ·
    refine ⟨6572222517765476989600423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35051853428082543944535589 6572222517765476989600423)
    ·
      refine ⟨9858333776648215484400635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6572222517765476989600423 9858333776648215484400635)
      ·
        refine ⟨14787500664972323226600953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9858333776648215484400635 14787500664972323226600953)
        ·
          refine ⟨11090625498729242419950715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14787500664972323226600953 11090625498729242419950715)
          ·
            refine ⟨16635938248093863629926073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090625498729242419950715 16635938248093863629926073)
            ·
              refine ⟨12476953686070397722444555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16635938248093863629926073 12476953686070397722444555)
              ·
                refine ⟨18715430529105596583666833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12476953686070397722444555 18715430529105596583666833)
                ·
                  refine ⟨14036572896829197437750125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18715430529105596583666833 14036572896829197437750125)
                  ·
                    refine ⟨5263714836310949039156297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14036572896829197437750125 5263714836310949039156297)
                    ·
                      refine ⟨3947786127233211779367223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263714836310949039156297 3947786127233211779367223)
                      ·
                        rfl

theorem cell23_7688286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_7688286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688286 prefixEnd_7688286 := by exact prefixLift 7688286
  have htrace : WordTrace (prefixWord ++ tailWord_7688286) baseStart_7688286 baseEnd_7688286 := by
    simpa [prefixWord, tailWord_7688286, baseEnd_7688286] using wordTrace_append hprefix tailTrace_7688286
  have hstable : (prefixWord ++ tailWord_7688286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688286).length < 2 ^ (prefixWord ++ tailWord_7688286).sum := by decide
  have hdescent : baseEnd_7688286 < baseStart_7688286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688302 : List Nat := [4, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_7688302 : Nat := 118140960795 + 7688302 * 2 ^ 59
def prefixEnd_7688302 : Nat := 4983230072969 + 3 ^ 40 * 7688302 * 2
def baseEnd_7688302 : Nat := 3947794342923683716767149

theorem tailTrace_7688302 : CollatzResearch.WordTrace tailWord_7688302 prefixEnd_7688302 3947794342923683716767149 := by
  unfold tailWord_7688302
  simp only [CollatzResearch.WordTrace]
  refine ⟨35051926374075298286108395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186943607328401590859244773 35051926374075298286108395)
  ·
    refine ⟨52577889561112947429162593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35051926374075298286108395 52577889561112947429162593)
    ·
      refine ⟨39433417170834710571871945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52577889561112947429162593 39433417170834710571871945)
      ·
        refine ⟨29575062878126032928903959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39433417170834710571871945 29575062878126032928903959)
        ·
          refine ⟨44362594317189049393355939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29575062878126032928903959 44362594317189049393355939)
          ·
            refine ⟨66543891475783574090033909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44362594317189049393355939 66543891475783574090033909)
            ·
              refine ⟨6238489825854710070940679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66543891475783574090033909 6238489825854710070940679)
              ·
                refine ⟨9357734738782065106411019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238489825854710070940679 9357734738782065106411019)
                ·
                  refine ⟨14036602108173097659616529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9357734738782065106411019 14036602108173097659616529)
                  ·
                    refine ⟨10527451581129823244712397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14036602108173097659616529 10527451581129823244712397)
                    ·
                      refine ⟨3947794342923683716767149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10527451581129823244712397 3947794342923683716767149)
                      ·
                        rfl

theorem cell23_7688302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_7688302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688302 prefixEnd_7688302 := by exact prefixLift 7688302
  have htrace : WordTrace (prefixWord ++ tailWord_7688302) baseStart_7688302 baseEnd_7688302 := by
    simpa [prefixWord, tailWord_7688302, baseEnd_7688302] using wordTrace_append hprefix tailTrace_7688302
  have hstable : (prefixWord ++ tailWord_7688302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688302).length < 2 ^ (prefixWord ++ tailWord_7688302).sum := by decide
  have hdescent : baseEnd_7688302 < baseStart_7688302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688316 : List Nat := [2, 2, 2, 1, 1, 6, 2, 2, 1, 2, 2]
def baseStart_7688316 : Nat := 118140960795 + 7688316 * 2 ^ 59
def prefixEnd_7688316 : Nat := 4983230072969 + 3 ^ 40 * 7688316 * 2
def baseEnd_7688316 : Nat := 3947801531652846661992085

theorem tailTrace_7688316 : CollatzResearch.WordTrace tailWord_7688316 prefixEnd_7688316 3947801531652846661992085 := by
  unfold tailWord_7688316
  simp only [CollatzResearch.WordTrace]
  refine ⟨140207960807275833339938401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186943947743034444453251201 140207960807275833339938401)
  ·
    refine ⟨105155970605456875004953801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140207960807275833339938401 105155970605456875004953801)
    ·
      refine ⟨78866977954092656253715351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105155970605456875004953801 78866977954092656253715351)
      ·
        refine ⟨118300466931138984380573027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78866977954092656253715351 118300466931138984380573027)
        ·
          refine ⟨177450700396708476570859541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118300466931138984380573027 177450700396708476570859541)
          ·
            refine ⟨8318001581095709839259041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177450700396708476570859541 8318001581095709839259041)
            ·
              refine ⟨6238501185821782379444281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318001581095709839259041 6238501185821782379444281)
              ·
                refine ⟨4678875889366336784583211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6238501185821782379444281 4678875889366336784583211)
                ·
                  refine ⟨7018313834049505176874817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678875889366336784583211 7018313834049505176874817)
                  ·
                    refine ⟨5263735375537128882656113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7018313834049505176874817 5263735375537128882656113)
                    ·
                      refine ⟨3947801531652846661992085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263735375537128882656113 3947801531652846661992085)
                      ·
                        rfl

theorem cell23_7688316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_7688316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688316 prefixEnd_7688316 := by exact prefixLift 7688316
  have htrace : WordTrace (prefixWord ++ tailWord_7688316) baseStart_7688316 baseEnd_7688316 := by
    simpa [prefixWord, tailWord_7688316, baseEnd_7688316] using wordTrace_append hprefix tailTrace_7688316
  have hstable : (prefixWord ++ tailWord_7688316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688316).length < 2 ^ (prefixWord ++ tailWord_7688316).sum := by decide
  have hdescent : baseEnd_7688316 < baseStart_7688316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688325 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 3, 3, 2]
def baseStart_7688325 : Nat := 118140960795 + 7688325 * 2 ^ 59
def prefixEnd_7688325 : Nat := 4983230072969 + 3 ^ 40 * 7688325 * 2
def baseEnd_7688325 : Nat := 3947806152978737126779543

theorem tailTrace_7688325 : CollatzResearch.WordTrace tailWord_7688325 prefixEnd_7688325 3947806152978737126779543 := by
  unfold tailWord_7688325
  simp only [CollatzResearch.WordTrace]
  refine ⟨280416249871519061216954429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186944166581012707477969619 280416249871519061216954429)
  ·
    refine ⟨105156093701819647956357911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280416249871519061216954429 105156093701819647956357911)
    ·
      refine ⟨157734140552729471934536867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105156093701819647956357911 157734140552729471934536867)
      ·
        refine ⟨236601210829094207901805301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157734140552729471934536867 236601210829094207901805301)
        ·
          refine ⟨22181363515227581990794247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236601210829094207901805301 22181363515227581990794247)
          ·
            refine ⟨33272045272841372986191371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22181363515227581990794247 33272045272841372986191371)
            ·
              refine ⟨49908067909262059479287057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33272045272841372986191371 49908067909262059479287057)
              ·
                refine ⟨37431050931946544609465293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49908067909262059479287057 37431050931946544609465293)
                ·
                  refine ⟨14036644099479954228549485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37431050931946544609465293 14036644099479954228549485)
                  ·
                    refine ⟨5263741537304982835706057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14036644099479954228549485 5263741537304982835706057)
                    ·
                      refine ⟨3947806152978737126779543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263741537304982835706057 3947806152978737126779543)
                      ·
                        rfl

theorem cell23_7688325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_7688325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688325 prefixEnd_7688325 := by exact prefixLift 7688325
  have htrace : WordTrace (prefixWord ++ tailWord_7688325) baseStart_7688325 baseEnd_7688325 := by
    simpa [prefixWord, tailWord_7688325, baseEnd_7688325] using wordTrace_append hprefix tailTrace_7688325
  have hstable : (prefixWord ++ tailWord_7688325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688325).length < 2 ^ (prefixWord ++ tailWord_7688325).sum := by decide
  have hdescent : baseEnd_7688325 < baseStart_7688325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688338 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7688338 : Nat := 118140960795 + 7688338 * 2 ^ 59
def prefixEnd_7688338 : Nat := 4983230072969 + 3 ^ 40 * 7688338 * 2
def baseEnd_7688338 : Nat := 3947812828227245575916983

theorem tailTrace_7688338 : CollatzResearch.WordTrace tailWord_7688338 prefixEnd_7688338 3947812828227245575916983 := by
  unfold tailWord_7688338
  simp only [CollatzResearch.WordTrace]
  refine ⟨70104181005117991109294417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186944482680314642958118445 70104181005117991109294417)
  ·
    refine ⟨52578135753838493331970813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70104181005117991109294417 52578135753838493331970813)
    ·
      refine ⟨19716800907689434999489055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52578135753838493331970813 19716800907689434999489055)
      ·
        refine ⟨29575201361534152499233583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19716800907689434999489055 29575201361534152499233583)
        ·
          refine ⟨44362802042301228748850375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29575201361534152499233583 44362802042301228748850375)
          ·
            refine ⟨66544203063451843123275563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44362802042301228748850375 66544203063451843123275563)
            ·
              refine ⟨99816304595177764684913345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66544203063451843123275563 99816304595177764684913345)
              ·
                refine ⟨74862228446383323513685009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99816304595177764684913345 74862228446383323513685009)
                ·
                  refine ⟨56146671334787492635263757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74862228446383323513685009 56146671334787492635263757)
                  ·
                    refine ⟨21055001750545309738223909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56146671334787492635263757 21055001750545309738223909)
                    ·
                      refine ⟨3947812828227245575916983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21055001750545309738223909 3947812828227245575916983)
                      ·
                        rfl

theorem cell23_7688338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7688338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688338 prefixEnd_7688338 := by exact prefixLift 7688338
  have htrace : WordTrace (prefixWord ++ tailWord_7688338) baseStart_7688338 baseEnd_7688338 := by
    simpa [prefixWord, tailWord_7688338, baseEnd_7688338] using wordTrace_append hprefix tailTrace_7688338
  have hstable : (prefixWord ++ tailWord_7688338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688338).length < 2 ^ (prefixWord ++ tailWord_7688338).sum := by decide
  have hdescent : baseEnd_7688338 < baseStart_7688338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688359 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_7688359 : Nat := 118140960795 + 7688359 * 2 ^ 59
def prefixEnd_7688359 : Nat := 4983230072969 + 3 ^ 40 * 7688359 * 2
def baseEnd_7688359 : Nat := 3947823611320989993754387

theorem tailTrace_7688359 : CollatzResearch.WordTrace tailWord_7688359 prefixEnd_7688359 3947823611320989993754387 := by
  unfold tailWord_7688359
  simp only [CollatzResearch.WordTrace]
  refine ⟨280417489953395885023692131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186944993302263923349128087 280417489953395885023692131)
  ·
    refine ⟨420626234930093827535538197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280417489953395885023692131 420626234930093827535538197)
    ·
      refine ⟨19716854762348148165728353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 420626234930093827535538197 19716854762348148165728353)
      ·
        refine ⟨14787641071761111124296265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19716854762348148165728353 14787641071761111124296265)
        ·
          refine ⟨11090730803820833343222199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14787641071761111124296265 11090730803820833343222199)
          ·
            refine ⟨16636096205731250014833299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090730803820833343222199 16636096205731250014833299)
            ·
              refine ⟨24954144308596875022249949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16636096205731250014833299 24954144308596875022249949)
              ·
                refine ⟨9357804115723828133343731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24954144308596875022249949 9357804115723828133343731)
                ·
                  refine ⟨14036706173585742200015597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9357804115723828133343731 14036706173585742200015597)
                  ·
                    refine ⟨5263764815094653325005849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14036706173585742200015597 5263764815094653325005849)
                    ·
                      refine ⟨3947823611320989993754387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263764815094653325005849 3947823611320989993754387)
                      ·
                        rfl

theorem cell23_7688359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_7688359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688359 prefixEnd_7688359 := by exact prefixLift 7688359
  have htrace : WordTrace (prefixWord ++ tailWord_7688359) baseStart_7688359 baseEnd_7688359 := by
    simpa [prefixWord, tailWord_7688359, baseEnd_7688359] using wordTrace_append hprefix tailTrace_7688359
  have hstable : (prefixWord ++ tailWord_7688359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688359).length < 2 ^ (prefixWord ++ tailWord_7688359).sum := by decide
  have hdescent : baseEnd_7688359 < baseStart_7688359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688408 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 1, 7]
def baseStart_7688408 : Nat := 118140960795 + 7688408 * 2 ^ 59
def prefixEnd_7688408 : Nat := 4983230072969 + 3 ^ 40 * 7688408 * 2
def baseEnd_7688408 : Nat := 1315949590624353434013887

theorem tailTrace_7688408 : CollatzResearch.WordTrace tailWord_7688408 prefixEnd_7688408 1315949590624353434013887 := by
  unfold tailWord_7688408
  simp only [CollatzResearch.WordTrace]
  refine ⟨140209638565109183196112939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186946184753478910928150585 140209638565109183196112939)
  ·
    refine ⟨210314457847663774794169409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140209638565109183196112939 210314457847663774794169409)
    ·
      refine ⟨157735843385747831095627057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210314457847663774794169409 157735843385747831095627057)
      ·
        refine ⟨118301882539310873321720293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157735843385747831095627057 118301882539310873321720293)
        ·
          refine ⟨22181602976120788747822555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118301882539310873321720293 22181602976120788747822555)
          ·
            refine ⟨33272404464181183121733833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22181602976120788747822555 33272404464181183121733833)
            ·
              refine ⟨24954303348135887341300375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33272404464181183121733833 24954303348135887341300375)
              ·
                refine ⟨37431455022203831011950563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24954303348135887341300375 37431455022203831011950563)
                ·
                  refine ⟨56147182533305746517925845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37431455022203831011950563 56147182533305746517925845)
                  ·
                    refine ⟨1315949590624353434013887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56147182533305746517925845 1315949590624353434013887)
                    ·
                      rfl

theorem cell23_7688408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_7688408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688408 prefixEnd_7688408 := by exact prefixLift 7688408
  have htrace : WordTrace (prefixWord ++ tailWord_7688408) baseStart_7688408 baseEnd_7688408 := by
    simpa [prefixWord, tailWord_7688408, baseEnd_7688408] using wordTrace_append hprefix tailTrace_7688408
  have hstable : (prefixWord ++ tailWord_7688408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688408).length < 2 ^ (prefixWord ++ tailWord_7688408).sum := by decide
  have hdescent : baseEnd_7688408 < baseStart_7688408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688429 : List Nat := [1, 5, 1, 2, 3, 1, 3, 2, 5]
def baseStart_7688429 : Nat := 118140960795 + 7688429 * 2 ^ 59
def prefixEnd_7688429 : Nat := 4983230072969 + 3 ^ 40 * 7688429 * 2
def baseEnd_7688429 : Nat := 438651061662978302208785

theorem tailTrace_7688429 : CollatzResearch.WordTrace tailWord_7688429 prefixEnd_7688429 438651061662978302208785 := by
  unfold tailWord_7688429
  simp only [CollatzResearch.WordTrace]
  refine ⟨280420043063142286978740341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186946695375428191319160227 280420043063142286978740341)
  ·
    refine ⟨26289379037169589404256907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280420043063142286978740341 26289379037169589404256907)
    ·
      refine ⟨39434068555754384106385361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26289379037169589404256907 39434068555754384106385361)
      ·
        refine ⟨29575551416815788079789021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39434068555754384106385361 29575551416815788079789021)
        ·
          refine ⟨11090831781305920529920883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29575551416815788079789021 11090831781305920529920883)
          ·
            refine ⟨16636247671958880794881325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090831781305920529920883 16636247671958880794881325)
            ·
              refine ⟨6238592876984580298080497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16636247671958880794881325 6238592876984580298080497)
              ·
                refine ⟨4678944657738435223560373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6238592876984580298080497 4678944657738435223560373)
                ·
                  refine ⟨438651061662978302208785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4678944657738435223560373 438651061662978302208785)
                  ·
                    rfl

theorem cell23_7688429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_7688429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688429 prefixEnd_7688429 := by exact prefixLift 7688429
  have htrace : WordTrace (prefixWord ++ tailWord_7688429) baseStart_7688429 baseEnd_7688429 := by
    simpa [prefixWord, tailWord_7688429, baseEnd_7688429] using wordTrace_append hprefix tailTrace_7688429
  have hstable : (prefixWord ++ tailWord_7688429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688429).length < 2 ^ (prefixWord ++ tailWord_7688429).sum := by decide
  have hdescent : baseEnd_7688429 < baseStart_7688429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688445 : List Nat := [1, 4, 1, 1, 1, 1, 1, 5, 2, 4, 2]
def baseStart_7688445 : Nat := 118140960795 + 7688445 * 2 ^ 59
def prefixEnd_7688445 : Nat := 4983230072969 + 3 ^ 40 * 7688445 * 2
def baseEnd_7688445 : Nat := 3947867770657276657278991

theorem tailTrace_7688445 : CollatzResearch.WordTrace tailWord_7688445 prefixEnd_7688445 3947867770657276657278991 := by
  unfold tailWord_7688445
  simp only [CollatzResearch.WordTrace]
  refine ⟨280420626631084321711322789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186947084420722881140881859 280420626631084321711322789)
  ·
    refine ⟨52578867493328310320873023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280420626631084321711322789 52578867493328310320873023)
    ·
      refine ⟨78868301239992465481309535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52578867493328310320873023 78868301239992465481309535)
      ·
        refine ⟨118302451859988698221964303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78868301239992465481309535 118302451859988698221964303)
        ·
          refine ⟨177453677789983047332946455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118302451859988698221964303 177453677789983047332946455)
          ·
            refine ⟨266180516684974570999419683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177453677789983047332946455 266180516684974570999419683)
            ·
              refine ⟨399270775027461856499129525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266180516684974570999419683 399270775027461856499129525)
              ·
                refine ⟨37431635158824549046793393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399270775027461856499129525 37431635158824549046793393)
                ·
                  refine ⟨28073726369118411785095045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37431635158824549046793393 28073726369118411785095045)
                  ·
                    refine ⟨5263823694209702209705321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28073726369118411785095045 5263823694209702209705321)
                    ·
                      refine ⟨3947867770657276657278991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5263823694209702209705321 3947867770657276657278991)
                      ·
                        rfl

theorem cell23_7688445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_7688445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688445 prefixEnd_7688445 := by exact prefixLift 7688445
  have htrace : WordTrace (prefixWord ++ tailWord_7688445) baseStart_7688445 baseEnd_7688445 := by
    simpa [prefixWord, tailWord_7688445, baseEnd_7688445] using wordTrace_append hprefix tailTrace_7688445
  have hstable : (prefixWord ++ tailWord_7688445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688445).length < 2 ^ (prefixWord ++ tailWord_7688445).sum := by decide
  have hdescent : baseEnd_7688445 < baseStart_7688445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688448 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 3]
def baseStart_7688448 : Nat := 118140960795 + 7688448 * 2 ^ 59
def prefixEnd_7688448 : Nat := 4983230072969 + 3 ^ 40 * 7688448 * 2
def baseEnd_7688448 : Nat := 3947869311099240145541477

theorem tailTrace_7688448 : CollatzResearch.WordTrace tailWord_7688448 prefixEnd_7688448 3947869311099240145541477 := by
  unfold tailWord_7688448
  simp only [CollatzResearch.WordTrace]
  refine ⟨140210368025036726611840999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186947157366715635482454665 140210368025036726611840999)
  ·
    refine ⟨210315552037555089917761499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140210368025036726611840999 210315552037555089917761499)
    ·
      refine ⟨315473328056332634876642249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210315552037555089917761499 315473328056332634876642249)
      ·
        refine ⟨236604996042249476157481687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315473328056332634876642249 236604996042249476157481687)
        ·
          refine ⟨354907494063374214236222531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236604996042249476157481687 354907494063374214236222531)
          ·
            refine ⟨532361241095061321354333797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354907494063374214236222531 532361241095061321354333797)
            ·
              refine ⟨99817732705323997753937587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 532361241095061321354333797 99817732705323997753937587)
              ·
                refine ⟨149726599057985996630906381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99817732705323997753937587 149726599057985996630906381)
                ·
                  refine ⟨56147474646744748736589893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149726599057985996630906381 56147474646744748736589893)
                  ·
                    refine ⟨10527651496264640388110605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56147474646744748736589893 10527651496264640388110605)
                    ·
                      refine ⟨3947869311099240145541477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10527651496264640388110605 3947869311099240145541477)
                      ·
                        rfl

theorem cell23_7688448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_7688448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688448 prefixEnd_7688448 := by exact prefixLift 7688448
  have htrace : WordTrace (prefixWord ++ tailWord_7688448) baseStart_7688448 baseEnd_7688448 := by
    simpa [prefixWord, tailWord_7688448, baseEnd_7688448] using wordTrace_append hprefix tailTrace_7688448
  have hstable : (prefixWord ++ tailWord_7688448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688448).length < 2 ^ (prefixWord ++ tailWord_7688448).sum := by decide
  have hdescent : baseEnd_7688448 < baseStart_7688448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688458 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_7688458 : Nat := 118140960795 + 7688458 * 2 ^ 59
def prefixEnd_7688458 : Nat := 4983230072969 + 3 ^ 40 * 7688458 * 2
def baseEnd_7688458 : Nat := 3947874445905785106416431

theorem tailTrace_7688458 : CollatzResearch.WordTrace tailWord_7688458 prefixEnd_7688458 3947874445905785106416431 := by
  unfold tailWord_7688458
  simp only [CollatzResearch.WordTrace]
  refine ⟨70105275195009306232886507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186947400520024816621030685 70105275195009306232886507)
  ·
    refine ⟨105157912792513959349329761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70105275195009306232886507 105157912792513959349329761)
    ·
      refine ⟨78868434594385469511997321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105157912792513959349329761 78868434594385469511997321)
      ·
        refine ⟨59151325945789102133997991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78868434594385469511997321 59151325945789102133997991)
        ·
          refine ⟨88726988918683653200996987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59151325945789102133997991 88726988918683653200996987)
          ·
            refine ⟨133090483378025479801495481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88726988918683653200996987 133090483378025479801495481)
            ·
              refine ⟨99817862533519109851121611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133090483378025479801495481 99817862533519109851121611)
              ·
                refine ⟨149726793800278664776682417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99817862533519109851121611 149726793800278664776682417)
                ·
                  refine ⟨112295095350208998582511813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149726793800278664776682417 112295095350208998582511813)
                  ·
                    refine ⟨21055330378164187234220965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112295095350208998582511813 21055330378164187234220965)
                    ·
                      refine ⟨3947874445905785106416431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21055330378164187234220965 3947874445905785106416431)
                      ·
                        rfl

theorem cell23_7688458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_7688458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688458 prefixEnd_7688458 := by exact prefixLift 7688458
  have htrace : WordTrace (prefixWord ++ tailWord_7688458) baseStart_7688458 baseEnd_7688458 := by
    simpa [prefixWord, tailWord_7688458, baseEnd_7688458] using wordTrace_append hprefix tailTrace_7688458
  have hstable : (prefixWord ++ tailWord_7688458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688458).length < 2 ^ (prefixWord ++ tailWord_7688458).sum := by decide
  have hdescent : baseEnd_7688458 < baseStart_7688458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688465 : List Nat := [1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_7688465 : Nat := 118140960795 + 7688465 * 2 ^ 59
def prefixEnd_7688465 : Nat := 4983230072969 + 3 ^ 40 * 7688465 * 2
def baseEnd_7688465 : Nat := 3947878040270366579028899

theorem tailTrace_7688465 : CollatzResearch.WordTrace tailWord_7688465 prefixEnd_7688465 3947878040270366579028899 := by
  unfold tailWord_7688465
  simp only [CollatzResearch.WordTrace]
  refine ⟨280421356091011865127050849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186947570727341243418033899 280421356091011865127050849)
  ·
    refine ⟨210316017068258898845288137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280421356091011865127050849 210316017068258898845288137)
    ·
      refine ⟨157737012801194174133966103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210316017068258898845288137 157737012801194174133966103)
      ·
        refine ⟨236605519201791261200949155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157737012801194174133966103 236605519201791261200949155)
        ·
          refine ⟨354908278802686891801423733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236605519201791261200949155 354908278802686891801423733)
          ·
            refine ⟨33272651137751896106383475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 354908278802686891801423733 33272651137751896106383475)
            ·
              refine ⟨49908976706627844159575213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33272651137751896106383475 49908976706627844159575213)
              ·
                refine ⟨18715866264985441559840705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49908976706627844159575213 18715866264985441559840705)
                ·
                  refine ⟨14036899698739081169880529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18715866264985441559840705 14036899698739081169880529)
                  ·
                    refine ⟨10527674774054310877410397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14036899698739081169880529 10527674774054310877410397)
                    ·
                      refine ⟨3947878040270366579028899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10527674774054310877410397 3947878040270366579028899)
                      ·
                        rfl

theorem cell23_7688465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_7688465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688465 prefixEnd_7688465 := by exact prefixLift 7688465
  have htrace : WordTrace (prefixWord ++ tailWord_7688465) baseStart_7688465 baseEnd_7688465 := by
    simpa [prefixWord, tailWord_7688465, baseEnd_7688465] using wordTrace_append hprefix tailTrace_7688465
  have hstable : (prefixWord ++ tailWord_7688465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688465).length < 2 ^ (prefixWord ++ tailWord_7688465).sum := by decide
  have hdescent : baseEnd_7688465 < baseStart_7688465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688472 : List Nat := [2, 1, 2, 3, 1, 2, 2, 5, 1, 4]
def baseStart_7688472 : Nat := 118140960795 + 7688472 * 2 ^ 59
def prefixEnd_7688472 : Nat := 4983230072969 + 3 ^ 40 * 7688472 * 2
def baseEnd_7688472 : Nat := 1315960544878316017213789

theorem tailTrace_7688472 : CollatzResearch.WordTrace tailWord_7688472 prefixEnd_7688472 1315960544878316017213789 := by
  unfold tailWord_7688472
  simp only [CollatzResearch.WordTrace]
  refine ⟨140210805700993252661277835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186947740934657670215037113 140210805700993252661277835)
  ·
    refine ⟨210316208551489878991916753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140210805700993252661277835 210316208551489878991916753)
    ·
      refine ⟨157737156413617409243937565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210316208551489878991916753 157737156413617409243937565)
      ·
        refine ⟨59151433655106528466476587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157737156413617409243937565 59151433655106528466476587)
        ·
          refine ⟨88727150482659792699714881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59151433655106528466476587 88727150482659792699714881)
          ·
            refine ⟨66545362861994844524786161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88727150482659792699714881 66545362861994844524786161)
            ·
              refine ⟨49909022146496133393589621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66545362861994844524786161 49909022146496133393589621)
              ·
                refine ⟨4678970826234012505649027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49909022146496133393589621 4678970826234012505649027)
                ·
                  refine ⟨7018456239351018758473541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678970826234012505649027 7018456239351018758473541)
                  ·
                    refine ⟨1315960544878316017213789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7018456239351018758473541 1315960544878316017213789)
                    ·
                      rfl

theorem cell23_7688472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_7688472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688472 prefixEnd_7688472 := by exact prefixLift 7688472
  have htrace : WordTrace (prefixWord ++ tailWord_7688472) baseStart_7688472 baseEnd_7688472 := by
    simpa [prefixWord, tailWord_7688472, baseEnd_7688472] using wordTrace_append hprefix tailTrace_7688472
  have hstable : (prefixWord ++ tailWord_7688472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688472).length < 2 ^ (prefixWord ++ tailWord_7688472).sum := by decide
  have hdescent : baseEnd_7688472 < baseStart_7688472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688482 : List Nat := [3, 3, 1, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_7688482 : Nat := 118140960795 + 7688482 * 2 ^ 59
def prefixEnd_7688482 : Nat := 4983230072969 + 3 ^ 40 * 7688482 * 2
def baseEnd_7688482 : Nat := 3947886769441493012516321

theorem tailTrace_7688482 : CollatzResearch.WordTrace tailWord_7688482 prefixEnd_7688482 3947886769441493012516321 := by
  unfold tailWord_7688482
  simp only [CollatzResearch.WordTrace]
  refine ⟨70105494032987569257604925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186947984087966851353613133 70105494032987569257604925)
  ·
    refine ⟨26289560262370338471601847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70105494032987569257604925 26289560262370338471601847)
    ·
      refine ⟨39434340393555507707402771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26289560262370338471601847 39434340393555507707402771)
      ·
        refine ⟨59151510590333261561104157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39434340393555507707402771 59151510590333261561104157)
        ·
          refine ⟨22181816471374973085414059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59151510590333261561104157 22181816471374973085414059)
          ·
            refine ⟨33272724707062459628121089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22181816471374973085414059 33272724707062459628121089)
            ·
              refine ⟨24954543530296844721090817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33272724707062459628121089 24954543530296844721090817)
              ·
                refine ⟨18715907647722633540818113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24954543530296844721090817 18715907647722633540818113)
                ·
                  refine ⟨14036930735791975155613585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18715907647722633540818113 14036930735791975155613585)
                  ·
                    refine ⟨10527698051843981366710189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14036930735791975155613585 10527698051843981366710189)
                    ·
                      refine ⟨3947886769441493012516321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10527698051843981366710189 3947886769441493012516321)
                      ·
                        rfl

theorem cell23_7688482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_7688482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688482 prefixEnd_7688482 := by exact prefixLift 7688482
  have htrace : WordTrace (prefixWord ++ tailWord_7688482) baseStart_7688482 baseEnd_7688482 := by
    simpa [prefixWord, tailWord_7688482, baseEnd_7688482] using wordTrace_append hprefix tailTrace_7688482
  have hstable : (prefixWord ++ tailWord_7688482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688482).length < 2 ^ (prefixWord ++ tailWord_7688482).sum := by decide
  have hdescent : baseEnd_7688482 < baseStart_7688482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688508 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_7688508 : Nat := 118140960795 + 7688508 * 2 ^ 59
def prefixEnd_7688508 : Nat := 4983230072969 + 3 ^ 40 * 7688508 * 2
def baseEnd_7688508 : Nat := 3947900119938509910791201

theorem tailTrace_7688508 : CollatzResearch.WordTrace tailWord_7688508 prefixEnd_7688508 3947900119938509910791201 := by
  unfold tailWord_7688508
  simp only [CollatzResearch.WordTrace]
  refine ⟨140211462214928041735433089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186948616286570722313910785 140211462214928041735433089)
  ·
    refine ⟨105158596661196031301574817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140211462214928041735433089 105158596661196031301574817)
    ·
      refine ⟨78868947495897023476181113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105158596661196031301574817 78868947495897023476181113)
      ·
        refine ⟨59151710621922767607135835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78868947495897023476181113 59151710621922767607135835)
        ·
          refine ⟨88727565932884151410703753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59151710621922767607135835 88727565932884151410703753)
          ·
            refine ⟨66545674449663113558027815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88727565932884151410703753 66545674449663113558027815)
            ·
              refine ⟨99818511674494670337041723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66545674449663113558027815 99818511674494670337041723)
              ·
                refine ⟨149727767511742005505562585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99818511674494670337041723 149727767511742005505562585)
                ·
                  refine ⟨112295825633806504129171939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149727767511742005505562585 112295825633806504129171939)
                  ·
                    refine ⟨168443738450709756193757909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112295825633806504129171939 168443738450709756193757909)
                    ·
                      refine ⟨3947900119938509910791201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168443738450709756193757909 3947900119938509910791201)
                      ·
                        rfl

theorem cell23_7688508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_7688508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688508 prefixEnd_7688508 := by exact prefixLift 7688508
  have htrace : WordTrace (prefixWord ++ tailWord_7688508) baseStart_7688508 baseEnd_7688508 := by
    simpa [prefixWord, tailWord_7688508, baseEnd_7688508] using wordTrace_append hprefix tailTrace_7688508
  have hstable : (prefixWord ++ tailWord_7688508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688508).length < 2 ^ (prefixWord ++ tailWord_7688508).sum := by decide
  have hdescent : baseEnd_7688508 < baseStart_7688508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688516 : List Nat := [2, 3, 4, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7688516 : Nat := 118140960795 + 7688516 * 2 ^ 59
def prefixEnd_7688516 : Nat := 4983230072969 + 3 ^ 40 * 7688516 * 2
def baseEnd_7688516 : Nat := 3947904227783745879491165

theorem tailTrace_7688516 : CollatzResearch.WordTrace tailWord_7688516 prefixEnd_7688516 3947904227783745879491165 := by
  unfold tailWord_7688516
  simp only [CollatzResearch.WordTrace]
  refine ⟨140211608106913550418578701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186948810809218067224771601 140211608106913550418578701)
  ·
    refine ⟨52579353040092581406967013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140211608106913550418578701 52579353040092581406967013)
    ·
      refine ⟨9858628695017359013806315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52579353040092581406967013 9858628695017359013806315)
      ·
        refine ⟨14787943042526038520709473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9858628695017359013806315 14787943042526038520709473)
        ·
          refine ⟨11090957281894528890532105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14787943042526038520709473 11090957281894528890532105)
          ·
            refine ⟨8318217961420896667899079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11090957281894528890532105 8318217961420896667899079)
            ·
              refine ⟨12477326942131345001848619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318217961420896667899079 12477326942131345001848619)
              ·
                refine ⟨18715990413197017502772929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12477326942131345001848619 18715990413197017502772929)
                ·
                  refine ⟨14036992809897763127079697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18715990413197017502772929 14036992809897763127079697)
                  ·
                    refine ⟨10527744607423322345309773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14036992809897763127079697 10527744607423322345309773)
                    ·
                      refine ⟨3947904227783745879491165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10527744607423322345309773 3947904227783745879491165)
                      ·
                        rfl

theorem cell23_7688516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7688516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688516 prefixEnd_7688516 := by exact prefixLift 7688516
  have htrace : WordTrace (prefixWord ++ tailWord_7688516) baseStart_7688516 baseEnd_7688516 := by
    simpa [prefixWord, tailWord_7688516, baseEnd_7688516] using wordTrace_append hprefix tailTrace_7688516
  have hstable : (prefixWord ++ tailWord_7688516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688516).length < 2 ^ (prefixWord ++ tailWord_7688516).sum := by decide
  have hdescent : baseEnd_7688516 < baseStart_7688516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688529 : List Nat := [1, 2, 2, 1, 4, 2, 1, 5, 1, 1, 3]
def baseStart_7688529 : Nat := 118140960795 + 7688529 * 2 ^ 59
def prefixEnd_7688529 : Nat := 4983230072969 + 3 ^ 40 * 7688529 * 2
def baseEnd_7688529 : Nat := 3947910903032254328628605

theorem tailTrace_7688529 : CollatzResearch.WordTrace tailWord_7688529 prefixEnd_7688529 3947910903032254328628605 := by
  unfold tailWord_7688529
  simp only [CollatzResearch.WordTrace]
  refine ⟨280423690362780004057380641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186949126908520002704920427 280423690362780004057380641)
  ·
    refine ⟨210317767772085003043035481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280423690362780004057380641 210317767772085003043035481)
    ·
      refine ⟨157738325829063752282276611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210317767772085003043035481 157738325829063752282276611)
      ·
        refine ⟨236607488743595628423414917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157738325829063752282276611 236607488743595628423414917)
        ·
          refine ⟨44363904139424180329390297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236607488743595628423414917 44363904139424180329390297)
          ·
            refine ⟨33272928104568135247042723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44363904139424180329390297 33272928104568135247042723)
            ·
              refine ⟨49909392156852202870564085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33272928104568135247042723 49909392156852202870564085)
              ·
                refine ⟨4679005514704894019115383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49909392156852202870564085 4679005514704894019115383)
                ·
                  refine ⟨7018508272057341028673075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679005514704894019115383 7018508272057341028673075)
                  ·
                    refine ⟨10527762408086011543009613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7018508272057341028673075 10527762408086011543009613)
                    ·
                      refine ⟨3947910903032254328628605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10527762408086011543009613 3947910903032254328628605)
                      ·
                        rfl

theorem cell23_7688529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 1, 1, 3].length) (baseStart_7688529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688529 prefixEnd_7688529 := by exact prefixLift 7688529
  have htrace : WordTrace (prefixWord ++ tailWord_7688529) baseStart_7688529 baseEnd_7688529 := by
    simpa [prefixWord, tailWord_7688529, baseEnd_7688529] using wordTrace_append hprefix tailTrace_7688529
  have hstable : (prefixWord ++ tailWord_7688529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688529).length < 2 ^ (prefixWord ++ tailWord_7688529).sum := by decide
  have hdescent : baseEnd_7688529 < baseStart_7688529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688532 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_7688532 : Nat := 118140960795 + 7688532 * 2 ^ 59
def prefixEnd_7688532 : Nat := 4983230072969 + 3 ^ 40 * 7688532 * 2
def baseEnd_7688532 : Nat := 1315970814491405938963697

theorem tailTrace_7688532 : CollatzResearch.WordTrace tailWord_7688532 prefixEnd_7688532 1315970814491405938963697 := by
  unfold tailWord_7688532
  simp only [CollatzResearch.WordTrace]
  refine ⟨140211899890884567784869925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186949199854512757046493233 140211899890884567784869925)
  ·
    refine ⟨26289731229540856459663111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140211899890884567784869925 26289731229540856459663111)
    ·
      refine ⟨39434596844311284689494667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26289731229540856459663111 39434596844311284689494667)
      ·
        refine ⟨59151895266466927034242001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39434596844311284689494667 59151895266466927034242001)
        ·
          refine ⟨44363921449850195275681501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59151895266466927034242001 44363921449850195275681501)
          ·
            refine ⟨16636470543693823228380563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44363921449850195275681501 16636470543693823228380563)
            ·
              refine ⟨24954705815540734842570845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16636470543693823228380563 24954705815540734842570845)
              ·
                refine ⟨9358014680827775565964067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24954705815540734842570845 9358014680827775565964067)
                ·
                  refine ⟨14037022021241663348946101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9358014680827775565964067 14037022021241663348946101)
                  ·
                    refine ⟨1315970814491405938963697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14037022021241663348946101 1315970814491405938963697)
                    ·
                      rfl

theorem cell23_7688532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_7688532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688532 prefixEnd_7688532 := by exact prefixLift 7688532
  have htrace : WordTrace (prefixWord ++ tailWord_7688532) baseStart_7688532 baseEnd_7688532 := by
    simpa [prefixWord, tailWord_7688532, baseEnd_7688532] using wordTrace_append hprefix tailTrace_7688532
  have hstable : (prefixWord ++ tailWord_7688532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688532).length < 2 ^ (prefixWord ++ tailWord_7688532).sum := by decide
  have hdescent : baseEnd_7688532 < baseStart_7688532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688546 : List Nat := [3, 3, 2, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_7688546 : Nat := 118140960795 + 7688546 * 2 ^ 59
def prefixEnd_7688546 : Nat := 4983230072969 + 3 ^ 40 * 7688546 * 2
def baseEnd_7688546 : Nat := 3947919632203380762116027

theorem tailTrace_7688546 : CollatzResearch.WordTrace tailWord_7688546 prefixEnd_7688546 3947919632203380762116027 := by
  unfold tailWord_7688546
  simp only [CollatzResearch.WordTrace]
  refine ⟨70106077600929603990187373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186949540269145610640499661 70106077600929603990187373)
  ·
    refine ⟨26289779100348601496320265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70106077600929603990187373 26289779100348601496320265)
    ·
      refine ⟨19717334325261451122240199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26289779100348601496320265 19717334325261451122240199)
      ·
        refine ⟨29576001487892176683360299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19717334325261451122240199 29576001487892176683360299)
        ·
          refine ⟨44364002231838265025040449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29576001487892176683360299 44364002231838265025040449)
          ·
            refine ⟨33273001673878698768780337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44364002231838265025040449 33273001673878698768780337)
            ·
              refine ⟨24954751255409024076585253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33273001673878698768780337 24954751255409024076585253)
              ·
                refine ⟨4679015860389192014359735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24954751255409024076585253 4679015860389192014359735)
                ·
                  refine ⟨7018523790583788021539603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679015860389192014359735 7018523790583788021539603)
                  ·
                    refine ⟨10527785685875682032309405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7018523790583788021539603 10527785685875682032309405)
                    ·
                      refine ⟨3947919632203380762116027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10527785685875682032309405 3947919632203380762116027)
                      ·
                        rfl

theorem cell23_7688546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_7688546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688546 prefixEnd_7688546 := by exact prefixLift 7688546
  have htrace : WordTrace (prefixWord ++ tailWord_7688546) baseStart_7688546 baseEnd_7688546 := by
    simpa [prefixWord, tailWord_7688546, baseEnd_7688546] using wordTrace_append hprefix tailTrace_7688546
  have hstable : (prefixWord ++ tailWord_7688546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688546).length < 2 ^ (prefixWord ++ tailWord_7688546).sum := by decide
  have hdescent : baseEnd_7688546 < baseStart_7688546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688562 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 1, 6]
def baseStart_7688562 : Nat := 118140960795 + 7688562 * 2 ^ 59
def prefixEnd_7688562 : Nat := 4983230072969 + 3 ^ 40 * 7688562 * 2
def baseEnd_7688562 : Nat := 1315975949297950899838651

theorem tailTrace_7688562 : CollatzResearch.WordTrace tailWord_7688562 prefixEnd_7688562 1315975949297950899838651 := by
  unfold tailWord_7688562
  simp only [CollatzResearch.WordTrace]
  refine ⟨70106223492915112673332985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186949929314440300462221293 70106223492915112673332985)
  ·
    refine ⟨52579667619686334504999739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70106223492915112673332985 52579667619686334504999739)
    ·
      refine ⟨78869501429529501757499609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52579667619686334504999739 78869501429529501757499609)
      ·
        refine ⟨59152126072147126318124707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78869501429529501757499609 59152126072147126318124707)
        ·
          refine ⟨88728189108220689477187061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59152126072147126318124707 88728189108220689477187061)
          ·
            refine ⟨8318267728895689638486287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88728189108220689477187061 8318267728895689638486287)
            ·
              refine ⟨12477401593343534457729431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318267728895689638486287 12477401593343534457729431)
              ·
                refine ⟨18716102390015301686594147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12477401593343534457729431 18716102390015301686594147)
                ·
                  refine ⟨28074153585022952529891221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18716102390015301686594147 28074153585022952529891221)
                  ·
                    refine ⟨1315975949297950899838651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28074153585022952529891221 1315975949297950899838651)
                    ·
                      rfl

theorem cell23_7688562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_7688562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688562 prefixEnd_7688562 := by exact prefixLift 7688562
  have htrace : WordTrace (prefixWord ++ tailWord_7688562) baseStart_7688562 baseEnd_7688562 := by
    simpa [prefixWord, tailWord_7688562, baseEnd_7688562] using wordTrace_append hprefix tailTrace_7688562
  have hstable : (prefixWord ++ tailWord_7688562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688562).length < 2 ^ (prefixWord ++ tailWord_7688562).sum := by decide
  have hdescent : baseEnd_7688562 < baseStart_7688562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688566 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_7688566 : Nat := 118140960795 + 7688566 * 2 ^ 59
def prefixEnd_7688566 : Nat := 4983230072969 + 3 ^ 40 * 7688566 * 2
def baseEnd_7688566 : Nat := 1315976633938823561288645

theorem tailTrace_7688566 : CollatzResearch.WordTrace tailWord_7688566 prefixEnd_7688566 1315976633938823561288645 := by
  unfold tailWord_7688566
  simp only [CollatzResearch.WordTrace]
  refine ⟨17526564991477872461029847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186950026575763972917651701 17526564991477872461029847)
  ·
    refine ⟨26289847487216808691544771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17526564991477872461029847 26289847487216808691544771)
    ·
      refine ⟨39434771230825213037317157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26289847487216808691544771 39434771230825213037317157)
      ·
        refine ⟨7394019605779727444496967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39434771230825213037317157 7394019605779727444496967)
        ·
          refine ⟨11091029408669591166745451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7394019605779727444496967 11091029408669591166745451)
          ·
            refine ⟨16636544113004386750118177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11091029408669591166745451 16636544113004386750118177)
            ·
              refine ⟨12477408084753290062588633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16636544113004386750118177 12477408084753290062588633)
              ·
                refine ⟨9358056063564967546941475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12477408084753290062588633 9358056063564967546941475)
                ·
                  refine ⟨14037084095347451320412213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9358056063564967546941475 14037084095347451320412213)
                  ·
                    refine ⟨1315976633938823561288645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14037084095347451320412213 1315976633938823561288645)
                    ·
                      rfl

theorem cell23_7688566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_7688566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688566 prefixEnd_7688566 := by exact prefixLift 7688566
  have htrace : WordTrace (prefixWord ++ tailWord_7688566) baseStart_7688566 baseEnd_7688566 := by
    simpa [prefixWord, tailWord_7688566, baseEnd_7688566] using wordTrace_append hprefix tailTrace_7688566
  have hstable : (prefixWord ++ tailWord_7688566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688566).length < 2 ^ (prefixWord ++ tailWord_7688566).sum := by decide
  have hdescent : baseEnd_7688566 < baseStart_7688566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688645 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_7688645 : Nat := 118140960795 + 7688645 * 2 ^ 59
def prefixEnd_7688645 : Nat := 4983230072969 + 3 ^ 40 * 7688645 * 2
def baseEnd_7688645 : Nat := 3947970466788175874778071

theorem tailTrace_7688645 : CollatzResearch.WordTrace tailWord_7688645 prefixEnd_7688645 3947970466788175874778071 := by
  unfold tailWord_7688645
  simp only [CollatzResearch.WordTrace]
  refine ⟨280427921230359755868603389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186951947486906503912402259 280427921230359755868603389)
  ·
    refine ⟨105160470461384908450726271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280427921230359755868603389 105160470461384908450726271)
    ·
      refine ⟨157740705692077362676089407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105160470461384908450726271 157740705692077362676089407)
      ·
        refine ⟨236611058538116044014134111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157740705692077362676089407 236611058538116044014134111)
        ·
          refine ⟨354916587807174066021201167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236611058538116044014134111 354916587807174066021201167)
          ·
            refine ⟨532374881710761099031801751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354916587807174066021201167 532374881710761099031801751)
            ·
              refine ⟨798562322566141648547702627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532374881710761099031801751 798562322566141648547702627)
              ·
                refine ⟨1197843483849212472821553941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798562322566141648547702627 1197843483849212472821553941)
                ·
                  refine ⟨56148913305431834663510341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1197843483849212472821553941 56148913305431834663510341)
                  ·
                    refine ⟨10527921244768468999408189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56148913305431834663510341 10527921244768468999408189)
                    ·
                      refine ⟨3947970466788175874778071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10527921244768468999408189 3947970466788175874778071)
                      ·
                        rfl

theorem cell23_7688645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_7688645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688645 prefixEnd_7688645 := by exact prefixLift 7688645
  have htrace : WordTrace (prefixWord ++ tailWord_7688645) baseStart_7688645 baseEnd_7688645 := by
    simpa [prefixWord, tailWord_7688645, baseEnd_7688645] using wordTrace_append hprefix tailTrace_7688645
  have hstable : (prefixWord ++ tailWord_7688645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688645).length < 2 ^ (prefixWord ++ tailWord_7688645).sum := by decide
  have hdescent : baseEnd_7688645 < baseStart_7688645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688655 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_7688655 : Nat := 118140960795 + 7688655 * 2 ^ 59
def prefixEnd_7688655 : Nat := 4983230072969 + 3 ^ 40 * 7688655 * 2
def baseEnd_7688655 : Nat := 3947975601594720835653025

theorem tailTrace_7688655 : CollatzResearch.WordTrace tailWord_7688655 prefixEnd_7688655 3947975601594720835653025 := by
  unfold tailWord_7688655
  simp only [CollatzResearch.WordTrace]
  refine ⟨280428285960323527576467419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186952190640215685050978279 280428285960323527576467419)
  ·
    refine ⟨420642428940485291364701129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280428285960323527576467419 420642428940485291364701129)
    ·
      refine ⟨315481821705363968523525847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420642428940485291364701129 315481821705363968523525847)
      ·
        refine ⟨473222732558045952785288771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315481821705363968523525847 473222732558045952785288771)
        ·
          refine ⟨709834098837068929177933157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473222732558045952785288771 709834098837068929177933157)
          ·
            refine ⟨133093893531950424220862467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 709834098837068929177933157 133093893531950424220862467)
            ·
              refine ⟨199640840297925636331293701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133093893531950424220862467 199640840297925636331293701)
              ·
                refine ⟨37432657555861056812117569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199640840297925636331293701 37432657555861056812117569)
                ·
                  refine ⟨28074493166895792609088177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37432657555861056812117569 28074493166895792609088177)
                  ·
                    refine ⟨21055869875171844456816133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28074493166895792609088177 21055869875171844456816133)
                    ·
                      refine ⟨3947975601594720835653025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21055869875171844456816133 3947975601594720835653025)
                      ·
                        rfl

theorem cell23_7688655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_7688655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688655 prefixEnd_7688655 := by exact prefixLift 7688655
  have htrace : WordTrace (prefixWord ++ tailWord_7688655) baseStart_7688655 baseEnd_7688655 := by
    simpa [prefixWord, tailWord_7688655, baseEnd_7688655] using wordTrace_append hprefix tailTrace_7688655
  have hstable : (prefixWord ++ tailWord_7688655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688655).length < 2 ^ (prefixWord ++ tailWord_7688655).sum := by decide
  have hdescent : baseEnd_7688655 < baseStart_7688655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688665 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 7]
def baseStart_7688665 : Nat := 118140960795 + 7688665 * 2 ^ 59
def prefixEnd_7688665 : Nat := 4983230072969 + 3 ^ 40 * 7688665 * 2
def baseEnd_7688665 : Nat := 438664526266807310725331

theorem tailTrace_7688665 : CollatzResearch.WordTrace tailWord_7688665 prefixEnd_7688665 438664526266807310725331 := by
  unfold tailWord_7688665
  simp only [CollatzResearch.WordTrace]
  refine ⟨280428650690287299284331449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186952433793524866189554299 280428650690287299284331449)
  ·
    refine ⟨210321488017715474463248587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280428650690287299284331449 210321488017715474463248587)
    ·
      refine ⟨315482232026573211694872881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210321488017715474463248587 315482232026573211694872881)
      ·
        refine ⟨236611674019929908771154661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315482232026573211694872881 236611674019929908771154661)
        ·
          refine ⟨44364688878736857894591499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236611674019929908771154661 44364688878736857894591499)
          ·
            refine ⟨66547033318105286841887249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44364688878736857894591499 66547033318105286841887249)
            ·
              refine ⟨49910274988578965131415437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66547033318105286841887249 49910274988578965131415437)
              ·
                refine ⟨18716353120717111924280789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49910274988578965131415437 18716353120717111924280789)
                ·
                  refine ⟨438664526266807310725331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18716353120717111924280789 438664526266807310725331)
                  ·
                    rfl

theorem cell23_7688665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 7].length) (baseStart_7688665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688665 prefixEnd_7688665 := by exact prefixLift 7688665
  have htrace : WordTrace (prefixWord ++ tailWord_7688665) baseStart_7688665 baseEnd_7688665 := by
    simpa [prefixWord, tailWord_7688665, baseEnd_7688665] using wordTrace_append hprefix tailTrace_7688665
  have hstable : (prefixWord ++ tailWord_7688665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688665).length < 2 ^ (prefixWord ++ tailWord_7688665).sum := by decide
  have hdescent : baseEnd_7688665 < baseStart_7688665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688682 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 7]
def baseStart_7688682 : Nat := 118140960795 + 7688682 * 2 ^ 59
def prefixEnd_7688682 : Nat := 4983230072969 + 3 ^ 40 * 7688682 * 2
def baseEnd_7688682 : Nat := 438665496174710247779489

theorem tailTrace_7688682 : CollatzResearch.WordTrace tailWord_7688682 prefixEnd_7688682 438665496174710247779489 := by
  unfold tailWord_7688682
  simp only [CollatzResearch.WordTrace]
  refine ⟨70107317682806427796925075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186952847154150474125133533 70107317682806427796925075)
  ·
    refine ⟨105160976524209641695387613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70107317682806427796925075 105160976524209641695387613)
    ·
      refine ⟨39435366196578615635770355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105160976524209641695387613 39435366196578615635770355)
      ·
        refine ⟨59153049294867923453655533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39435366196578615635770355 59153049294867923453655533)
        ·
          refine ⟨22182393485575471295120825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59153049294867923453655533 22182393485575471295120825)
          ·
            refine ⟨16636795114181603471340619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22182393485575471295120825 16636795114181603471340619)
            ·
              refine ⟨24955192671272405207010929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16636795114181603471340619 24955192671272405207010929)
              ·
                refine ⟨18716394503454303905258197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24955192671272405207010929 18716394503454303905258197)
                ·
                  refine ⟨438665496174710247779489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18716394503454303905258197 438665496174710247779489)
                  ·
                    rfl

theorem cell23_7688682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 7].length) (baseStart_7688682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688682 prefixEnd_7688682 := by exact prefixLift 7688682
  have htrace : WordTrace (prefixWord ++ tailWord_7688682) baseStart_7688682 baseEnd_7688682 := by
    simpa [prefixWord, tailWord_7688682, baseEnd_7688682] using wordTrace_append hprefix tailTrace_7688682
  have hstable : (prefixWord ++ tailWord_7688682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688682).length < 2 ^ (prefixWord ++ tailWord_7688682).sum := by decide
  have hdescent : baseEnd_7688682 < baseStart_7688682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688732 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_7688732 : Nat := 118140960795 + 7688732 * 2 ^ 59
def prefixEnd_7688732 : Nat := 4983230072969 + 3 ^ 40 * 7688732 * 2
def baseEnd_7688732 : Nat := 3948015139605117034390171

theorem tailTrace_7688732 : CollatzResearch.WordTrace tailWord_7688732 prefixEnd_7688732 3948015139605117034390171 := by
  unfold tailWord_7688732
  simp only [CollatzResearch.WordTrace]
  refine ⟨140215547190522284863510225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186954062920696379818013633 140215547190522284863510225)
  ·
    refine ⟨105161660392891713647632669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140215547190522284863510225 105161660392891713647632669)
    ·
      refine ⟨39435622647334392617862251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105161660392891713647632669 39435622647334392617862251)
      ·
        refine ⟨59153433971001588926793377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39435622647334392617862251 59153433971001588926793377)
        ·
          refine ⟨44365075478251191695095033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59153433971001588926793377 44365075478251191695095033)
          ·
            refine ⟨33273806608688393771321275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44365075478251191695095033 33273806608688393771321275)
            ·
              refine ⟨49910709913032590656981913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33273806608688393771321275 49910709913032590656981913)
              ·
                refine ⟨37433032434774442992736435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49910709913032590656981913 37433032434774442992736435)
                ·
                  refine ⟨56149548652161664489104653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37433032434774442992736435 56149548652161664489104653)
                  ·
                    refine ⟨21056080744560624183414245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56149548652161664489104653 21056080744560624183414245)
                    ·
                      refine ⟨3948015139605117034390171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21056080744560624183414245 3948015139605117034390171)
                      ·
                        rfl

theorem cell23_7688732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_7688732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688732 prefixEnd_7688732 := by exact prefixLift 7688732
  have htrace : WordTrace (prefixWord ++ tailWord_7688732) baseStart_7688732 baseEnd_7688732 := by
    simpa [prefixWord, tailWord_7688732, baseEnd_7688732] using wordTrace_append hprefix tailTrace_7688732
  have hstable : (prefixWord ++ tailWord_7688732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688732).length < 2 ^ (prefixWord ++ tailWord_7688732).sum := by decide
  have hdescent : baseEnd_7688732 < baseStart_7688732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688752 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 3]
def baseStart_7688752 : Nat := 118140960795 + 7688752 * 2 ^ 59
def prefixEnd_7688752 : Nat := 4983230072969 + 3 ^ 40 * 7688752 * 2
def baseEnd_7688752 : Nat := 3948025409218206956140079

theorem tailTrace_7688752 : CollatzResearch.WordTrace tailWord_7688752 prefixEnd_7688752 3948025409218206956140079 := by
  unfold tailWord_7688752
  simp only [CollatzResearch.WordTrace]
  refine ⟨140215911920486056571374255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186954549227314742095165673 140215911920486056571374255)
  ·
    refine ⟨210323867880729084857061383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140215911920486056571374255 210323867880729084857061383)
    ·
      refine ⟨315485801821093627285592075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210323867880729084857061383 315485801821093627285592075)
      ·
        refine ⟨473228702731640440928388113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315485801821093627285592075 473228702731640440928388113)
        ·
          refine ⟨354921527048730330696291085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473228702731640440928388113 354921527048730330696291085)
          ·
            refine ⟨133095572643273874011109157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354921527048730330696291085 133095572643273874011109157)
            ·
              refine ⟨24955419870613851377082967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133095572643273874011109157 24955419870613851377082967)
              ·
                refine ⟨37433129805920777065624451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24955419870613851377082967 37433129805920777065624451)
                ·
                  refine ⟨56149694708881165598436677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37433129805920777065624451 56149694708881165598436677)
                  ·
                    refine ⟨10528067757915218549706877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56149694708881165598436677 10528067757915218549706877)
                    ·
                      refine ⟨3948025409218206956140079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10528067757915218549706877 3948025409218206956140079)
                      ·
                        rfl

theorem cell23_7688752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_7688752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688752 prefixEnd_7688752 := by exact prefixLift 7688752
  have htrace : WordTrace (prefixWord ++ tailWord_7688752) baseStart_7688752 baseEnd_7688752 := by
    simpa [prefixWord, tailWord_7688752, baseEnd_7688752] using wordTrace_append hprefix tailTrace_7688752
  have hstable : (prefixWord ++ tailWord_7688752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688752).length < 2 ^ (prefixWord ++ tailWord_7688752).sum := by decide
  have hdescent : baseEnd_7688752 < baseStart_7688752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688755 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 10]
def baseStart_7688755 : Nat := 118140960795 + 7688755 * 2 ^ 59
def prefixEnd_7688755 : Nat := 4983230072969 + 3 ^ 40 * 7688755 * 2
def baseEnd_7688755 : Nat := 438669661073352271600285

theorem tailTrace_7688755 : CollatzResearch.WordTrace tailWord_7688755 prefixEnd_7688755 438669661073352271600285 := by
  unfold tailWord_7688755
  simp only [CollatzResearch.WordTrace]
  refine ⟨280431933259961244655107719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186954622173307496436738479 280431933259961244655107719)
  ·
    refine ⟨420647899889941866982661579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280431933259961244655107719 420647899889941866982661579)
    ·
      refine ⟨630971849834912800473992369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420647899889941866982661579 630971849834912800473992369)
      ·
        refine ⟨473228887376184600355494277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630971849834912800473992369 473228887376184600355494277)
        ·
          refine ⟨88730416383034612566655177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473228887376184600355494277 88730416383034612566655177)
          ·
            refine ⟨66547812287275959424991383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88730416383034612566655177 66547812287275959424991383)
            ·
              refine ⟨99821718430913939137487075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66547812287275959424991383 99821718430913939137487075)
              ·
                refine ⟨149732577646370908706230613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99821718430913939137487075 149732577646370908706230613)
                ·
                  refine ⟨438669661073352271600285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149732577646370908706230613 438669661073352271600285)
                  ·
                    rfl

theorem cell23_7688755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 10].length) (baseStart_7688755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688755 prefixEnd_7688755 := by exact prefixLift 7688755
  have htrace : WordTrace (prefixWord ++ tailWord_7688755) baseStart_7688755 baseEnd_7688755 := by
    simpa [prefixWord, tailWord_7688755, baseEnd_7688755] using wordTrace_append hprefix tailTrace_7688755
  have hstable : (prefixWord ++ tailWord_7688755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688755).length < 2 ^ (prefixWord ++ tailWord_7688755).sum := by decide
  have hdescent : baseEnd_7688755 < baseStart_7688755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688769 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_7688769 : Nat := 118140960795 + 7688769 * 2 ^ 59
def prefixEnd_7688769 : Nat := 4983230072969 + 3 ^ 40 * 7688769 * 2
def baseEnd_7688769 : Nat := 3948034138389333389627501

theorem tailTrace_7688769 : CollatzResearch.WordTrace tailWord_7688769 prefixEnd_7688769 3948034138389333389627501 := by
  unfold tailWord_7688769
  simp only [CollatzResearch.WordTrace]
  refine ⟨280432443881910525046117361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186954962587940350030744907 280432443881910525046117361)
  ·
    refine ⟨210324332911432893784588021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280432443881910525046117361 210324332911432893784588021)
    ·
      refine ⟨19717906210446833792305127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210324332911432893784588021 19717906210446833792305127)
      ·
        refine ⟨29576859315670250688457691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19717906210446833792305127 29576859315670250688457691)
        ·
          refine ⟨44365288973505376032686537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29576859315670250688457691 44365288973505376032686537)
          ·
            refine ⟨33273966730129032024514903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44365288973505376032686537 33273966730129032024514903)
            ·
              refine ⟨49910950095193548036772355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33273966730129032024514903 49910950095193548036772355)
              ·
                refine ⟨74866425142790322055158533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49910950095193548036772355 74866425142790322055158533)
                ·
                  refine ⟨14037454714273185385342225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74866425142790322055158533 14037454714273185385342225)
                  ·
                    refine ⟨10528091035704889039006669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14037454714273185385342225 10528091035704889039006669)
                    ·
                      refine ⟨3948034138389333389627501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10528091035704889039006669 3948034138389333389627501)
                      ·
                        rfl

theorem cell23_7688769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_7688769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688769 prefixEnd_7688769 := by exact prefixLift 7688769
  have htrace : WordTrace (prefixWord ++ tailWord_7688769) baseStart_7688769 baseEnd_7688769 := by
    simpa [prefixWord, tailWord_7688769, baseEnd_7688769] using wordTrace_append hprefix tailTrace_7688769
  have hstable : (prefixWord ++ tailWord_7688769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688769).length < 2 ^ (prefixWord ++ tailWord_7688769).sum := by decide
  have hdescent : baseEnd_7688769 < baseStart_7688769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688789 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 6]
def baseStart_7688789 : Nat := 118140960795 + 7688789 * 2 ^ 59
def prefixEnd_7688789 : Nat := 4983230072969 + 3 ^ 40 * 7688789 * 2
def baseEnd_7688789 : Nat := 438671600889158145708601

theorem tailTrace_7688789 : CollatzResearch.WordTrace tailWord_7688789 prefixEnd_7688789 438671600889158145708601 := by
  unfold tailWord_7688789
  simp only [CollatzResearch.WordTrace]
  refine ⟨280433173341838068461845421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186955448894558712307896947 280433173341838068461845421)
  ·
    refine ⟨105162440003189275673192033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280433173341838068461845421 105162440003189275673192033)
    ·
      refine ⟨78871830002391956754894025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105162440003189275673192033 78871830002391956754894025)
      ·
        refine ⟨59153872501793967566170519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78871830002391956754894025 59153872501793967566170519)
        ·
          refine ⟨88730808752690951349255779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59153872501793967566170519 88730808752690951349255779)
          ·
            refine ⟨133096213129036427023883669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88730808752690951349255779 133096213129036427023883669)
            ·
              refine ⟨6238884990423582516744547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133096213129036427023883669 6238884990423582516744547)
              ·
                refine ⟨9358327485635373775116821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238884990423582516744547 9358327485635373775116821)
                ·
                  refine ⟨438671600889158145708601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9358327485635373775116821 438671600889158145708601)
                  ·
                    rfl

theorem cell23_7688789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_7688789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688789 prefixEnd_7688789 := by exact prefixLift 7688789
  have htrace : WordTrace (prefixWord ++ tailWord_7688789) baseStart_7688789 baseEnd_7688789 := by
    simpa [prefixWord, tailWord_7688789, baseEnd_7688789] using wordTrace_append hprefix tailTrace_7688789
  have hstable : (prefixWord ++ tailWord_7688789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688789).length < 2 ^ (prefixWord ++ tailWord_7688789).sum := by decide
  have hdescent : baseEnd_7688789 < baseStart_7688789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688799 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 3]
def baseStart_7688799 : Nat := 118140960795 + 7688799 * 2 ^ 59
def prefixEnd_7688799 : Nat := 4983230072969 + 3 ^ 40 * 7688799 * 2
def baseEnd_7688799 : Nat := 3948049542808968272252363

theorem tailTrace_7688799 : CollatzResearch.WordTrace tailWord_7688799 prefixEnd_7688799 3948049542808968272252363 := by
  unfold tailWord_7688799
  simp only [CollatzResearch.WordTrace]
  refine ⟨280433538071801840169709451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186955692047867893446472967 280433538071801840169709451)
  ·
    refine ⟨420650307107702760254564177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280433538071801840169709451 420650307107702760254564177)
    ·
      refine ⟨315487730330777070190923133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420650307107702760254564177 315487730330777070190923133)
      ·
        refine ⟨118307898874041401321596175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315487730330777070190923133 118307898874041401321596175)
        ·
          refine ⟨177461848311062101982394263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118307898874041401321596175 177461848311062101982394263)
          ·
            refine ⟨266192772466593152973591395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177461848311062101982394263 266192772466593152973591395)
            ·
              refine ⟨399289158699889729460387093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266192772466593152973591395 399289158699889729460387093)
              ·
                refine ⟨18716679314057331068455645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 399289158699889729460387093 18716679314057331068455645)
                ·
                  refine ⟨7018754742771499150670867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18716679314057331068455645 7018754742771499150670867)
                  ·
                    refine ⟨10528132114157248726006301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7018754742771499150670867 10528132114157248726006301)
                    ·
                      refine ⟨3948049542808968272252363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10528132114157248726006301 3948049542808968272252363)
                      ·
                        rfl

theorem cell23_7688799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_7688799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688799 prefixEnd_7688799 := by exact prefixLift 7688799
  have htrace : WordTrace (prefixWord ++ tailWord_7688799) baseStart_7688799 baseEnd_7688799 := by
    simpa [prefixWord, tailWord_7688799, baseEnd_7688799] using wordTrace_append hprefix tailTrace_7688799
  have hstable : (prefixWord ++ tailWord_7688799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688799).length < 2 ^ (prefixWord ++ tailWord_7688799).sum := by decide
  have hdescent : baseEnd_7688799 < baseStart_7688799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688833 : List Nat := [1, 2, 4, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_7688833 : Nat := 118140960795 + 7688833 * 2 ^ 59
def prefixEnd_7688833 : Nat := 4983230072969 + 3 ^ 40 * 7688833 * 2
def baseEnd_7688833 : Nat := 3948067001151221139227207

theorem tailTrace_7688833 : CollatzResearch.WordTrace tailWord_7688833 prefixEnd_7688833 3948067001151221139227207 := by
  unfold tailWord_7688833
  simp only [CollatzResearch.WordTrace]
  refine ⟨280434778153678663976447153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186956518769119109317631435 280434778153678663976447153)
  ·
    refine ⟨210326083615258997982335365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280434778153678663976447153 210326083615258997982335365)
    ·
      refine ⟨39436140677861062121687881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210326083615258997982335365 39436140677861062121687881)
      ·
        refine ⟨29577105508395796591265911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39436140677861062121687881 29577105508395796591265911)
        ·
          refine ⟨44365658262593694886898867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29577105508395796591265911 44365658262593694886898867)
          ·
            refine ⟨66548487393890542330348301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44365658262593694886898867 66548487393890542330348301)
            ·
              refine ⟨24955682772708953373880613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66548487393890542330348301 24955682772708953373880613)
              ·
                refine ⟨4679190519882928757602615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24955682772708953373880613 4679190519882928757602615)
                ·
                  refine ⟨7018785779824393136403923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679190519882928757602615 7018785779824393136403923)
                  ·
                    refine ⟨10528178669736589704605885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7018785779824393136403923 10528178669736589704605885)
                    ·
                      refine ⟨3948067001151221139227207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10528178669736589704605885 3948067001151221139227207)
                      ·
                        rfl

theorem cell23_7688833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_7688833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688833 prefixEnd_7688833 := by exact prefixLift 7688833
  have htrace : WordTrace (prefixWord ++ tailWord_7688833) baseStart_7688833 baseEnd_7688833 := by
    simpa [prefixWord, tailWord_7688833, baseEnd_7688833] using wordTrace_append hprefix tailTrace_7688833
  have hstable : (prefixWord ++ tailWord_7688833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688833).length < 2 ^ (prefixWord ++ tailWord_7688833).sum := by decide
  have hdescent : baseEnd_7688833 < baseStart_7688833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688873 : List Nat := [1, 2, 1, 1, 1, 1, 2, 9, 1, 2, 2]
def baseStart_7688873 : Nat := 118140960795 + 7688873 * 2 ^ 59
def prefixEnd_7688873 : Nat := 4983230072969 + 3 ^ 40 * 7688873 * 2
def baseEnd_7688873 : Nat := 3948087540377400982727023

theorem tailTrace_7688873 : CollatzResearch.WordTrace tailWord_7688873 prefixEnd_7688873 3948087540377400982727023 := by
  unfold tailWord_7688873
  simp only [CollatzResearch.WordTrace]
  refine ⟨280436237073533750807903273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186957491382355833871935515 280436237073533750807903273)
  ·
    refine ⟨210327177805150313105927455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280436237073533750807903273 210327177805150313105927455)
    ·
      refine ⟨315490766707725469658891183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210327177805150313105927455 315490766707725469658891183)
      ·
        refine ⟨473236150061588204488336775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315490766707725469658891183 473236150061588204488336775)
        ·
          refine ⟨709854225092382306732505163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473236150061588204488336775 709854225092382306732505163)
          ·
            refine ⟨1064781337638573460098757745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709854225092382306732505163 1064781337638573460098757745)
            ·
              refine ⟨798586003228930095074068309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064781337638573460098757745 798586003228930095074068309)
              ·
                refine ⟨4679214862669512275824619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 798586003228930095074068309 4679214862669512275824619)
                ·
                  refine ⟨7018822294004268413736929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679214862669512275824619 7018822294004268413736929)
                  ·
                    refine ⟨5264116720503201310302697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7018822294004268413736929 5264116720503201310302697)
                    ·
                      refine ⟨3948087540377400982727023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264116720503201310302697 3948087540377400982727023)
                      ·
                        rfl

theorem cell23_7688873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 1, 2, 2].length) (baseStart_7688873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688873 prefixEnd_7688873 := by exact prefixLift 7688873
  have htrace : WordTrace (prefixWord ++ tailWord_7688873) baseStart_7688873 baseEnd_7688873 := by
    simpa [prefixWord, tailWord_7688873, baseEnd_7688873] using wordTrace_append hprefix tailTrace_7688873
  have hstable : (prefixWord ++ tailWord_7688873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688873).length < 2 ^ (prefixWord ++ tailWord_7688873).sum := by decide
  have hdescent : baseEnd_7688873 < baseStart_7688873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688882 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_7688882 : Nat := 118140960795 + 7688882 * 2 ^ 59
def prefixEnd_7688882 : Nat := 4983230072969 + 3 ^ 40 * 7688882 * 2
def baseEnd_7688882 : Nat := 3948092161703291447514481

theorem tailTrace_7688882 : CollatzResearch.WordTrace tailWord_7688882 prefixEnd_7688882 3948092161703291447514481 := by
  unfold tailWord_7688882
  simp only [CollatzResearch.WordTrace]
  refine ⟨70109141332625286336245225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186957710220334096896653933 70109141332625286336245225)
  ·
    refine ⟨52581855999468964752183919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70109141332625286336245225 52581855999468964752183919)
    ·
      refine ⟨78872783999203447128275879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52581855999468964752183919 78872783999203447128275879)
      ·
        refine ⟨118309175998805170692413819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78872783999203447128275879 118309175998805170692413819)
        ·
          refine ⟨177463763998207756038620729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118309175998805170692413819 177463763998207756038620729)
          ·
            refine ⟨133097822998655817028965547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177463763998207756038620729 133097822998655817028965547)
            ·
              refine ⟨199646734497983725543448321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133097822998655817028965547 199646734497983725543448321)
              ·
                refine ⟨149735050873487794157586241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199646734497983725543448321 149735050873487794157586241)
                ·
                  refine ⟨112301288155115845618189681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149735050873487794157586241 112301288155115845618189681)
                  ·
                    refine ⟨84225966116336884213642261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112301288155115845618189681 84225966116336884213642261)
                    ·
                      refine ⟨3948092161703291447514481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84225966116336884213642261 3948092161703291447514481)
                      ·
                        rfl

theorem cell23_7688882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_7688882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688882 prefixEnd_7688882 := by exact prefixLift 7688882
  have htrace : WordTrace (prefixWord ++ tailWord_7688882) baseStart_7688882 baseEnd_7688882 := by
    simpa [prefixWord, tailWord_7688882, baseEnd_7688882] using wordTrace_append hprefix tailTrace_7688882
  have hstable : (prefixWord ++ tailWord_7688882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688882).length < 2 ^ (prefixWord ++ tailWord_7688882).sum := by decide
  have hdescent : baseEnd_7688882 < baseStart_7688882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688906 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_7688906 : Nat := 118140960795 + 7688906 * 2 ^ 59
def prefixEnd_7688906 : Nat := 4983230072969 + 3 ^ 40 * 7688906 * 2
def baseEnd_7688906 : Nat := 3948104485238999353614371

theorem tailTrace_7688906 : CollatzResearch.WordTrace tailWord_7688906 prefixEnd_7688906 3948104485238999353614371 := by
  unfold tailWord_7688906
  simp only [CollatzResearch.WordTrace]
  refine ⟨70109360170603549360963643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186958293788276131629236381 70109360170603549360963643)
  ·
    refine ⟨105164040255905324041445465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70109360170603549360963643 105164040255905324041445465)
    ·
      refine ⟨78873030191928993031084099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105164040255905324041445465 78873030191928993031084099)
      ·
        refine ⟨118309545287893489546626149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78873030191928993031084099 118309545287893489546626149)
        ·
          refine ⟨22183039741480029289992403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118309545287893489546626149 22183039741480029289992403)
          ·
            refine ⟨33274559612220043934988605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22183039741480029289992403 33274559612220043934988605)
            ·
              refine ⟨12477959854582516475620727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33274559612220043934988605 12477959854582516475620727)
              ·
                refine ⟨18716939781873774713431091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12477959854582516475620727 18716939781873774713431091)
                ·
                  refine ⟨28075409672810662070146637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18716939781873774713431091 28075409672810662070146637)
                  ·
                    refine ⟨10528278627303998276304989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28075409672810662070146637 10528278627303998276304989)
                    ·
                      refine ⟨3948104485238999353614371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10528278627303998276304989 3948104485238999353614371)
                      ·
                        rfl

theorem cell23_7688906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_7688906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688906 prefixEnd_7688906 := by exact prefixLift 7688906
  have htrace : WordTrace (prefixWord ++ tailWord_7688906) baseStart_7688906 baseEnd_7688906 := by
    simpa [prefixWord, tailWord_7688906, baseEnd_7688906] using wordTrace_append hprefix tailTrace_7688906
  have hstable : (prefixWord ++ tailWord_7688906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688906).length < 2 ^ (prefixWord ++ tailWord_7688906).sum := by decide
  have hdescent : baseEnd_7688906 < baseStart_7688906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688912 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_7688912 : Nat := 118140960795 + 7688912 * 2 ^ 59
def prefixEnd_7688912 : Nat := 4983230072969 + 3 ^ 40 * 7688912 * 2
def baseEnd_7688912 : Nat := 3948107566122926330139343

theorem tailTrace_7688912 : CollatzResearch.WordTrace tailWord_7688912 prefixEnd_7688912 3948107566122926330139343 := by
  unfold tailWord_7688912
  simp only [CollatzResearch.WordTrace]
  refine ⟨140218829760196230234286495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186958439680261640312381993 140218829760196230234286495)
  ·
    refine ⟨210328244640294345351429743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140218829760196230234286495 210328244640294345351429743)
    ·
      refine ⟨315492366960441518027144615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210328244640294345351429743 315492366960441518027144615)
      ·
        refine ⟨473238550440662277040716923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315492366960441518027144615 473238550440662277040716923)
        ·
          refine ⟨709857825660993415561075385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473238550440662277040716923 709857825660993415561075385)
          ·
            refine ⟨532393369245745061670806539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709857825660993415561075385 532393369245745061670806539)
            ·
              refine ⟨798590053868617592506209809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532393369245745061670806539 798590053868617592506209809)
              ·
                refine ⟨598942540401463194379657357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798590053868617592506209809 598942540401463194379657357)
                ·
                  refine ⟨224603452650548697892371509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598942540401463194379657357 224603452650548697892371509)
                  ·
                    refine ⟨21056573685988940427409829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224603452650548697892371509 21056573685988940427409829)
                    ·
                      refine ⟨3948107566122926330139343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21056573685988940427409829 3948107566122926330139343)
                      ·
                        rfl

theorem cell23_7688912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_7688912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688912 prefixEnd_7688912 := by exact prefixLift 7688912
  have htrace : WordTrace (prefixWord ++ tailWord_7688912) baseStart_7688912 baseEnd_7688912 := by
    simpa [prefixWord, tailWord_7688912, baseEnd_7688912] using wordTrace_append hprefix tailTrace_7688912
  have hstable : (prefixWord ++ tailWord_7688912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688912).length < 2 ^ (prefixWord ++ tailWord_7688912).sum := by decide
  have hdescent : baseEnd_7688912 < baseStart_7688912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688924 : List Nat := [2, 2, 5, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_7688924 : Nat := 118140960795 + 7688924 * 2 ^ 59
def prefixEnd_7688924 : Nat := 4983230072969 + 3 ^ 40 * 7688924 * 2
def baseEnd_7688924 : Nat := 3948113727890780283189289

theorem tailTrace_7688924 : CollatzResearch.WordTrace tailWord_7688924 prefixEnd_7688924 3948113727890780283189289 := by
  unfold tailWord_7688924
  simp only [CollatzResearch.WordTrace]
  refine ⟨140219048598174493259004913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186958731464232657678673217 140219048598174493259004913)
  ·
    refine ⟨105164286448630869944253685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140219048598174493259004913 105164286448630869944253685)
    ·
      refine ⟨9859151854559144057273783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105164286448630869944253685 9859151854559144057273783)
      ·
        refine ⟨14788727781838716085910675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859151854559144057273783 14788727781838716085910675)
        ·
          refine ⟨22183091672758074128866013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14788727781838716085910675 22183091672758074128866013)
          ·
            refine ⟨8318659377284277798324755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22183091672758074128866013 8318659377284277798324755)
            ·
              refine ⟨12477989065926416697487133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318659377284277798324755 12477989065926416697487133)
              ·
                refine ⟨4679245899722406261557675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12477989065926416697487133 4679245899722406261557675)
                ·
                  refine ⟨7018868849583609392336513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679245899722406261557675 7018868849583609392336513)
                  ·
                    refine ⟨5264151637187707044252385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7018868849583609392336513 5264151637187707044252385)
                    ·
                      refine ⟨3948113727890780283189289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264151637187707044252385 3948113727890780283189289)
                      ·
                        rfl

theorem cell23_7688924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_7688924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688924 prefixEnd_7688924 := by exact prefixLift 7688924
  have htrace : WordTrace (prefixWord ++ tailWord_7688924) baseStart_7688924 baseEnd_7688924 := by
    simpa [prefixWord, tailWord_7688924, baseEnd_7688924] using wordTrace_append hprefix tailTrace_7688924
  have hstable : (prefixWord ++ tailWord_7688924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688924).length < 2 ^ (prefixWord ++ tailWord_7688924).sum := by decide
  have hdescent : baseEnd_7688924 < baseStart_7688924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688933 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 1, 3, 2]
def baseStart_7688933 : Nat := 118140960795 + 7688933 * 2 ^ 59
def prefixEnd_7688933 : Nat := 4983230072969 + 3 ^ 40 * 7688933 * 2
def baseEnd_7688933 : Nat := 3948118349216670747976747

theorem tailTrace_7688933 : CollatzResearch.WordTrace tailWord_7688933 prefixEnd_7688933 3948118349216670747976747 := by
  unfold tailWord_7688933
  simp only [CollatzResearch.WordTrace]
  refine ⟨280438425453316381055087453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186958950302210920703391635 280438425453316381055087453)
  ·
    refine ⟨105164409544993642895657795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280438425453316381055087453 105164409544993642895657795)
    ·
      refine ⟨157746614317490464343486693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105164409544993642895657795 157746614317490464343486693)
      ·
        refine ⟨29577490184529462064403755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157746614317490464343486693 29577490184529462064403755)
        ·
          refine ⟨44366235276794193096605633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29577490184529462064403755 44366235276794193096605633)
          ·
            refine ⟨33274676457595644822454225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44366235276794193096605633 33274676457595644822454225)
            ·
              refine ⟨24956007343196733616840669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33274676457595644822454225 24956007343196733616840669)
              ·
                refine ⟨9358502753698775106315251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24956007343196733616840669 9358502753698775106315251)
                ·
                  refine ⟨14037754130548162659472877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9358502753698775106315251 14037754130548162659472877)
                  ·
                    refine ⟨5264157798955560997302329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14037754130548162659472877 5264157798955560997302329)
                    ·
                      refine ⟨3948118349216670747976747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264157798955560997302329 3948118349216670747976747)
                      ·
                        rfl

theorem cell23_7688933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_7688933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688933 prefixEnd_7688933 := by exact prefixLift 7688933
  have htrace : WordTrace (prefixWord ++ tailWord_7688933) baseStart_7688933 baseEnd_7688933 := by
    simpa [prefixWord, tailWord_7688933, baseEnd_7688933] using wordTrace_append hprefix tailTrace_7688933
  have hstable : (prefixWord ++ tailWord_7688933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688933).length < 2 ^ (prefixWord ++ tailWord_7688933).sum := by decide
  have hdescent : baseEnd_7688933 < baseStart_7688933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7688986 : List Nat := [3, 1, 1, 3, 2, 1, 2, 5, 5]
def baseStart_7688986 : Nat := 118140960795 + 7688986 * 2 ^ 59
def prefixEnd_7688986 : Nat := 4983230072969 + 3 ^ 40 * 7688986 * 2
def baseEnd_7688986 : Nat := 438682840410151004512667

theorem tailTrace_7688986 : CollatzResearch.WordTrace tailWord_7688986 prefixEnd_7688986 438682840410151004512667 := by
  unfold tailWord_7688986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70110089630531092776691703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186960239014749580737844541 70110089630531092776691703)
  ·
    refine ⟨105165134445796639165037555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70110089630531092776691703 105165134445796639165037555)
    ·
      refine ⟨157747701668694958747556333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105165134445796639165037555 157747701668694958747556333)
      ·
        refine ⟨59155388125760609530333625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157747701668694958747556333 59155388125760609530333625)
        ·
          refine ⟨44366541094320457147750219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59155388125760609530333625 44366541094320457147750219)
          ·
            refine ⟨66549811641480685721625329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44366541094320457147750219 66549811641480685721625329)
            ·
              refine ⟨49912358731110514291218997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66549811641480685721625329 49912358731110514291218997)
              ·
                refine ⟨4679283631041610714801781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49912358731110514291218997 4679283631041610714801781)
                ·
                  refine ⟨438682840410151004512667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4679283631041610714801781 438682840410151004512667)
                  ·
                    rfl

theorem cell23_7688986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_7688986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7688986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7688986 prefixEnd_7688986 := by exact prefixLift 7688986
  have htrace : WordTrace (prefixWord ++ tailWord_7688986) baseStart_7688986 baseEnd_7688986 := by
    simpa [prefixWord, tailWord_7688986, baseEnd_7688986] using wordTrace_append hprefix tailTrace_7688986
  have hstable : (prefixWord ++ tailWord_7688986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7688986).length < 2 ^ (prefixWord ++ tailWord_7688986).sum := by decide
  have hdescent : baseEnd_7688986 < baseStart_7688986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7688986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689009 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_7689009 : Nat := 118140960795 + 7689009 * 2 ^ 59
def prefixEnd_7689009 : Nat := 4983230072969 + 3 ^ 40 * 7689009 * 2
def baseEnd_7689009 : Nat := 3948157373746412450626397

theorem tailTrace_7689009 : CollatzResearch.WordTrace tailWord_7689009 prefixEnd_7689009 3948157373746412450626397 := by
  unfold tailWord_7689009
  simp only [CollatzResearch.WordTrace]
  refine ⟨280441197401041046034854081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186960798267360697356569387 280441197401041046034854081)
  ·
    refine ⟨210330898050780784526140561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280441197401041046034854081 210330898050780784526140561)
    ·
      refine ⟨157748173538085588394605421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210330898050780784526140561 157748173538085588394605421)
      ·
        refine ⟨59155565076782095647977033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157748173538085588394605421 59155565076782095647977033)
        ·
          refine ⟨44366673807586571735982775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59155565076782095647977033 44366673807586571735982775)
          ·
            refine ⟨66550010711379857603974163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44366673807586571735982775 66550010711379857603974163)
            ·
              refine ⟨99825016067069786405961245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66550010711379857603974163 99825016067069786405961245)
              ·
                refine ⟨37434381025151169902235467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99825016067069786405961245 37434381025151169902235467)
                ·
                  refine ⟨56151571537726754853353201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37434381025151169902235467 56151571537726754853353201)
                  ·
                    refine ⟨42113678653295066140014901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56151571537726754853353201 42113678653295066140014901)
                    ·
                      refine ⟨3948157373746412450626397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42113678653295066140014901 3948157373746412450626397)
                      ·
                        rfl

theorem cell23_7689009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_7689009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689009 prefixEnd_7689009 := by exact prefixLift 7689009
  have htrace : WordTrace (prefixWord ++ tailWord_7689009) baseStart_7689009 baseEnd_7689009 := by
    simpa [prefixWord, tailWord_7689009, baseEnd_7689009] using wordTrace_append hprefix tailTrace_7689009
  have hstable : (prefixWord ++ tailWord_7689009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689009).length < 2 ^ (prefixWord ++ tailWord_7689009).sum := by decide
  have hdescent : baseEnd_7689009 < baseStart_7689009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689036 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_7689036 : Nat := 118140960795 + 7689036 * 2 ^ 59
def prefixEnd_7689036 : Nat := 4983230072969 + 3 ^ 40 * 7689036 * 2
def baseEnd_7689036 : Nat := 3948171237724083844988773

theorem tailTrace_7689036 : CollatzResearch.WordTrace tailWord_7689036 prefixEnd_7689036 3948171237724083844988773 := by
  unfold tailWord_7689036
  simp only [CollatzResearch.WordTrace]
  refine ⟨140221091085971614823043481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186961454781295486430724641 140221091085971614823043481)
  ·
    refine ⟨105165818314478711117282611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140221091085971614823043481 105165818314478711117282611)
    ·
      refine ⟨157748727471718066675923917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105165818314478711117282611 157748727471718066675923917)
      ·
        refine ⟨59155772801894275003471469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157748727471718066675923917 59155772801894275003471469)
        ·
          refine ⟨22183414800710353126301801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59155772801894275003471469 22183414800710353126301801)
          ·
            refine ⟨16637561100532764844726351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22183414800710353126301801 16637561100532764844726351)
            ·
              refine ⟨24956341650799147267089527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16637561100532764844726351 24956341650799147267089527)
              ·
                refine ⟨37434512476198720900634291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24956341650799147267089527 37434512476198720900634291)
                ·
                  refine ⟨56151768714298081350951437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37434512476198720900634291 56151768714298081350951437)
                  ·
                    refine ⟨21056913267861780506606789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56151768714298081350951437 21056913267861780506606789)
                    ·
                      refine ⟨3948171237724083844988773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21056913267861780506606789 3948171237724083844988773)
                      ·
                        rfl

theorem cell23_7689036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_7689036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689036 prefixEnd_7689036 := by exact prefixLift 7689036
  have htrace : WordTrace (prefixWord ++ tailWord_7689036) baseStart_7689036 baseEnd_7689036 := by
    simpa [prefixWord, tailWord_7689036, baseEnd_7689036] using wordTrace_append hprefix tailTrace_7689036
  have hstable : (prefixWord ++ tailWord_7689036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689036).length < 2 ^ (prefixWord ++ tailWord_7689036).sum := by decide
  have hdescent : baseEnd_7689036 < baseStart_7689036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689049 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_7689049 : Nat := 118140960795 + 7689049 * 2 ^ 59
def prefixEnd_7689049 : Nat := 4983230072969 + 3 ^ 40 * 7689049 * 2
def baseEnd_7689049 : Nat := 3948177912972592294126213

theorem tailTrace_7689049 : CollatzResearch.WordTrace tailWord_7689049 prefixEnd_7689049 3948177912972592294126213 := by
  unfold tailWord_7689049
  simp only [CollatzResearch.WordTrace]
  refine ⟨280442656320896132866310201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186961770880597421910873467 280442656320896132866310201)
  ·
    refine ⟨210331992240672099649732651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280442656320896132866310201 210331992240672099649732651)
    ·
      refine ⟨315497988361008149474598977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210331992240672099649732651 315497988361008149474598977)
      ·
        refine ⟨236623491270756112105949233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315497988361008149474598977 236623491270756112105949233)
        ·
          refine ⟨177467618453067084079461925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236623491270756112105949233 177467618453067084079461925)
          ·
            refine ⟨33275178459950078264899111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177467618453067084079461925 33275178459950078264899111)
            ·
              refine ⟨49912767689925117397348667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33275178459950078264899111 49912767689925117397348667)
              ·
                refine ⟨74869151534887676096023001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49912767689925117397348667 74869151534887676096023001)
                ·
                  refine ⟨56151863651165757072017251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74869151534887676096023001 56151863651165757072017251)
                  ·
                    refine ⟨84227795476748635608025877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56151863651165757072017251 84227795476748635608025877)
                    ·
                      refine ⟨3948177912972592294126213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84227795476748635608025877 3948177912972592294126213)
                      ·
                        rfl

theorem cell23_7689049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_7689049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689049 prefixEnd_7689049 := by exact prefixLift 7689049
  have htrace : WordTrace (prefixWord ++ tailWord_7689049) baseStart_7689049 baseEnd_7689049 := by
    simpa [prefixWord, tailWord_7689049, baseEnd_7689049] using wordTrace_append hprefix tailTrace_7689049
  have hstable : (prefixWord ++ tailWord_7689049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689049).length < 2 ^ (prefixWord ++ tailWord_7689049).sum := by decide
  have hdescent : baseEnd_7689049 < baseStart_7689049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689056 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 3]
def baseStart_7689056 : Nat := 118140960795 + 7689056 * 2 ^ 59
def prefixEnd_7689056 : Nat := 4983230072969 + 3 ^ 40 * 7689056 * 2
def baseEnd_7689056 : Nat := 3948181507337173766738681

theorem tailTrace_7689056 : CollatzResearch.WordTrace tailWord_7689056 prefixEnd_7689056 3948181507337173766738681 := by
  unfold tailWord_7689056
  simp only [CollatzResearch.WordTrace]
  refine ⟨140221455815935386530907511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186961941087913848707876681 140221455815935386530907511)
  ·
    refine ⟨210332183723903079796361267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140221455815935386530907511 210332183723903079796361267)
    ·
      refine ⟨315498275585854619694541901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210332183723903079796361267 315498275585854619694541901)
      ·
        refine ⟨118311853344695482385453213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315498275585854619694541901 118311853344695482385453213)
        ·
          refine ⟨44366945004260805894544955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118311853344695482385453213 44366945004260805894544955)
          ·
            refine ⟨66550417506391208841817433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44366945004260805894544955 66550417506391208841817433)
            ·
              refine ⟨49912813129793406631363075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66550417506391208841817433 49912813129793406631363075)
              ·
                refine ⟨74869219694690109947044613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49912813129793406631363075 74869219694690109947044613)
                ·
                  refine ⟨14037978692754395615070865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74869219694690109947044613 14037978692754395615070865)
                  ·
                    refine ⟨10528484019565796711303149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14037978692754395615070865 10528484019565796711303149)
                    ·
                      refine ⟨3948181507337173766738681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10528484019565796711303149 3948181507337173766738681)
                      ·
                        rfl

theorem cell23_7689056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_7689056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689056 prefixEnd_7689056 := by exact prefixLift 7689056
  have htrace : WordTrace (prefixWord ++ tailWord_7689056) baseStart_7689056 baseEnd_7689056 := by
    simpa [prefixWord, tailWord_7689056, baseEnd_7689056] using wordTrace_append hprefix tailTrace_7689056
  have hstable : (prefixWord ++ tailWord_7689056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689056).length < 2 ^ (prefixWord ++ tailWord_7689056).sum := by decide
  have hdescent : baseEnd_7689056 < baseStart_7689056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689063 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 3, 4]
def baseStart_7689063 : Nat := 118140960795 + 7689063 * 2 ^ 59
def prefixEnd_7689063 : Nat := 4983230072969 + 3 ^ 40 * 7689063 * 2
def baseEnd_7689063 : Nat := 1316061700567251746450383

theorem tailTrace_7689063 : CollatzResearch.WordTrace tailWord_7689063 prefixEnd_7689063 1316061700567251746450383 := by
  unfold tailWord_7689063
  simp only [CollatzResearch.WordTrace]
  refine ⟨280443166942845413257319843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186962111295230275504879895 280443166942845413257319843)
  ·
    refine ⟨420664750414268119885979765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280443166942845413257319843 420664750414268119885979765)
    ·
      refine ⟨39437320351337636239310603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 420664750414268119885979765 39437320351337636239310603)
      ·
        refine ⟨59155980527006454358965905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39437320351337636239310603 59155980527006454358965905)
        ·
          refine ⟨44366985395254840769224429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59155980527006454358965905 44366985395254840769224429)
          ·
            refine ⟨16637619523220565288459161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44366985395254840769224429 16637619523220565288459161)
            ·
              refine ⟨12478214642415423966344371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16637619523220565288459161 12478214642415423966344371)
              ·
                refine ⟨18717321963623135949516557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12478214642415423966344371 18717321963623135949516557)
                ·
                  refine ⟨7018995736358675981068709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18717321963623135949516557 7018995736358675981068709)
                  ·
                    refine ⟨1316061700567251746450383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7018995736358675981068709 1316061700567251746450383)
                    ·
                      rfl

theorem cell23_7689063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_7689063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689063 prefixEnd_7689063 := by exact prefixLift 7689063
  have htrace : WordTrace (prefixWord ++ tailWord_7689063) baseStart_7689063 baseEnd_7689063 := by
    simpa [prefixWord, tailWord_7689063, baseEnd_7689063] using wordTrace_append hprefix tailTrace_7689063
  have hstable : (prefixWord ++ tailWord_7689063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689063).length < 2 ^ (prefixWord ++ tailWord_7689063).sum := by decide
  have hdescent : baseEnd_7689063 < baseStart_7689063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689110 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7689110 : Nat := 118140960795 + 7689110 * 2 ^ 59
def prefixEnd_7689110 : Nat := 4983230072969 + 3 ^ 40 * 7689110 * 2
def baseEnd_7689110 : Nat := 438689915032501839495937

theorem tailTrace_7689110 : CollatzResearch.WordTrace tailWord_7689110 prefixEnd_7689110 438689915032501839495937 := by
  unfold tailWord_7689110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17527805073354696267767549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186963254115783426856187189 17527805073354696267767549)
  ·
    refine ⟨6572926902508011100412831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17527805073354696267767549 6572926902508011100412831)
    ·
      refine ⟨9859390353762016650619247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6572926902508011100412831 9859390353762016650619247)
      ·
        refine ⟨14789085530643024975928871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859390353762016650619247 14789085530643024975928871)
        ·
          refine ⟨22183628295964537463893307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14789085530643024975928871 22183628295964537463893307)
          ·
            refine ⟨33275442443946806195839961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22183628295964537463893307 33275442443946806195839961)
            ·
              refine ⟨24956581832960104646879971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33275442443946806195839961 24956581832960104646879971)
              ·
                refine ⟨37434872749440156970319957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24956581832960104646879971 37434872749440156970319957)
                ·
                  refine ⟨438689915032501839495937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37434872749440156970319957 438689915032501839495937)
                  ·
                    rfl

theorem cell23_7689110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7689110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689110 prefixEnd_7689110 := by exact prefixLift 7689110
  have htrace : WordTrace (prefixWord ++ tailWord_7689110) baseStart_7689110 baseEnd_7689110 := by
    simpa [prefixWord, tailWord_7689110, baseEnd_7689110] using wordTrace_append hprefix tailTrace_7689110
  have hstable : (prefixWord ++ tailWord_7689110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689110).length < 2 ^ (prefixWord ++ tailWord_7689110).sum := by decide
  have hdescent : baseEnd_7689110 < baseStart_7689110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689120 : List Nat := [2, 1, 1, 4, 1, 1, 2, 6, 1, 1, 3]
def baseStart_7689120 : Nat := 118140960795 + 7689120 * 2 ^ 59
def prefixEnd_7689120 : Nat := 4983230072969 + 3 ^ 40 * 7689120 * 2
def baseEnd_7689120 : Nat := 3948214370099061516338387

theorem tailTrace_7689120 : CollatzResearch.WordTrace tailWord_7689120 prefixEnd_7689120 3948214370099061516338387 := by
  unfold tailWord_7689120
  simp only [CollatzResearch.WordTrace]
  refine ⟨140222622951819455996072407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186963497269092607994763209 140222622951819455996072407)
  ·
    refine ⟨210333934427729183994108611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140222622951819455996072407 210333934427729183994108611)
    ·
      refine ⟨315500901641593775991162917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210333934427729183994108611 315500901641593775991162917)
      ·
        refine ⟨59156419057798832998343047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315500901641593775991162917 59156419057798832998343047)
        ·
          refine ⟨88734628586698249497514571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59156419057798832998343047 88734628586698249497514571)
          ·
            refine ⟨133101942880047374246271857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88734628586698249497514571 133101942880047374246271857)
            ·
              refine ⟨99826457160035530684703893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133101942880047374246271857 99826457160035530684703893)
              ·
                refine ⟨4679365179376665500845495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99826457160035530684703893 4679365179376665500845495)
                ·
                  refine ⟨7019047769064998251268243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679365179376665500845495 7019047769064998251268243)
                  ·
                    refine ⟨10528571653597497376902365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7019047769064998251268243 10528571653597497376902365)
                    ·
                      refine ⟨3948214370099061516338387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10528571653597497376902365 3948214370099061516338387)
                      ·
                        rfl

theorem cell23_7689120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_7689120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689120 prefixEnd_7689120 := by exact prefixLift 7689120
  have htrace : WordTrace (prefixWord ++ tailWord_7689120) baseStart_7689120 baseEnd_7689120 := by
    simpa [prefixWord, tailWord_7689120, baseEnd_7689120] using wordTrace_append hprefix tailTrace_7689120
  have hstable : (prefixWord ++ tailWord_7689120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689120).length < 2 ^ (prefixWord ++ tailWord_7689120).sum := by decide
  have hdescent : baseEnd_7689120 < baseStart_7689120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689127 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 6]
def baseStart_7689127 : Nat := 118140960795 + 7689127 * 2 ^ 59
def prefixEnd_7689127 : Nat := 4983230072969 + 3 ^ 40 * 7689127 * 2
def baseEnd_7689127 : Nat := 438690884940404776550095

theorem tailTrace_7689127 : CollatzResearch.WordTrace tailWord_7689127 prefixEnd_7689127 438690884940404776550095 := by
  unfold tailWord_7689127
  simp only [CollatzResearch.WordTrace]
  refine ⟨280445501214613552187649635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186963667476409034791766423 280445501214613552187649635)
  ·
    refine ⟨420668251821920328281474453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280445501214613552187649635 420668251821920328281474453)
    ·
      refine ⟨19718824304152515388194115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 420668251821920328281474453 19718824304152515388194115)
      ·
        refine ⟨29578236456228773082291173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19718824304152515388194115 29578236456228773082291173)
        ·
          refine ⟨5545919335542894952929595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29578236456228773082291173 5545919335542894952929595)
          ·
            refine ⟨8318879003314342429394393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545919335542894952929595 8318879003314342429394393)
            ·
              refine ⟨6239159252485756822045795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318879003314342429394393 6239159252485756822045795)
              ·
                refine ⟨9358738878728635233068693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239159252485756822045795 9358738878728635233068693)
                ·
                  refine ⟨438690884940404776550095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9358738878728635233068693 438690884940404776550095)
                  ·
                    rfl

theorem cell23_7689127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 6].length) (baseStart_7689127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689127 prefixEnd_7689127 := by exact prefixLift 7689127
  have htrace : WordTrace (prefixWord ++ tailWord_7689127) baseStart_7689127 baseEnd_7689127 := by
    simpa [prefixWord, tailWord_7689127, baseEnd_7689127] using wordTrace_append hprefix tailTrace_7689127
  have hstable : (prefixWord ++ tailWord_7689127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689127).length < 2 ^ (prefixWord ++ tailWord_7689127).sum := by decide
  have hdescent : baseEnd_7689127 < baseStart_7689127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689140 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7689140 : Nat := 118140960795 + 7689140 * 2 ^ 59
def prefixEnd_7689140 : Nat := 4983230072969 + 3 ^ 40 * 7689140 * 2
def baseEnd_7689140 : Nat := 1316074879904050479362765

theorem tailTrace_7689140 : CollatzResearch.WordTrace tailWord_7689140 prefixEnd_7689140 1316074879904050479362765 := by
  unfold tailWord_7689140
  simp only [CollatzResearch.WordTrace]
  refine ⟨140222987681783227703936437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186963983575710970271915249 140222987681783227703936437)
  ·
    refine ⟨13145905095167177597244041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140222987681783227703936437 13145905095167177597244041)
    ·
      refine ⟨9859428821375383197933031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13145905095167177597244041 9859428821375383197933031)
      ·
        refine ⟨14789143232063074796899547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859428821375383197933031 14789143232063074796899547)
        ·
          refine ⟨22183714848094612195349321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14789143232063074796899547 22183714848094612195349321)
          ·
            refine ⟨16637786136070959146511991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22183714848094612195349321 16637786136070959146511991)
            ·
              refine ⟨24956679204106438719767987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16637786136070959146511991 24956679204106438719767987)
              ·
                refine ⟨37435018806159658079651981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24956679204106438719767987 37435018806159658079651981)
                ·
                  refine ⟨14038132052309871779869493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37435018806159658079651981 14038132052309871779869493)
                  ·
                    refine ⟨1316074879904050479362765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14038132052309871779869493 1316074879904050479362765)
                    ·
                      rfl

theorem cell23_7689140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7689140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689140 prefixEnd_7689140 := by exact prefixLift 7689140
  have htrace : WordTrace (prefixWord ++ tailWord_7689140) baseStart_7689140 baseEnd_7689140 := by
    simpa [prefixWord, tailWord_7689140, baseEnd_7689140] using wordTrace_append hprefix tailTrace_7689140
  have hstable : (prefixWord ++ tailWord_7689140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689140).length < 2 ^ (prefixWord ++ tailWord_7689140).sum := by decide
  have hdescent : baseEnd_7689140 < baseStart_7689140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689143 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 4]
def baseStart_7689143 : Nat := 118140960795 + 7689143 * 2 ^ 59
def prefixEnd_7689143 : Nat := 4983230072969 + 3 ^ 40 * 7689143 * 2
def baseEnd_7689143 : Nat := 3948226180154114926350781

theorem tailTrace_7689143 : CollatzResearch.WordTrace tailWord_7689143 prefixEnd_7689143 3948226180154114926350781 := by
  unfold tailWord_7689143
  simp only [CollatzResearch.WordTrace]
  refine ⟨280446084782555586920232083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186964056521703724613488055 280446084782555586920232083)
  ·
    refine ⟨420669127173833380380348125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280446084782555586920232083 420669127173833380380348125)
    ·
      refine ⟨157750922690187517642630547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420669127173833380380348125 157750922690187517642630547)
      ·
        refine ⟨236626384035281276463945821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157750922690187517642630547 236626384035281276463945821)
        ·
          refine ⟨88734894013230478673979683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236626384035281276463945821 88734894013230478673979683)
          ·
            refine ⟨133102341019845718010969525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88734894013230478673979683 133102341019845718010969525)
            ·
              refine ⟨12478344470610536063528393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133102341019845718010969525 12478344470610536063528393)
              ·
                refine ⟨9358758352957902047646295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12478344470610536063528393 9358758352957902047646295)
                ·
                  refine ⟨14038137529436853071469443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9358758352957902047646295 14038137529436853071469443)
                  ·
                    refine ⟨21057206294155279607204165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14038137529436853071469443 21057206294155279607204165)
                    ·
                      refine ⟨3948226180154114926350781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21057206294155279607204165 3948226180154114926350781)
                      ·
                        rfl

theorem cell23_7689143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_7689143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689143 prefixEnd_7689143 := by exact prefixLift 7689143
  have htrace : WordTrace (prefixWord ++ tailWord_7689143) baseStart_7689143 baseEnd_7689143 := by
    simpa [prefixWord, tailWord_7689143, baseEnd_7689143] using wordTrace_append hprefix tailTrace_7689143
  have hstable : (prefixWord ++ tailWord_7689143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689143).length < 2 ^ (prefixWord ++ tailWord_7689143).sum := by decide
  have hdescent : baseEnd_7689143 < baseStart_7689143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689163 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 5]
def baseStart_7689163 : Nat := 118140960795 + 7689163 * 2 ^ 59
def prefixEnd_7689163 : Nat := 4983230072969 + 3 ^ 40 * 7689163 * 2
def baseEnd_7689163 : Nat := 3948236449767204848100689

theorem tailTrace_7689163 : CollatzResearch.WordTrace tailWord_7689163 prefixEnd_7689163 3948236449767204848100689 := by
  unfold tailWord_7689163
  simp only [CollatzResearch.WordTrace]
  refine ⟨280446814242483130335960143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186964542828322086890640095 280446814242483130335960143)
  ·
    refine ⟨420670221363724695503940215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280446814242483130335960143 420670221363724695503940215)
    ·
      refine ⟨631005332045587043255910323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420670221363724695503940215 631005332045587043255910323)
      ·
        refine ⟨946507998068380564883865485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631005332045587043255910323 946507998068380564883865485)
        ·
          refine ⟨354940499275642711831449557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 946507998068380564883865485 354940499275642711831449557)
          ·
            refine ⟨8318917951772876058549599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 354940499275642711831449557 8318917951772876058549599)
            ·
              refine ⟨12478376927659314087824399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318917951772876058549599 12478376927659314087824399)
              ·
                refine ⟨18717565391488971131736599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12478376927659314087824399 18717565391488971131736599)
                ·
                  refine ⟨28076348087233456697604899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18717565391488971131736599 28076348087233456697604899)
                  ·
                    refine ⟨42114522130850185046407349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28076348087233456697604899 42114522130850185046407349)
                    ·
                      refine ⟨3948236449767204848100689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42114522130850185046407349 3948236449767204848100689)
                      ·
                        rfl

theorem cell23_7689163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 5].length) (baseStart_7689163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689163 prefixEnd_7689163 := by exact prefixLift 7689163
  have htrace : WordTrace (prefixWord ++ tailWord_7689163) baseStart_7689163 baseEnd_7689163 := by
    simpa [prefixWord, tailWord_7689163, baseEnd_7689163] using wordTrace_append hprefix tailTrace_7689163
  have hstable : (prefixWord ++ tailWord_7689163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689163).length < 2 ^ (prefixWord ++ tailWord_7689163).sum := by decide
  have hdescent : baseEnd_7689163 < baseStart_7689163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689165 : List Nat := [1, 6, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7689165 : Nat := 118140960795 + 7689165 * 2 ^ 59
def prefixEnd_7689165 : Nat := 4983230072969 + 3 ^ 40 * 7689165 * 2
def baseEnd_7689165 : Nat := 1316079158909504613425227

theorem tailTrace_7689165 : CollatzResearch.WordTrace tailWord_7689165 prefixEnd_7689165 1316079158909504613425227 := by
  unfold tailWord_7689165
  simp only [CollatzResearch.WordTrace]
  refine ⟨280446887188475884677532949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186964591458983923118355299 280446887188475884677532949)
  ·
    refine ⟨13145947836959807094259357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 280446887188475884677532949 13145947836959807094259357)
    ·
      refine ⟨4929730438859927660347259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13145947836959807094259357 4929730438859927660347259)
      ·
        refine ⟨7394595658289891490520889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4929730438859927660347259 7394595658289891490520889)
        ·
          refine ⟨5545946743717418617890667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7394595658289891490520889 5545946743717418617890667)
          ·
            refine ⟨8318920115576127926836001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5545946743717418617890667 8318920115576127926836001)
            ·
              refine ⟨6239190086682095945127001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8318920115576127926836001 6239190086682095945127001)
              ·
                refine ⟨4679392565011571958845251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239190086682095945127001 4679392565011571958845251)
                ·
                  refine ⟨7019088847517357938267877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679392565011571958845251 7019088847517357938267877)
                  ·
                    refine ⟨1316079158909504613425227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7019088847517357938267877 1316079158909504613425227)
                    ·
                      rfl

theorem cell23_7689165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7689165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689165 prefixEnd_7689165 := by exact prefixLift 7689165
  have htrace : WordTrace (prefixWord ++ tailWord_7689165) baseStart_7689165 baseEnd_7689165 := by
    simpa [prefixWord, tailWord_7689165, baseEnd_7689165] using wordTrace_append hprefix tailTrace_7689165
  have hstable : (prefixWord ++ tailWord_7689165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689165).length < 2 ^ (prefixWord ++ tailWord_7689165).sum := by decide
  have hdescent : baseEnd_7689165 < baseStart_7689165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689170 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_7689170 : Nat := 118140960795 + 7689170 * 2 ^ 59
def prefixEnd_7689170 : Nat := 4983230072969 + 3 ^ 40 * 7689170 * 2
def baseEnd_7689170 : Nat := 1316080014710595440237719

theorem tailTrace_7689170 : CollatzResearch.WordTrace tailWord_7689170 prefixEnd_7689170 1316080014710595440237719 := by
  unfold tailWord_7689170
  simp only [CollatzResearch.WordTrace]
  refine ⟨70111767388364442632866241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186964713035638513687643309 70111767388364442632866241)
  ·
    refine ⟨52583825541273331974649681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70111767388364442632866241 52583825541273331974649681)
    ·
      refine ⟨39437869155954998980987261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52583825541273331974649681 39437869155954998980987261)
      ·
        refine ⟨14789200933483124617870223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39437869155954998980987261 14789200933483124617870223)
        ·
          refine ⟨22183801400224686926805335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14789200933483124617870223 22183801400224686926805335)
          ·
            refine ⟨33275702100337030390208003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22183801400224686926805335 33275702100337030390208003)
            ·
              refine ⟨49913553150505545585312005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33275702100337030390208003 49913553150505545585312005)
              ·
                refine ⟨9358791215719789797246001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49913553150505545585312005 9358791215719789797246001)
                ·
                  refine ⟨7019093411789842347934501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9358791215719789797246001 7019093411789842347934501)
                  ·
                    refine ⟨1316080014710595440237719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7019093411789842347934501 1316080014710595440237719)
                    ·
                      rfl

theorem cell23_7689170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_7689170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689170 prefixEnd_7689170 := by exact prefixLift 7689170
  have htrace : WordTrace (prefixWord ++ tailWord_7689170) baseStart_7689170 baseEnd_7689170 := by
    simpa [prefixWord, tailWord_7689170, baseEnd_7689170] using wordTrace_append hprefix tailTrace_7689170
  have hstable : (prefixWord ++ tailWord_7689170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689170).length < 2 ^ (prefixWord ++ tailWord_7689170).sum := by decide
  have hdescent : baseEnd_7689170 < baseStart_7689170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689183 : List Nat := [1, 1, 2, 3, 5, 2, 1, 8]
def baseStart_7689183 : Nat := 118140960795 + 7689183 * 2 ^ 59
def prefixEnd_7689183 : Nat := 4983230072969 + 3 ^ 40 * 7689183 * 2
def baseEnd_7689183 : Nat := 146231359977047954438911

theorem tailTrace_7689183 : CollatzResearch.WordTrace tailWord_7689183 prefixEnd_7689183 146231359977047954438911 := by
  unfold tailWord_7689183
  simp only [CollatzResearch.WordTrace]
  refine ⟨280447543702410673751688203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186965029134940449167792135 280447543702410673751688203)
  ·
    refine ⟨420671315553616010627532305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280447543702410673751688203 420671315553616010627532305)
    ·
      refine ⟨315503486665212007970649229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420671315553616010627532305 315503486665212007970649229)
      ·
        refine ⟨118313807499454502988993461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315503486665212007970649229 118313807499454502988993461)
        ·
          refine ⟨11091919453073859655218137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118313807499454502988993461 11091919453073859655218137)
          ·
            refine ⟨8318939589805394741413603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11091919453073859655218137 8318939589805394741413603)
            ·
              refine ⟨12478409384708092112120405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318939589805394741413603 12478409384708092112120405)
              ·
                refine ⟨146231359977047954438911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12478409384708092112120405 146231359977047954438911)
                ·
                  rfl

theorem cell23_7689183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 8].length) (baseStart_7689183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689183 prefixEnd_7689183 := by exact prefixLift 7689183
  have htrace : WordTrace (prefixWord ++ tailWord_7689183) baseStart_7689183 baseEnd_7689183 := by
    simpa [prefixWord, tailWord_7689183, baseEnd_7689183] using wordTrace_append hprefix tailTrace_7689183
  have hstable : (prefixWord ++ tailWord_7689183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689183).length < 2 ^ (prefixWord ++ tailWord_7689183).sum := by decide
  have hdescent : baseEnd_7689183 < baseStart_7689183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689227 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 3]
def baseStart_7689227 : Nat := 118140960795 + 7689227 * 2 ^ 59
def prefixEnd_7689227 : Nat := 4983230072969 + 3 ^ 40 * 7689227 * 2
def baseEnd_7689227 : Nat := 3948269312529092597700395

theorem tailTrace_7689227 : CollatzResearch.WordTrace tailWord_7689227 prefixEnd_7689227 3948269312529092597700395 := by
  unfold tailWord_7689227
  simp only [CollatzResearch.WordTrace]
  refine ⟨280449148514251269266289935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186966099009500846177526623 280449148514251269266289935)
  ·
    refine ⟨420673722771376903899434903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280449148514251269266289935 420673722771376903899434903)
    ·
      refine ⟨631010584157065355849152355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420673722771376903899434903 631010584157065355849152355)
      ·
        refine ⟨946515876235598033773728533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631010584157065355849152355 946515876235598033773728533)
        ·
          refine ⟨44367931698543657833143525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 946515876235598033773728533 44367931698543657833143525)
          ·
            refine ⟨8318987193476935843714411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44367931698543657833143525 8318987193476935843714411)
            ·
              refine ⟨12478480790215403765571617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8318987193476935843714411 12478480790215403765571617)
              ·
                refine ⟨9358860592661552824178713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12478480790215403765571617 9358860592661552824178713)
                ·
                  refine ⟨7019145444496164618134035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9358860592661552824178713 7019145444496164618134035)
                  ·
                    refine ⟨10528718166744246927201053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7019145444496164618134035 10528718166744246927201053)
                    ·
                      refine ⟨3948269312529092597700395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10528718166744246927201053 3948269312529092597700395)
                      ·
                        rfl

theorem cell23_7689227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 3].length) (baseStart_7689227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689227 prefixEnd_7689227 := by exact prefixLift 7689227
  have htrace : WordTrace (prefixWord ++ tailWord_7689227) baseStart_7689227 baseEnd_7689227 := by
    simpa [prefixWord, tailWord_7689227, baseEnd_7689227] using wordTrace_append hprefix tailTrace_7689227
  have hstable : (prefixWord ++ tailWord_7689227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689227).length < 2 ^ (prefixWord ++ tailWord_7689227).sum := by decide
  have hdescent : baseEnd_7689227 < baseStart_7689227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689233 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 3, 4, 2]
def baseStart_7689233 : Nat := 118140960795 + 7689233 * 2 ^ 59
def prefixEnd_7689233 : Nat := 4983230072969 + 3 ^ 40 * 7689233 * 2
def baseEnd_7689233 : Nat := 3948272393413019574225367

theorem tailTrace_7689233 : CollatzResearch.WordTrace tailWord_7689233 prefixEnd_7689233 3948272393413019574225367 := by
  unfold tailWord_7689233
  simp only [CollatzResearch.WordTrace]
  refine ⟨280449367352229532291008353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186966244901486354860672235 280449367352229532291008353)
  ·
    refine ⟨210337025514172149218256265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280449367352229532291008353 210337025514172149218256265)
    ·
      refine ⟨157752769135629111913692199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210337025514172149218256265 157752769135629111913692199)
      ·
        refine ⟨236629153703443667870538299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157752769135629111913692199 236629153703443667870538299)
        ·
          refine ⟨354943730555165501805807449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236629153703443667870538299 354943730555165501805807449)
          ·
            refine ⟨266207797916374126354355587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354943730555165501805807449 266207797916374126354355587)
            ·
              refine ⟨399311696874561189531533381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266207797916374126354355587 399311696874561189531533381)
              ·
                refine ⟨74870943163980223037162509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399311696874561189531533381 74870943163980223037162509)
                ·
                  refine ⟨28076603686492583638935941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74870943163980223037162509 28076603686492583638935941)
                  ·
                    refine ⟨5264363191217359432300489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28076603686492583638935941 5264363191217359432300489)
                    ·
                      refine ⟨3948272393413019574225367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264363191217359432300489 3948272393413019574225367)
                      ·
                        rfl

theorem cell23_7689233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_7689233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689233 prefixEnd_7689233 := by exact prefixLift 7689233
  have htrace : WordTrace (prefixWord ++ tailWord_7689233) baseStart_7689233 baseEnd_7689233 := by
    simpa [prefixWord, tailWord_7689233, baseEnd_7689233] using wordTrace_append hprefix tailTrace_7689233
  have hstable : (prefixWord ++ tailWord_7689233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689233).length < 2 ^ (prefixWord ++ tailWord_7689233).sum := by decide
  have hdescent : baseEnd_7689233 < baseStart_7689233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689244 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_7689244 : Nat := 118140960795 + 7689244 * 2 ^ 59
def prefixEnd_7689244 : Nat := 4983230072969 + 3 ^ 40 * 7689244 * 2
def baseEnd_7689244 : Nat := 3948278041700219031187817

theorem tailTrace_7689244 : CollatzResearch.WordTrace tailWord_7689244 prefixEnd_7689244 3948278041700219031187817 := by
  unfold tailWord_7689244
  simp only [CollatzResearch.WordTrace]
  refine ⟨140224884277594840584829393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186966512370126454113105857 140224884277594840584829393)
  ·
    refine ⟨105168663208196130438622045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140224884277594840584829393 105168663208196130438622045)
    ·
      refine ⟨39438248703073548914483267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105168663208196130438622045 39438248703073548914483267)
      ·
        refine ⟨59157373054610323371724901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39438248703073548914483267 59157373054610323371724901)
        ·
          refine ⟨11092007447739435632198419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59157373054610323371724901 11092007447739435632198419)
          ·
            refine ⟨16638011171609153448297629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092007447739435632198419 16638011171609153448297629)
            ·
              refine ⟨6239254189353432543111611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16638011171609153448297629 6239254189353432543111611)
              ·
                refine ⟨9358881284030148814667417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239254189353432543111611 9358881284030148814667417)
                ·
                  refine ⟨7019160963022611611000563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9358881284030148814667417 7019160963022611611000563)
                  ·
                    refine ⟨10528741444533917416500845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7019160963022611611000563 10528741444533917416500845)
                    ·
                      refine ⟨3948278041700219031187817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10528741444533917416500845 3948278041700219031187817)
                      ·
                        rfl

theorem cell23_7689244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_7689244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689244 prefixEnd_7689244 := by exact prefixLift 7689244
  have htrace : WordTrace (prefixWord ++ tailWord_7689244) baseStart_7689244 baseEnd_7689244 := by
    simpa [prefixWord, tailWord_7689244, baseEnd_7689244] using wordTrace_append hprefix tailTrace_7689244
  have hstable : (prefixWord ++ tailWord_7689244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689244).length < 2 ^ (prefixWord ++ tailWord_7689244).sum := by decide
  have hdescent : baseEnd_7689244 < baseStart_7689244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689270 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_7689270 : Nat := 118140960795 + 7689270 * 2 ^ 59
def prefixEnd_7689270 : Nat := 4983230072969 + 3 ^ 40 * 7689270 * 2
def baseEnd_7689270 : Nat := 3948291392197235929462697

theorem tailTrace_7689270 : CollatzResearch.WordTrace tailWord_7689270 prefixEnd_7689270 3948291392197235929462697 := by
  unfold tailWord_7689270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17528169803318467975631579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186967144568730325073403509 17528169803318467975631579)
  ·
    refine ⟨26292254704977701963447369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17528169803318467975631579 26292254704977701963447369)
    ·
      refine ⟨19719191028733276472585527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26292254704977701963447369 19719191028733276472585527)
      ·
        refine ⟨29578786543099914708878291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19719191028733276472585527 29578786543099914708878291)
        ·
          refine ⟨44368179814649872063317437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29578786543099914708878291 44368179814649872063317437)
          ·
            refine ⟨16638067430493702023744039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44368179814649872063317437 16638067430493702023744039)
            ·
              refine ⟨24957101145740553035616059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16638067430493702023744039 24957101145740553035616059)
              ·
                refine ⟨37435651718610829553424089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24957101145740553035616059 37435651718610829553424089)
                ·
                  refine ⟨28076738788958122165068067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37435651718610829553424089 28076738788958122165068067)
                  ·
                    refine ⟨42115108183437183247602101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28076738788958122165068067 42115108183437183247602101)
                    ·
                      refine ⟨3948291392197235929462697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42115108183437183247602101 3948291392197235929462697)
                      ·
                        rfl

theorem cell23_7689270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_7689270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689270 prefixEnd_7689270 := by exact prefixLift 7689270
  have htrace : WordTrace (prefixWord ++ tailWord_7689270) baseStart_7689270 baseEnd_7689270 := by
    simpa [prefixWord, tailWord_7689270, baseEnd_7689270] using wordTrace_append hprefix tailTrace_7689270
  have hstable : (prefixWord ++ tailWord_7689270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689270).length < 2 ^ (prefixWord ++ tailWord_7689270).sum := by decide
  have hdescent : baseEnd_7689270 < baseStart_7689270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689340 : List Nat := [2, 2, 2, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_7689340 : Nat := 118140960795 + 7689340 * 2 ^ 59
def prefixEnd_7689340 : Nat := 4983230072969 + 3 ^ 40 * 7689340 * 2
def baseEnd_7689340 : Nat := 3948327335843050655587375

theorem tailTrace_7689340 : CollatzResearch.WordTrace tailWord_7689340 prefixEnd_7689340 3948327335843050655587375 := by
  unfold tailWord_7689340
  simp only [CollatzResearch.WordTrace]
  refine ⟨140226634981420944782576737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186968846641894593043435649 140226634981420944782576737)
  ·
    refine ⟨105169976236065708586932553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140226634981420944782576737 105169976236065708586932553)
    ·
      refine ⟨78877482177049281440199415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105169976236065708586932553 78877482177049281440199415)
      ·
        refine ⟨118316223265573922160299123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78877482177049281440199415 118316223265573922160299123)
        ·
          refine ⟨177474334898360883240448685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118316223265573922160299123 177474334898360883240448685)
          ·
            refine ⟨66552875586885331215168257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177474334898360883240448685 66552875586885331215168257)
            ·
              refine ⟨49914656690163998411376193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66552875586885331215168257 49914656690163998411376193)
              ·
                refine ⟨37435992517622998808532145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49914656690163998411376193 37435992517622998808532145)
                ·
                  refine ⟨28076994388217249106399109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37435992517622998808532145 28076994388217249106399109)
                  ·
                    refine ⟨5264436447790734207449833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28076994388217249106399109 5264436447790734207449833)
                    ·
                      refine ⟨3948327335843050655587375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264436447790734207449833 3948327335843050655587375)
                      ·
                        rfl

theorem cell23_7689340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_7689340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689340 prefixEnd_7689340 := by exact prefixLift 7689340
  have htrace : WordTrace (prefixWord ++ tailWord_7689340) baseStart_7689340 baseEnd_7689340 := by
    simpa [prefixWord, tailWord_7689340, baseEnd_7689340] using wordTrace_append hprefix tailTrace_7689340
  have hstable : (prefixWord ++ tailWord_7689340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689340).length < 2 ^ (prefixWord ++ tailWord_7689340).sum := by decide
  have hdescent : baseEnd_7689340 < baseStart_7689340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689363 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 6]
def baseStart_7689363 : Nat := 118140960795 + 7689363 * 2 ^ 59
def prefixEnd_7689363 : Nat := 4983230072969 + 3 ^ 40 * 7689363 * 2
def baseEnd_7689363 : Nat := 438704349544233785066641

theorem tailTrace_7689363 : CollatzResearch.WordTrace tailWord_7689363 prefixEnd_7689363 438704349544233785066641 := by
  unfold tailWord_7689363
  simp only [CollatzResearch.WordTrace]
  refine ⟨280454108841758564493240743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186969405894505709662160495 280454108841758564493240743)
  ·
    refine ⟨420681163262637846739861115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280454108841758564493240743 420681163262637846739861115)
    ·
      refine ⟨631021744893956770109791673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420681163262637846739861115 631021744893956770109791673)
      ·
        refine ⟨473266308670467577582343755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631021744893956770109791673 473266308670467577582343755)
        ·
          refine ⟨709899463005701366373515633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473266308670467577582343755 709899463005701366373515633)
          ·
            refine ⟨532424597254276024780136725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709899463005701366373515633 532424597254276024780136725)
            ·
              refine ⟨24957402996294188661568909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 532424597254276024780136725 24957402996294188661568909)
              ·
                refine ⟨9359026123610320748088341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24957402996294188661568909 9359026123610320748088341)
                ·
                  refine ⟨438704349544233785066641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9359026123610320748088341 438704349544233785066641)
                  ·
                    rfl

theorem cell23_7689363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 6].length) (baseStart_7689363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689363 prefixEnd_7689363 := by exact prefixLift 7689363
  have htrace : WordTrace (prefixWord ++ tailWord_7689363) baseStart_7689363 baseEnd_7689363 := by
    simpa [prefixWord, tailWord_7689363, baseEnd_7689363] using wordTrace_append hprefix tailTrace_7689363
  have hstable : (prefixWord ++ tailWord_7689363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689363).length < 2 ^ (prefixWord ++ tailWord_7689363).sum := by decide
  have hdescent : baseEnd_7689363 < baseStart_7689363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689374 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_7689374 : Nat := 118140960795 + 7689374 * 2 ^ 59
def prefixEnd_7689374 : Nat := 4983230072969 + 3 ^ 40 * 7689374 * 2
def baseEnd_7689374 : Nat := 3948344794185303522562219

theorem tailTrace_7689374 : CollatzResearch.WordTrace tailWord_7689374 prefixEnd_7689374 3948344794185303522562219 := by
  unfold tailWord_7689374
  simp only [CollatzResearch.WordTrace]
  refine ⟨35056813755589839171486397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186969673363145808914594117 35056813755589839171486397)
  ·
    refine ⟨13146305158346189689307399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35056813755589839171486397 13146305158346189689307399)
    ·
      refine ⟨19719457737519284533961099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13146305158346189689307399 19719457737519284533961099)
      ·
        refine ⟨29579186606278926800941649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19719457737519284533961099 29579186606278926800941649)
        ·
          refine ⟨22184389954709195100706237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29579186606278926800941649 22184389954709195100706237)
          ·
            refine ⟨8319146233015948162764839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22184389954709195100706237 8319146233015948162764839)
            ·
              refine ⟨12478719349523922244147259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319146233015948162764839 12478719349523922244147259)
              ·
                refine ⟨18718079024285883366220889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12478719349523922244147259 18718079024285883366220889)
                ·
                  refine ⟨14038559268214412524665667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18718079024285883366220889 14038559268214412524665667)
                  ·
                    refine ⟨21057838902321618786998501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14038559268214412524665667 21057838902321618786998501)
                    ·
                      refine ⟨3948344794185303522562219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21057838902321618786998501 3948344794185303522562219)
                      ·
                        rfl

theorem cell23_7689374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_7689374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689374 prefixEnd_7689374 := by exact prefixLift 7689374
  have htrace : WordTrace (prefixWord ++ tailWord_7689374) baseStart_7689374 baseEnd_7689374 := by
    simpa [prefixWord, tailWord_7689374, baseEnd_7689374] using wordTrace_append hprefix tailTrace_7689374
  have hstable : (prefixWord ++ tailWord_7689374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689374).length < 2 ^ (prefixWord ++ tailWord_7689374).sum := by decide
  have hdescent : baseEnd_7689374 < baseStart_7689374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689423 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 1, 6]
def baseStart_7689423 : Nat := 118140960795 + 7689423 * 2 ^ 59
def prefixEnd_7689423 : Nat := 4983230072969 + 3 ^ 40 * 7689423 * 2
def baseEnd_7689423 : Nat := 1316123318245791276949831

theorem tailTrace_7689423 : CollatzResearch.WordTrace tailWord_7689423 prefixEnd_7689423 1316123318245791276949831 := by
  unfold tailWord_7689423
  simp only [CollatzResearch.WordTrace]
  refine ⟨280456297221541194740424923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186970864814360796493616615 280456297221541194740424923)
  ·
    refine ⟨420684445832311792110637385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280456297221541194740424923 420684445832311792110637385)
    ·
      refine ⟨315513334374233844082978039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420684445832311792110637385 315513334374233844082978039)
      ·
        refine ⟨473270001561350766124467059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315513334374233844082978039 473270001561350766124467059)
        ·
          refine ⟨709905002342026149186700589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473270001561350766124467059 709905002342026149186700589)
          ·
            refine ⟨266214375878259805945012721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 709905002342026149186700589 266214375878259805945012721)
            ·
              refine ⟨199660781908694854458759541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266214375878259805945012721 199660781908694854458759541)
              ·
                refine ⟨18718198303940142605508707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199660781908694854458759541 18718198303940142605508707)
                ·
                  refine ⟨28077297455910213908263061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18718198303940142605508707 28077297455910213908263061)
                  ·
                    refine ⟨1316123318245791276949831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28077297455910213908263061 1316123318245791276949831)
                    ·
                      rfl

theorem cell23_7689423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_7689423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689423 prefixEnd_7689423 := by exact prefixLift 7689423
  have htrace : WordTrace (prefixWord ++ tailWord_7689423) baseStart_7689423 baseEnd_7689423 := by
    simpa [prefixWord, tailWord_7689423, baseEnd_7689423] using wordTrace_append hprefix tailTrace_7689423
  have hstable : (prefixWord ++ tailWord_7689423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689423).length < 2 ^ (prefixWord ++ tailWord_7689423).sum := by decide
  have hdescent : baseEnd_7689423 < baseStart_7689423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689433 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_7689433 : Nat := 118140960795 + 7689433 * 2 ^ 59
def prefixEnd_7689433 : Nat := 4983230072969 + 3 ^ 40 * 7689433 * 2
def baseEnd_7689433 : Nat := 3948375089543918791724447

theorem tailTrace_7689433 : CollatzResearch.WordTrace tailWord_7689433 prefixEnd_7689433 3948375089543918791724447 := by
  unfold tailWord_7689433
  simp only [CollatzResearch.WordTrace]
  refine ⟨280456661951504966448288953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186971107967669977632192635 280456661951504966448288953)
  ·
    refine ⟨210342496463628724836216715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280456661951504966448288953 210342496463628724836216715)
    ·
      refine ⟨315513744695443087254325073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210342496463628724836216715 315513744695443087254325073)
      ·
        refine ⟨236635308521582315440743805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315513744695443087254325073 236635308521582315440743805)
        ·
          refine ⟨88738240695593368290278927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236635308521582315440743805 88738240695593368290278927)
          ·
            refine ⟨133107361043390052435418391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88738240695593368290278927 133107361043390052435418391)
            ·
              refine ⟨199661041565085078653127587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133107361043390052435418391 199661041565085078653127587)
              ·
                refine ⟨299491562347627617979691381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199661041565085078653127587 299491562347627617979691381)
                ·
                  refine ⟨28077333970090089185596067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 299491562347627617979691381 28077333970090089185596067)
                  ·
                    refine ⟨42116000955135133778394101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28077333970090089185596067 42116000955135133778394101)
                    ·
                      refine ⟨3948375089543918791724447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42116000955135133778394101 3948375089543918791724447)
                      ·
                        rfl

theorem cell23_7689433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_7689433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689433 prefixEnd_7689433 := by exact prefixLift 7689433
  have htrace : WordTrace (prefixWord ++ tailWord_7689433) baseStart_7689433 baseEnd_7689433 := by
    simpa [prefixWord, tailWord_7689433, baseEnd_7689433] using wordTrace_append hprefix tailTrace_7689433
  have hstable : (prefixWord ++ tailWord_7689433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689433).length < 2 ^ (prefixWord ++ tailWord_7689433).sum := by decide
  have hdescent : baseEnd_7689433 < baseStart_7689433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689440 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 4, 4]
def baseStart_7689440 : Nat := 118140960795 + 7689440 * 2 ^ 59
def prefixEnd_7689440 : Nat := 4983230072969 + 3 ^ 40 * 7689440 * 2
def baseEnd_7689440 : Nat := 1316126227969500088112305

theorem tailTrace_7689440 : CollatzResearch.WordTrace tailWord_7689440 prefixEnd_7689440 1316126227969500088112305 := by
  unfold tailWord_7689440
  simp only [CollatzResearch.WordTrace]
  refine ⟨140228458631239803321896887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186971278174986404429195849 140228458631239803321896887)
  ·
    refine ⟨210342687946859704982845331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140228458631239803321896887 210342687946859704982845331)
    ·
      refine ⟨315514031920289557474267997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210342687946859704982845331 315514031920289557474267997)
      ·
        refine ⟨118317761970108584052850499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315514031920289557474267997 118317761970108584052850499)
        ·
          refine ⟨177476642955162876079275749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118317761970108584052850499 177476642955162876079275749)
          ·
            refine ⟨33276870554093039264864203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177476642955162876079275749 33276870554093039264864203)
            ·
              refine ⟨49915305831139558897296305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33276870554093039264864203 49915305831139558897296305)
              ·
                refine ⟨37436479373354669172972229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49915305831139558897296305 37436479373354669172972229)
                ·
                  refine ⟨7019339882504000469932293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37436479373354669172972229 7019339882504000469932293)
                  ·
                    refine ⟨1316126227969500088112305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7019339882504000469932293 1316126227969500088112305)
                    ·
                      rfl

theorem cell23_7689440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 4].length) (baseStart_7689440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689440 prefixEnd_7689440 := by exact prefixLift 7689440
  have htrace : WordTrace (prefixWord ++ tailWord_7689440) baseStart_7689440 baseEnd_7689440 := by
    simpa [prefixWord, tailWord_7689440, baseEnd_7689440] using wordTrace_append hprefix tailTrace_7689440
  have hstable : (prefixWord ++ tailWord_7689440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689440).length < 2 ^ (prefixWord ++ tailWord_7689440).sum := by decide
  have hdescent : baseEnd_7689440 < baseStart_7689440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689441 : List Nat := [1, 2, 3, 1, 3, 4, 1, 3, 1, 1, 3]
def baseStart_7689441 : Nat := 118140960795 + 7689441 * 2 ^ 59
def prefixEnd_7689441 : Nat := 4983230072969 + 3 ^ 40 * 7689441 * 2
def baseEnd_7689441 : Nat := 3948379197389154760424411

theorem tailTrace_7689441 : CollatzResearch.WordTrace tailWord_7689441 prefixEnd_7689441 3948379197389154760424411 := by
  unfold tailWord_7689441
  simp only [CollatzResearch.WordTrace]
  refine ⟨280456953735475983814580177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186971302490317322543053451 280456953735475983814580177)
  ·
    refine ⟨210342715301606987860935133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280456953735475983814580177 210342715301606987860935133)
    ·
      refine ⟨78878518238102620447850675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210342715301606987860935133 78878518238102620447850675)
      ·
        refine ⟨118317777357153930671776013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78878518238102620447850675 118317777357153930671776013)
        ·
          refine ⟨44369166508932724001916005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118317777357153930671776013 44369166508932724001916005)
          ·
            refine ⟨8319218720424885750359251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44369166508932724001916005 8319218720424885750359251)
            ·
              refine ⟨12478828080637328625538877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319218720424885750359251 12478828080637328625538877)
              ·
                refine ⟨4679560530238998234577079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12478828080637328625538877 4679560530238998234577079)
                ·
                  refine ⟨7019340795358497351865619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679560530238998234577079 7019340795358497351865619)
                  ·
                    refine ⟨10529011193037746027798429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7019340795358497351865619 10529011193037746027798429)
                    ·
                      refine ⟨3948379197389154760424411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10529011193037746027798429 3948379197389154760424411)
                      ·
                        rfl

theorem cell23_7689441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_7689441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689441 prefixEnd_7689441 := by exact prefixLift 7689441
  have htrace : WordTrace (prefixWord ++ tailWord_7689441) baseStart_7689441 baseEnd_7689441 := by
    simpa [prefixWord, tailWord_7689441, baseEnd_7689441] using wordTrace_append hprefix tailTrace_7689441
  have hstable : (prefixWord ++ tailWord_7689441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689441).length < 2 ^ (prefixWord ++ tailWord_7689441).sum := by decide
  have hdescent : baseEnd_7689441 < baseStart_7689441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689450 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_7689450 : Nat := 118140960795 + 7689450 * 2 ^ 59
def prefixEnd_7689450 : Nat := 4983230072969 + 3 ^ 40 * 7689450 * 2
def baseEnd_7689450 : Nat := 3948383818715045225211869

theorem tailTrace_7689450 : CollatzResearch.WordTrace tailWord_7689450 prefixEnd_7689450 3948383818715045225211869 := by
  unfold tailWord_7689450
  simp only [CollatzResearch.WordTrace]
  refine ⟨70114320498110844587914451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186971521328295585567771869 70114320498110844587914451)
  ·
    refine ⟨105171480747166266881871677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70114320498110844587914451 105171480747166266881871677)
    ·
      refine ⟨39439305280187350080701879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105171480747166266881871677 39439305280187350080701879)
      ·
        refine ⟨59158957920281025121052819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39439305280187350080701879 59158957920281025121052819)
        ·
          refine ⟨88738436880421537681579229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59158957920281025121052819 88738436880421537681579229)
          ·
            refine ⟨33276913830158076630592211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88738436880421537681579229 33276913830158076630592211)
            ·
              refine ⟨49915370745237114945888317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33276913830158076630592211 49915370745237114945888317)
              ·
                refine ⟨18718264029463918104708119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49915370745237114945888317 18718264029463918104708119)
                ·
                  refine ⟨28077396044195877157062179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18718264029463918104708119 28077396044195877157062179)
                  ·
                    refine ⟨42116094066293815735593269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28077396044195877157062179 42116094066293815735593269)
                    ·
                      refine ⟨3948383818715045225211869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42116094066293815735593269 3948383818715045225211869)
                      ·
                        rfl

theorem cell23_7689450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_7689450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689450 prefixEnd_7689450 := by exact prefixLift 7689450
  have htrace : WordTrace (prefixWord ++ tailWord_7689450) baseStart_7689450 baseEnd_7689450 := by
    simpa [prefixWord, tailWord_7689450, baseEnd_7689450] using wordTrace_append hprefix tailTrace_7689450
  have hstable : (prefixWord ++ tailWord_7689450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689450).length < 2 ^ (prefixWord ++ tailWord_7689450).sum := by decide
  have hdescent : baseEnd_7689450 < baseStart_7689450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689458 : List Nat := [3, 2, 1, 3, 3, 1, 3, 2, 1, 1, 3]
def baseStart_7689458 : Nat := 118140960795 + 7689458 * 2 ^ 59
def prefixEnd_7689458 : Nat := 4983230072969 + 3 ^ 40 * 7689458 * 2
def baseEnd_7689458 : Nat := 3948387926560281193911833

theorem tailTrace_7689458 : CollatzResearch.WordTrace tailWord_7689458 prefixEnd_7689458 3948387926560281193911833 := by
  unfold tailWord_7689458
  simp only [CollatzResearch.WordTrace]
  refine ⟨70114393444103598929487257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186971715850942930478632685 70114393444103598929487257)
  ·
    refine ⟨52585795083077699197115443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70114393444103598929487257 52585795083077699197115443)
    ·
      refine ⟨78878692624616548795673165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52585795083077699197115443 78878692624616548795673165)
      ·
        refine ⟨29579509734231205798377437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78878692624616548795673165 29579509734231205798377437)
        ·
          refine ⟨11092316150336702174391539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29579509734231205798377437 11092316150336702174391539)
          ·
            refine ⟨16638474225505053261587309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092316150336702174391539 16638474225505053261587309)
            ·
              refine ⟨6239427834564394973095241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16638474225505053261587309 6239427834564394973095241)
              ·
                refine ⟨4679570875923296229821431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239427834564394973095241 4679570875923296229821431)
                ·
                  refine ⟨7019356313884944344732147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679570875923296229821431 7019356313884944344732147)
                  ·
                    refine ⟨10529034470827416517098221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7019356313884944344732147 10529034470827416517098221)
                    ·
                      refine ⟨3948387926560281193911833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10529034470827416517098221 3948387926560281193911833)
                      ·
                        rfl

theorem cell23_7689458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_7689458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689458 prefixEnd_7689458 := by exact prefixLift 7689458
  have htrace : WordTrace (prefixWord ++ tailWord_7689458) baseStart_7689458 baseEnd_7689458 := by
    simpa [prefixWord, tailWord_7689458, baseEnd_7689458] using wordTrace_append hprefix tailTrace_7689458
  have hstable : (prefixWord ++ tailWord_7689458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689458).length < 2 ^ (prefixWord ++ tailWord_7689458).sum := by decide
  have hdescent : baseEnd_7689458 < baseStart_7689458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689470 : List Nat := [4, 2, 2, 1, 1, 2, 1, 10]
def baseStart_7689470 : Nat := 118140960795 + 7689470 * 2 ^ 59
def prefixEnd_7689470 : Nat := 4983230072969 + 3 ^ 40 * 7689470 * 2
def baseEnd_7689470 : Nat := 146236818086227227665251

theorem tailTrace_7689470 : CollatzResearch.WordTrace tailWord_7689470 prefixEnd_7689470 146236818086227227665251 := by
  unfold tailWord_7689470
  simp only [CollatzResearch.WordTrace]
  refine ⟨35057251431546365220923233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186972007634913947844923909 35057251431546365220923233)
  ·
    refine ⟨26292938573659773915692425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35057251431546365220923233 26292938573659773915692425)
    ·
      refine ⟨19719703930244830436769319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26292938573659773915692425 19719703930244830436769319)
      ·
        refine ⟨29579555895367245655153979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19719703930244830436769319 29579555895367245655153979)
        ·
          refine ⟨44369333843050868482730969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29579555895367245655153979 44369333843050868482730969)
          ·
            refine ⟨33277000382288151362048227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44369333843050868482730969 33277000382288151362048227)
            ·
              refine ⟨49915500573432227043072341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33277000382288151362048227 49915500573432227043072341)
              ·
                refine ⟨146236818086227227665251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49915500573432227043072341 146236818086227227665251)
                ·
                  rfl

theorem cell23_7689470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_7689470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689470 prefixEnd_7689470 := by exact prefixLift 7689470
  have htrace : WordTrace (prefixWord ++ tailWord_7689470) baseStart_7689470 baseEnd_7689470 := by
    simpa [prefixWord, tailWord_7689470, baseEnd_7689470] using wordTrace_append hprefix tailTrace_7689470
  have hstable : (prefixWord ++ tailWord_7689470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689470).length < 2 ^ (prefixWord ++ tailWord_7689470).sum := by decide
  have hdescent : baseEnd_7689470 < baseStart_7689470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689484 : List Nat := [2, 2, 1, 2, 2, 5, 1, 2, 1, 2, 3]
def baseStart_7689484 : Nat := 118140960795 + 7689484 * 2 ^ 59
def prefixEnd_7689484 : Nat := 4983230072969 + 3 ^ 40 * 7689484 * 2
def baseEnd_7689484 : Nat := 3948401277057298092186713

theorem tailTrace_7689484 : CollatzResearch.WordTrace tailWord_7689484 prefixEnd_7689484 3948401277057298092186713 := by
  unfold tailWord_7689484
  simp only [CollatzResearch.WordTrace]
  refine ⟨140229261037160101079197753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186972348049546801438930337 140229261037160101079197753)
  ·
    refine ⟨105171945777870075809398315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140229261037160101079197753 105171945777870075809398315)
    ·
      refine ⟨157757918666805113714097473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105171945777870075809398315 157757918666805113714097473)
      ·
        refine ⟨118318439000103835285573105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157757918666805113714097473 118318439000103835285573105)
        ·
          refine ⟨88738829250077876464179829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118318439000103835285573105 88738829250077876464179829)
          ·
            refine ⟨8319265242194800918516859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88738829250077876464179829 8319265242194800918516859)
            ·
              refine ⟨12478897863292201377775289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319265242194800918516859 12478897863292201377775289)
              ·
                refine ⟨9359173397469151033331467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12478897863292201377775289 9359173397469151033331467)
                ·
                  refine ⟨14038760096203726549997201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359173397469151033331467 14038760096203726549997201)
                  ·
                    refine ⟨10529070072152794912497901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14038760096203726549997201 10529070072152794912497901)
                    ·
                      refine ⟨3948401277057298092186713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10529070072152794912497901 3948401277057298092186713)
                      ·
                        rfl

theorem cell23_7689484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_7689484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689484 prefixEnd_7689484 := by exact prefixLift 7689484
  have htrace : WordTrace (prefixWord ++ tailWord_7689484) baseStart_7689484 baseEnd_7689484 := by
    simpa [prefixWord, tailWord_7689484, baseEnd_7689484] using wordTrace_append hprefix tailTrace_7689484
  have hstable : (prefixWord ++ tailWord_7689484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689484).length < 2 ^ (prefixWord ++ tailWord_7689484).sum := by decide
  have hdescent : baseEnd_7689484 < baseStart_7689484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689501 : List Nat := [1, 4, 2, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_7689501 : Nat := 118140960795 + 7689501 * 2 ^ 59
def prefixEnd_7689501 : Nat := 4983230072969 + 3 ^ 40 * 7689501 * 2
def baseEnd_7689501 : Nat := 3948410006228424525674135

theorem tailTrace_7689501 : CollatzResearch.WordTrace tailWord_7689501 prefixEnd_7689501 3948410006228424525674135 := by
  unfold tailWord_7689501
  simp only [CollatzResearch.WordTrace]
  refine ⟨280459142115258614061764357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186972761410172409374509571 280459142115258614061764357)
  ·
    refine ⟨52586089146610990136580817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280459142115258614061764357 52586089146610990136580817)
    ·
      refine ⟨39439566859958242602435613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52586089146610990136580817 39439566859958242602435613)
      ·
        refine ⟨14789837572484340975913355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39439566859958242602435613 14789837572484340975913355)
        ·
          refine ⟨22184756358726511463870033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14789837572484340975913355 22184756358726511463870033)
          ·
            refine ⟨16638567269044883597902525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22184756358726511463870033 16638567269044883597902525)
            ·
              refine ⟨6239462725891831349213447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16638567269044883597902525 6239462725891831349213447)
              ·
                refine ⟨9359194088837747023820171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239462725891831349213447 9359194088837747023820171)
                ·
                  refine ⟨14038791133256620535730257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359194088837747023820171 14038791133256620535730257)
                  ·
                    refine ⟨10529093349942465401797693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14038791133256620535730257 10529093349942465401797693)
                    ·
                      refine ⟨3948410006228424525674135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10529093349942465401797693 3948410006228424525674135)
                      ·
                        rfl

theorem cell23_7689501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_7689501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689501 prefixEnd_7689501 := by exact prefixLift 7689501
  have htrace : WordTrace (prefixWord ++ tailWord_7689501) baseStart_7689501 baseEnd_7689501 := by
    simpa [prefixWord, tailWord_7689501, baseEnd_7689501] using wordTrace_append hprefix tailTrace_7689501
  have hstable : (prefixWord ++ tailWord_7689501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689501).length < 2 ^ (prefixWord ++ tailWord_7689501).sum := by decide
  have hdescent : baseEnd_7689501 < baseStart_7689501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689517 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_7689517 : Nat := 118140960795 + 7689517 * 2 ^ 59
def prefixEnd_7689517 : Nat := 4983230072969 + 3 ^ 40 * 7689517 * 2
def baseEnd_7689517 : Nat := 1316139407306298821024687

theorem tailTrace_7689517 : CollatzResearch.WordTrace tailWord_7689517 prefixEnd_7689517 1316139407306298821024687 := by
  unfold tailWord_7689517
  simp only [CollatzResearch.WordTrace]
  refine ⟨280459725683200648794346805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186973150455467099196231203 280459725683200648794346805)
  ·
    refine ⟨26293099282800060824470013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280459725683200648794346805 26293099282800060824470013)
    ·
      refine ⟨9859912231050022809176255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26293099282800060824470013 9859912231050022809176255)
      ·
        refine ⟨14789868346575034213764383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9859912231050022809176255 14789868346575034213764383)
        ·
          refine ⟨22184802519862551320646575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14789868346575034213764383 22184802519862551320646575)
          ·
            refine ⟨33277203779793826980969863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22184802519862551320646575 33277203779793826980969863)
            ·
              refine ⟨49915805669690740471454795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33277203779793826980969863 49915805669690740471454795)
              ·
                refine ⟨74873708504536110707182193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49915805669690740471454795 74873708504536110707182193)
                ·
                  refine ⟨56155281378402083030386645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74873708504536110707182193 56155281378402083030386645)
                  ·
                    refine ⟨1316139407306298821024687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56155281378402083030386645 1316139407306298821024687)
                    ·
                      rfl

theorem cell23_7689517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_7689517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689517 prefixEnd_7689517 := by exact prefixLift 7689517
  have htrace : WordTrace (prefixWord ++ tailWord_7689517) baseStart_7689517 baseEnd_7689517 := by
    simpa [prefixWord, tailWord_7689517, baseEnd_7689517] using wordTrace_append hprefix tailTrace_7689517
  have hstable : (prefixWord ++ tailWord_7689517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689517).length < 2 ^ (prefixWord ++ tailWord_7689517).sum := by decide
  have hdescent : baseEnd_7689517 < baseStart_7689517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689524 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_7689524 : Nat := 118140960795 + 7689524 * 2 ^ 59
def prefixEnd_7689524 : Nat := 4983230072969 + 3 ^ 40 * 7689524 * 2
def baseEnd_7689524 : Nat := 3948421816283477935686529

theorem tailTrace_7689524 : CollatzResearch.WordTrace tailWord_7689524 prefixEnd_7689524 3948421816283477935686529 := by
  unfold tailWord_7689524
  simp only [CollatzResearch.WordTrace]
  refine ⟨140229990497087644494925813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186973320662783525993234417 140229990497087644494925813)
  ·
    refine ⟨13146561609101966671399295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140229990497087644494925813 13146561609101966671399295)
    ·
      refine ⟨19719842413652950007098943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13146561609101966671399295 19719842413652950007098943)
      ·
        refine ⟨29579763620479425010648415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19719842413652950007098943 29579763620479425010648415)
        ·
          refine ⟨44369645430719137515972623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29579763620479425010648415 44369645430719137515972623)
          ·
            refine ⟨66554468146078706273958935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44369645430719137515972623 66554468146078706273958935)
            ·
              refine ⟨99831702219118059410938403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66554468146078706273958935 99831702219118059410938403)
              ·
                refine ⟨149747553328677089116407605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99831702219118059410938403 149747553328677089116407605)
                ·
                  refine ⟨14038833124563477104663213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149747553328677089116407605 14038833124563477104663213)
                  ·
                    refine ⟨5264562421711303914248705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14038833124563477104663213 5264562421711303914248705)
                    ·
                      refine ⟨3948421816283477935686529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264562421711303914248705 3948421816283477935686529)
                      ·
                        rfl

theorem cell23_7689524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_7689524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689524 prefixEnd_7689524 := by exact prefixLift 7689524
  have htrace : WordTrace (prefixWord ++ tailWord_7689524) baseStart_7689524 baseEnd_7689524 := by
    simpa [prefixWord, tailWord_7689524, baseEnd_7689524] using wordTrace_append hprefix tailTrace_7689524
  have hstable : (prefixWord ++ tailWord_7689524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689524).length < 2 ^ (prefixWord ++ tailWord_7689524).sum := by decide
  have hdescent : baseEnd_7689524 < baseStart_7689524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689530 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_7689530 : Nat := 118140960795 + 7689530 * 2 ^ 59
def prefixEnd_7689530 : Nat := 4983230072969 + 3 ^ 40 * 7689530 * 2
def baseEnd_7689530 : Nat := 1316141632389134970737167

theorem tailTrace_7689530 : CollatzResearch.WordTrace tailWord_7689530 prefixEnd_7689530 1316141632389134970737167 := by
  unfold tailWord_7689530
  simp only [CollatzResearch.WordTrace]
  refine ⟨70115049958038388003642511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186973466554769034676380029 70115049958038388003642511)
  ·
    refine ⟨105172574937057582005463767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70115049958038388003642511 105172574937057582005463767)
    ·
      refine ⟨157758862405586373008195651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105172574937057582005463767 157758862405586373008195651)
      ·
        refine ⟨236638293608379559512293477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157758862405586373008195651 236638293608379559512293477)
        ·
          refine ⟨44369680051571167408555027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236638293608379559512293477 44369680051571167408555027)
          ·
            refine ⟨66554520077356751112832541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44369680051571167408555027 66554520077356751112832541)
            ·
              refine ⟨24957945029008781667312203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66554520077356751112832541 24957945029008781667312203)
              ·
                refine ⟨37436917543513172500968305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24957945029008781667312203 37436917543513172500968305)
                ·
                  refine ⟨28077688157634879375726229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37436917543513172500968305 28077688157634879375726229)
                  ·
                    refine ⟨1316141632389134970737167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28077688157634879375726229 1316141632389134970737167)
                    ·
                      rfl

theorem cell23_7689530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_7689530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689530 prefixEnd_7689530 := by exact prefixLift 7689530
  have htrace : WordTrace (prefixWord ++ tailWord_7689530) baseStart_7689530 baseEnd_7689530 := by
    simpa [prefixWord, tailWord_7689530, baseEnd_7689530] using wordTrace_append hprefix tailTrace_7689530
  have hstable : (prefixWord ++ tailWord_7689530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689530).length < 2 ^ (prefixWord ++ tailWord_7689530).sum := by decide
  have hdescent : baseEnd_7689530 < baseStart_7689530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689550 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_7689550 : Nat := 118140960795 + 7689550 * 2 ^ 59
def prefixEnd_7689550 : Nat := 4983230072969 + 3 ^ 40 * 7689550 * 2
def baseEnd_7689550 : Nat := 3948435166780494833961409

theorem tailTrace_7689550 : CollatzResearch.WordTrace tailWord_7689550 prefixEnd_7689550 3948435166780494833961409 := by
  unfold tailWord_7689550
  simp only [CollatzResearch.WordTrace]
  refine ⟨35057616161510136928787263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186973952861387396953532069 35057616161510136928787263)
  ·
    refine ⟨52586424242265205393180895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35057616161510136928787263 52586424242265205393180895)
    ·
      refine ⟨78879636363397808089771343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52586424242265205393180895 78879636363397808089771343)
      ·
        refine ⟨118319454545096712134657015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78879636363397808089771343 118319454545096712134657015)
        ·
          refine ⟨177479181817645068201985523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118319454545096712134657015 177479181817645068201985523)
          ·
            refine ⟨266218772726467602302978285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177479181817645068201985523 266218772726467602302978285)
            ·
              refine ⟨99832039772425350863616857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266218772726467602302978285 99832039772425350863616857)
              ·
                refine ⟨74874029829319013147712643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99832039772425350863616857 74874029829319013147712643)
                ·
                  refine ⟨112311044743978519721568965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74874029829319013147712643 112311044743978519721568965)
                  ·
                    refine ⟨21058320889495972447794181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112311044743978519721568965 21058320889495972447794181)
                    ·
                      refine ⟨3948435166780494833961409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21058320889495972447794181 3948435166780494833961409)
                      ·
                        rfl

theorem cell23_7689550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_7689550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689550 prefixEnd_7689550 := by exact prefixLift 7689550
  have htrace : WordTrace (prefixWord ++ tailWord_7689550) baseStart_7689550 baseEnd_7689550 := by
    simpa [prefixWord, tailWord_7689550, baseEnd_7689550] using wordTrace_append hprefix tailTrace_7689550
  have hstable : (prefixWord ++ tailWord_7689550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689550).length < 2 ^ (prefixWord ++ tailWord_7689550).sum := by decide
  have hdescent : baseEnd_7689550 < baseStart_7689550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689554 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_7689554 : Nat := 118140960795 + 7689554 * 2 ^ 59
def prefixEnd_7689554 : Nat := 4983230072969 + 3 ^ 40 * 7689554 * 2
def baseEnd_7689554 : Nat := 3948437220703112818311391

theorem tailTrace_7689554 : CollatzResearch.WordTrace tailWord_7689554 prefixEnd_7689554 3948437220703112818311391 := by
  unfold tailWord_7689554
  simp only [CollatzResearch.WordTrace]
  refine ⟨70115268796016651028360929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186974050122711069408962477 70115268796016651028360929)
  ·
    refine ⟨52586451597012488271270697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70115268796016651028360929 52586451597012488271270697)
    ·
      refine ⟨39439838697759366203453023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52586451597012488271270697 39439838697759366203453023)
      ·
        refine ⟨59159758046639049305179535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39439838697759366203453023 59159758046639049305179535)
        ·
          refine ⟨88739637069958573957769303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59159758046639049305179535 88739637069958573957769303)
          ·
            refine ⟨133109455604937860936653955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88739637069958573957769303 133109455604937860936653955)
            ·
              refine ⟨199664183407406791404980933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133109455604937860936653955 199664183407406791404980933)
              ·
                refine ⟨37437034388888773388433925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199664183407406791404980933 37437034388888773388433925)
                ·
                  refine ⟨7019443947916645010331361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37437034388888773388433925 7019443947916645010331361)
                  ·
                    refine ⟨5264582960937483757748521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7019443947916645010331361 5264582960937483757748521)
                    ·
                      refine ⟨3948437220703112818311391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264582960937483757748521 3948437220703112818311391)
                      ·
                        rfl

theorem cell23_7689554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_7689554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689554 prefixEnd_7689554 := by exact prefixLift 7689554
  have htrace : WordTrace (prefixWord ++ tailWord_7689554) baseStart_7689554 baseEnd_7689554 := by
    simpa [prefixWord, tailWord_7689554, baseEnd_7689554] using wordTrace_append hprefix tailTrace_7689554
  have hstable : (prefixWord ++ tailWord_7689554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689554).length < 2 ^ (prefixWord ++ tailWord_7689554).sum := by decide
  have hdescent : baseEnd_7689554 < baseStart_7689554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689571 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 2, 2, 2]
def baseStart_7689571 : Nat := 118140960795 + 7689571 * 2 ^ 59
def prefixEnd_7689571 : Nat := 4983230072969 + 3 ^ 40 * 7689571 * 2
def baseEnd_7689571 : Nat := 3948445949874239251798813

theorem tailTrace_7689571 : CollatzResearch.WordTrace tailWord_7689571 prefixEnd_7689571 3948445949874239251798813 := by
  unfold tailWord_7689571
  simp only [CollatzResearch.WordTrace]
  refine ⟨280461695225005016016812567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186974463483336677344541711 280461695225005016016812567)
  ·
    refine ⟨420692542837507524025218851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280461695225005016016812567 420692542837507524025218851)
    ·
      refine ⟨631038814256261286037828277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420692542837507524025218851 631038814256261286037828277)
      ·
        refine ⟨59159888836524495566046401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 631038814256261286037828277 59159888836524495566046401)
        ·
          refine ⟨44369916627393371674534801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59159888836524495566046401 44369916627393371674534801)
          ·
            refine ⟨33277437470545028755901101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44369916627393371674534801 33277437470545028755901101)
            ·
              refine ⟨12479039051454385783462913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33277437470545028755901101 12479039051454385783462913)
              ·
                refine ⟨9359279288590789337597185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12479039051454385783462913 9359279288590789337597185)
                ·
                  refine ⟨7019459466443092003197889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9359279288590789337597185 7019459466443092003197889)
                  ·
                    refine ⟨5264594599832319002398417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7019459466443092003197889 5264594599832319002398417)
                    ·
                      refine ⟨3948445949874239251798813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264594599832319002398417 3948445949874239251798813)
                      ·
                        rfl

theorem cell23_7689571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_7689571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689571 prefixEnd_7689571 := by exact prefixLift 7689571
  have htrace : WordTrace (prefixWord ++ tailWord_7689571) baseStart_7689571 baseEnd_7689571 := by
    simpa [prefixWord, tailWord_7689571, baseEnd_7689571] using wordTrace_append hprefix tailTrace_7689571
  have hstable : (prefixWord ++ tailWord_7689571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689571).length < 2 ^ (prefixWord ++ tailWord_7689571).sum := by decide
  have hdescent : baseEnd_7689571 < baseStart_7689571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689624 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 2, 5]
def baseStart_7689624 : Nat := 118140960795 + 7689624 * 2 ^ 59
def prefixEnd_7689624 : Nat := 4983230072969 + 3 ^ 40 * 7689624 * 2
def baseEnd_7689624 : Nat := 1316157721449642514812023

theorem tailTrace_7689624 : CollatzResearch.WordTrace tailWord_7689624 prefixEnd_7689624 1316157721449642514812023 := by
  unfold tailWord_7689624
  simp only [CollatzResearch.WordTrace]
  refine ⟨140231814146906503034245963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186975752195875337378994617 140231814146906503034245963)
  ·
    refine ⟨210347721220359754551368945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140231814146906503034245963 210347721220359754551368945)
    ·
      refine ⟨157760790915269815913526709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210347721220359754551368945 157760790915269815913526709)
      ·
        refine ⟨14790074148306545241893129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157760790915269815913526709 14790074148306545241893129)
        ·
          refine ⟨11092555611229908931419847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14790074148306545241893129 11092555611229908931419847)
          ·
            refine ⟨16638833416844863397129771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092555611229908931419847 16638833416844863397129771)
            ·
              refine ⟨24958250125267295095694657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16638833416844863397129771 24958250125267295095694657)
              ·
                refine ⟨18718687593950471321770993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24958250125267295095694657 18718687593950471321770993)
                ·
                  refine ⟨14039015695462853491328245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18718687593950471321770993 14039015695462853491328245)
                  ·
                    refine ⟨1316157721449642514812023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14039015695462853491328245 1316157721449642514812023)
                    ·
                      rfl

theorem cell23_7689624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_7689624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689624 prefixEnd_7689624 := by exact prefixLift 7689624
  have htrace : WordTrace (prefixWord ++ tailWord_7689624) baseStart_7689624 baseEnd_7689624 := by
    simpa [prefixWord, tailWord_7689624, baseEnd_7689624] using wordTrace_append hprefix tailTrace_7689624
  have hstable : (prefixWord ++ tailWord_7689624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689624).length < 2 ^ (prefixWord ++ tailWord_7689624).sum := by decide
  have hdescent : baseEnd_7689624 < baseStart_7689624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689628 : List Nat := [2, 2, 3, 4, 1, 1, 3, 2, 5]
def baseStart_7689628 : Nat := 118140960795 + 7689628 * 2 ^ 59
def prefixEnd_7689628 : Nat := 4983230072969 + 3 ^ 40 * 7689628 * 2
def baseEnd_7689628 : Nat := 438719468696838392087339

theorem tailTrace_7689628 : CollatzResearch.WordTrace tailWord_7689628 prefixEnd_7689628 438719468696838392087339 := by
  unfold tailWord_7689628
  simp only [CollatzResearch.WordTrace]
  refine ⟨140231887092899257375818769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186975849457199009834425025 140231887092899257375818769)
  ·
    refine ⟨105173915319674443031864077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140231887092899257375818769 105173915319674443031864077)
    ·
      refine ⟨39440218244877916136949029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105173915319674443031864077 39440218244877916136949029)
      ·
        refine ⟨7395040920914609275677943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39440218244877916136949029 7395040920914609275677943)
        ·
          refine ⟨11092561381371913913516915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7395040920914609275677943 11092561381371913913516915)
          ·
            refine ⟨16638842072057870870275373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092561381371913913516915 16638842072057870870275373)
            ·
              refine ⟨6239565777021701576353265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16638842072057870870275373 6239565777021701576353265)
              ·
                refine ⟨4679674332766276182264949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6239565777021701576353265 4679674332766276182264949)
                ·
                  refine ⟨438719468696838392087339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4679674332766276182264949 438719468696838392087339)
                  ·
                    rfl

theorem cell23_7689628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_7689628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689628 prefixEnd_7689628 := by exact prefixLift 7689628
  have htrace : WordTrace (prefixWord ++ tailWord_7689628) baseStart_7689628 baseEnd_7689628 := by
    simpa [prefixWord, tailWord_7689628, baseEnd_7689628] using wordTrace_append hprefix tailTrace_7689628
  have hstable : (prefixWord ++ tailWord_7689628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689628).length < 2 ^ (prefixWord ++ tailWord_7689628).sum := by decide
  have hdescent : baseEnd_7689628 < baseStart_7689628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689637 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_7689637 : Nat := 118140960795 + 7689637 * 2 ^ 59
def prefixEnd_7689637 : Nat := 4983230072969 + 3 ^ 40 * 7689637 * 2
def baseEnd_7689637 : Nat := 1316159946532478664524503

theorem tailTrace_7689637 : CollatzResearch.WordTrace tailWord_7689637 prefixEnd_7689637 1316159946532478664524503 := by
  unfold tailWord_7689637
  simp only [CollatzResearch.WordTrace]
  refine ⟨280464102442765909288715165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186976068295177272859143443 280464102442765909288715165)
  ·
    refine ⟨105174038416037215983268187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280464102442765909288715165 105174038416037215983268187)
    ·
      refine ⟨157761057624055823974902281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105174038416037215983268187 157761057624055823974902281)
      ·
        refine ⟨118320793218041867981176711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157761057624055823974902281 118320793218041867981176711)
        ·
          refine ⟨177481189827062801971765067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118320793218041867981176711 177481189827062801971765067)
          ·
            refine ⟨266221784740594202957647601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177481189827062801971765067 266221784740594202957647601)
            ·
              refine ⟨199666338555445652218235701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266221784740594202957647601 199666338555445652218235701)
              ·
                refine ⟨18718719239573029895459597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199666338555445652218235701 18718719239573029895459597)
                ·
                  refine ⟨7019519714839886210797349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18718719239573029895459597 7019519714839886210797349)
                  ·
                    refine ⟨1316159946532478664524503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7019519714839886210797349 1316159946532478664524503)
                    ·
                      rfl

theorem cell23_7689637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_7689637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689637 prefixEnd_7689637 := by exact prefixLift 7689637
  have htrace : WordTrace (prefixWord ++ tailWord_7689637) baseStart_7689637 baseEnd_7689637 := by
    simpa [prefixWord, tailWord_7689637, baseEnd_7689637] using wordTrace_append hprefix tailTrace_7689637
  have hstable : (prefixWord ++ tailWord_7689637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689637).length < 2 ^ (prefixWord ++ tailWord_7689637).sum := by decide
  have hdescent : baseEnd_7689637 < baseStart_7689637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689650 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 10]
def baseStart_7689650 : Nat := 118140960795 + 7689650 * 2 ^ 59
def prefixEnd_7689650 : Nat := 4983230072969 + 3 ^ 40 * 7689650 * 2
def baseEnd_7689650 : Nat := 438720723871771604745661

theorem tailTrace_7689650 : CollatzResearch.WordTrace tailWord_7689650 prefixEnd_7689650 438720723871771604745661 := by
  unfold tailWord_7689650
  simp only [CollatzResearch.WordTrace]
  refine ⟨70116144147929703127234601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186976384394479208339292269 70116144147929703127234601)
  ·
    refine ⟨52587108110947277345425951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70116144147929703127234601 52587108110947277345425951)
    ·
      refine ⟨78880662166420916018138927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52587108110947277345425951 78880662166420916018138927)
      ·
        refine ⟨118320993249631374027208391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78880662166420916018138927 118320993249631374027208391)
        ·
          refine ⟨177481489874447061040812587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118320993249631374027208391 177481489874447061040812587)
          ·
            refine ⟨266222234811670591561218881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177481489874447061040812587 266222234811670591561218881)
            ·
              refine ⟨199666676108752943670914161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266222234811670591561218881 199666676108752943670914161)
              ·
                refine ⟨149750007081564707753185621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199666676108752943670914161 149750007081564707753185621)
                ·
                  refine ⟨438720723871771604745661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149750007081564707753185621 438720723871771604745661)
                  ·
                    rfl

theorem cell23_7689650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_7689650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689650 prefixEnd_7689650 := by exact prefixLift 7689650
  have htrace : WordTrace (prefixWord ++ tailWord_7689650) baseStart_7689650 baseEnd_7689650 := by
    simpa [prefixWord, tailWord_7689650, baseEnd_7689650] using wordTrace_append hprefix tailTrace_7689650
  have hstable : (prefixWord ++ tailWord_7689650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689650).length < 2 ^ (prefixWord ++ tailWord_7689650).sum := by decide
  have hdescent : baseEnd_7689650 < baseStart_7689650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689697 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 3, 5]
def baseStart_7689697 : Nat := 118140960795 + 7689697 * 2 ^ 59
def prefixEnd_7689697 : Nat := 4983230072969 + 3 ^ 40 * 7689697 * 2
def baseEnd_7689697 : Nat := 1316170216145568586274411

theorem tailTrace_7689697 : CollatzResearch.WordTrace tailWord_7689697 prefixEnd_7689697 1316170216145568586274411 := by
  unfold tailWord_7689697
  simp only [CollatzResearch.WordTrace]
  refine ⟨280466290822548539535899345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186977527215032359690599563 280466290822548539535899345)
  ·
    refine ⟨210349718116911404651924509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280466290822548539535899345 210349718116911404651924509)
    ·
      refine ⟨78881144293841776744471691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210349718116911404651924509 78881144293841776744471691)
      ·
        refine ⟨118321716440762665116707537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78881144293841776744471691 118321716440762665116707537)
        ·
          refine ⟨88741287330571998837530653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118321716440762665116707537 88741287330571998837530653)
          ·
            refine ⟨33277982748964499564073995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88741287330571998837530653 33277982748964499564073995)
            ·
              refine ⟨49916974123446749346110993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33277982748964499564073995 49916974123446749346110993)
              ·
                refine ⟨37437730592585062009583245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49916974123446749346110993 37437730592585062009583245)
                ·
                  refine ⟨14039148972219398253593717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37437730592585062009583245 14039148972219398253593717)
                  ·
                    refine ⟨1316170216145568586274411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14039148972219398253593717 1316170216145568586274411)
                    ·
                      rfl

theorem cell23_7689697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_7689697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689697 prefixEnd_7689697 := by exact prefixLift 7689697
  have htrace : WordTrace (prefixWord ++ tailWord_7689697) baseStart_7689697 baseEnd_7689697 := by
    simpa [prefixWord, tailWord_7689697, baseEnd_7689697] using wordTrace_append hprefix tailTrace_7689697
  have hstable : (prefixWord ++ tailWord_7689697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689697).length < 2 ^ (prefixWord ++ tailWord_7689697).sum := by decide
  have hdescent : baseEnd_7689697 < baseStart_7689697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689704 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_7689704 : Nat := 118140960795 + 7689704 * 2 ^ 59
def prefixEnd_7689704 : Nat := 4983230072969 + 3 ^ 40 * 7689704 * 2
def baseEnd_7689704 : Nat := 3948514242801287231435701

theorem tailTrace_7689704 : CollatzResearch.WordTrace tailWord_7689704 prefixEnd_7689704 3948514242801287231435701 := by
  unfold tailWord_7689704
  simp only [CollatzResearch.WordTrace]
  refine ⟨140233273066761589865702083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186977697422348786487602777 140233273066761589865702083)
  ·
    refine ⟨210349909600142384798553125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140233273066761589865702083 210349909600142384798553125)
    ·
      refine ⟨39440608050026697149728711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210349909600142384798553125 39440608050026697149728711)
      ·
        refine ⟨59160912075040045724593067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39440608050026697149728711 59160912075040045724593067)
        ·
          refine ⟨88741368112560068586889601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59160912075040045724593067 88741368112560068586889601)
          ·
            refine ⟨66556026084420051440167201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88741368112560068586889601 66556026084420051440167201)
            ·
              refine ⟨49917019563315038580125401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66556026084420051440167201 49917019563315038580125401)
              ·
                refine ⟨37437764672486278935094051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49917019563315038580125401 37437764672486278935094051)
                ·
                  refine ⟨56156647008729418402641077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37437764672486278935094051 56156647008729418402641077)
                  ·
                    refine ⟨5264685657068382975247601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56156647008729418402641077 5264685657068382975247601)
                    ·
                      refine ⟨3948514242801287231435701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264685657068382975247601 3948514242801287231435701)
                      ·
                        rfl

theorem cell23_7689704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_7689704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689704 prefixEnd_7689704 := by exact prefixLift 7689704
  have htrace : WordTrace (prefixWord ++ tailWord_7689704) baseStart_7689704 baseEnd_7689704 := by
    simpa [prefixWord, tailWord_7689704, baseEnd_7689704] using wordTrace_append hprefix tailTrace_7689704
  have hstable : (prefixWord ++ tailWord_7689704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689704).length < 2 ^ (prefixWord ++ tailWord_7689704).sum := by decide
  have hdescent : baseEnd_7689704 < baseStart_7689704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689714 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_7689714 : Nat := 118140960795 + 7689714 * 2 ^ 59
def prefixEnd_7689714 : Nat := 4983230072969 + 3 ^ 40 * 7689714 * 2
def baseEnd_7689714 : Nat := 1316173125869277397436885

theorem tailTrace_7689714 : CollatzResearch.WordTrace tailWord_7689714 prefixEnd_7689714 1316173125869277397436885 := by
  unfold tailWord_7689714
  simp only [CollatzResearch.WordTrace]
  refine ⟨70116727715871737859817049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186977940575657967626178797 70116727715871737859817049)
  ·
    refine ⟨52587545786903803394862787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70116727715871737859817049 52587545786903803394862787)
    ·
      refine ⟨78881318680355705092294181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52587545786903803394862787 78881318680355705092294181)
      ·
        refine ⟨14790247252566694704805159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78881318680355705092294181 14790247252566694704805159)
        ·
          refine ⟨22185370878850042057207739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14790247252566694704805159 22185370878850042057207739)
          ·
            refine ⟨33278056318275063085811609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22185370878850042057207739 33278056318275063085811609)
            ·
              refine ⟨24958542238706297314358707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33278056318275063085811609 24958542238706297314358707)
              ·
                refine ⟨37437813358059445971538061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24958542238706297314358707 37437813358059445971538061)
                ·
                  refine ⟨14039180009272292239326773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37437813358059445971538061 14039180009272292239326773)
                  ·
                    refine ⟨1316173125869277397436885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14039180009272292239326773 1316173125869277397436885)
                    ·
                      rfl

theorem cell23_7689714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_7689714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689714 prefixEnd_7689714 := by exact prefixLift 7689714
  have htrace : WordTrace (prefixWord ++ tailWord_7689714) baseStart_7689714 baseEnd_7689714 := by
    simpa [prefixWord, tailWord_7689714, baseEnd_7689714] using wordTrace_append hprefix tailTrace_7689714
  have hstable : (prefixWord ++ tailWord_7689714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689714).length < 2 ^ (prefixWord ++ tailWord_7689714).sum := by decide
  have hdescent : baseEnd_7689714 < baseStart_7689714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689737 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_7689737 : Nat := 118140960795 + 7689737 * 2 ^ 59
def prefixEnd_7689737 : Nat := 4983230072969 + 3 ^ 40 * 7689737 * 2
def baseEnd_7689737 : Nat := 3948531187662885602323049

theorem tailTrace_7689737 : CollatzResearch.WordTrace tailWord_7689737 prefixEnd_7689737 3948531187662885602323049 := by
  unfold tailWord_7689737
  simp only [CollatzResearch.WordTrace]
  refine ⟨280467749742403626367355465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186978499828269084244903643 280467749742403626367355465)
  ·
    refine ⟨210350812306802719775516599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280467749742403626367355465 210350812306802719775516599)
    ·
      refine ⟨315526218460204079663274899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210350812306802719775516599 315526218460204079663274899)
      ·
        refine ⟨473289327690306119494912349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315526218460204079663274899 473289327690306119494912349)
        ·
          refine ⟨177483497883864794810592131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473289327690306119494912349 177483497883864794810592131)
          ·
            refine ⟨266225246825797192215888197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177483497883864794810592131 266225246825797192215888197)
            ·
              refine ⟨49917233779836973540479037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266225246825797192215888197 49917233779836973540479037)
              ·
                refine ⟨18718962667438865077679639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49917233779836973540479037 18718962667438865077679639)
                ·
                  refine ⟨28078444001158297616519459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18718962667438865077679639 28078444001158297616519459)
                  ·
                    refine ⟨42117666001737446424779189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28078444001158297616519459 42117666001737446424779189)
                    ·
                      refine ⟨3948531187662885602323049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42117666001737446424779189 3948531187662885602323049)
                      ·
                        rfl

theorem cell23_7689737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_7689737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689737 prefixEnd_7689737 := by exact prefixLift 7689737
  have htrace : WordTrace (prefixWord ++ tailWord_7689737) baseStart_7689737 baseEnd_7689737 := by
    simpa [prefixWord, tailWord_7689737, baseEnd_7689737] using wordTrace_append hprefix tailTrace_7689737
  have hstable : (prefixWord ++ tailWord_7689737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689737).length < 2 ^ (prefixWord ++ tailWord_7689737).sum := by decide
  have hdescent : baseEnd_7689737 < baseStart_7689737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689757 : List Nat := [1, 4, 2, 2, 1, 1, 2, 10]
def baseStart_7689757 : Nat := 118140960795 + 7689757 * 2 ^ 59
def prefixEnd_7689757 : Nat := 4983230072969 + 3 ^ 40 * 7689757 * 2
def baseEnd_7689757 : Nat := 146242276195406500891591

theorem tailTrace_7689757 : CollatzResearch.WordTrace tailWord_7689757 prefixEnd_7689757 146242276195406500891591 := by
  unfold tailWord_7689757
  simp only [CollatzResearch.WordTrace]
  refine ⟨280468479202331169783083525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186978986134887446522055683 280468479202331169783083525)
  ·
    refine ⟨52587839850437094334328161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280468479202331169783083525 52587839850437094334328161)
    ·
      refine ⟨39440879887827820750746121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52587839850437094334328161 39440879887827820750746121)
      ·
        refine ⟨29580659915870865563059591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39440879887827820750746121 29580659915870865563059591)
        ·
          refine ⟨44370989873806298344589387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29580659915870865563059591 44370989873806298344589387)
          ·
            refine ⟨66556484810709447516884081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44370989873806298344589387 66556484810709447516884081)
            ·
              refine ⟨49917363608032085637663061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66556484810709447516884081 49917363608032085637663061)
              ·
                refine ⟨146242276195406500891591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49917363608032085637663061 146242276195406500891591)
                ·
                  rfl

theorem cell23_7689757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 10].length) (baseStart_7689757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689757 prefixEnd_7689757 := by exact prefixLift 7689757
  have htrace : WordTrace (prefixWord ++ tailWord_7689757) baseStart_7689757 baseEnd_7689757 := by
    simpa [prefixWord, tailWord_7689757, baseEnd_7689757] using wordTrace_append hprefix tailTrace_7689757
  have hstable : (prefixWord ++ tailWord_7689757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689757).length < 2 ^ (prefixWord ++ tailWord_7689757).sum := by decide
  have hdescent : baseEnd_7689757 < baseStart_7689757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689768 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7689768 : Nat := 118140960795 + 7689768 * 2 ^ 59
def prefixEnd_7689768 : Nat := 4983230072969 + 3 ^ 40 * 7689768 * 2
def baseEnd_7689768 : Nat := 3948547105563174981035407

theorem tailTrace_7689768 : CollatzResearch.WordTrace tailWord_7689768 prefixEnd_7689768 3948547105563174981035407 := by
  unfold tailWord_7689768
  simp only [CollatzResearch.WordTrace]
  refine ⟨140234440202645659330866979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186979253603527545774489305 140234440202645659330866979)
  ·
    refine ⟨210351660303968488996300469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140234440202645659330866979 210351660303968488996300469)
    ·
      refine ⟨19720468153497045843403169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210351660303968488996300469 19720468153497045843403169)
      ·
        refine ⟨14790351115122784382552377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19720468153497045843403169 14790351115122784382552377)
        ·
          refine ⟨11092763336342088286914283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14790351115122784382552377 11092763336342088286914283)
          ·
            refine ⟨16639145004513132430371425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11092763336342088286914283 16639145004513132430371425)
            ·
              refine ⟨12479358753384849322778569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16639145004513132430371425 12479358753384849322778569)
              ·
                refine ⟨9359519065038636992083927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12479358753384849322778569 9359519065038636992083927)
                ·
                  refine ⟨14039278597557955488125891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359519065038636992083927 14039278597557955488125891)
                  ·
                    refine ⟨21058917896336933232188837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14039278597557955488125891 21058917896336933232188837)
                    ·
                      refine ⟨3948547105563174981035407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21058917896336933232188837 3948547105563174981035407)
                      ·
                        rfl

theorem cell23_7689768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7689768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689768 prefixEnd_7689768 := by exact prefixLift 7689768
  have htrace : WordTrace (prefixWord ++ tailWord_7689768) baseStart_7689768 baseEnd_7689768 := by
    simpa [prefixWord, tailWord_7689768, baseEnd_7689768] using wordTrace_append hprefix tailTrace_7689768
  have hstable : (prefixWord ++ tailWord_7689768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689768).length < 2 ^ (prefixWord ++ tailWord_7689768).sum := by decide
  have hdescent : baseEnd_7689768 < baseStart_7689768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689774 : List Nat := [4, 1, 3, 1, 2, 2, 1, 9]
def baseStart_7689774 : Nat := 118140960795 + 7689774 * 2 ^ 59
def prefixEnd_7689774 : Nat := 4983230072969 + 3 ^ 40 * 7689774 * 2
def baseEnd_7689774 : Nat := 146242599498040813242977

theorem tailTrace_7689774 : CollatzResearch.WordTrace tailWord_7689774 prefixEnd_7689774 146242599498040813242977 := by
  unfold tailWord_7689774
  simp only [CollatzResearch.WordTrace]
  refine ⟨35058637405408697710806547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186979399495513054457634917 35058637405408697710806547)
  ·
    refine ⟨52587956108113046566209821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35058637405408697710806547 52587956108113046566209821)
    ·
      refine ⟨19720483540542392462328683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52587956108113046566209821 19720483540542392462328683)
      ·
        refine ⟨29580725310813588693493025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19720483540542392462328683 29580725310813588693493025)
        ·
          refine ⟨22185543983110191520119769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29580725310813588693493025 22185543983110191520119769)
          ·
            refine ⟨16639157987332643640089827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22185543983110191520119769 16639157987332643640089827)
            ·
              refine ⟨24958736980998965460134741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16639157987332643640089827 24958736980998965460134741)
              ·
                refine ⟨146242599498040813242977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24958736980998965460134741 146242599498040813242977)
                ·
                  rfl

theorem cell23_7689774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_7689774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689774 prefixEnd_7689774 := by exact prefixLift 7689774
  have htrace : WordTrace (prefixWord ++ tailWord_7689774) baseStart_7689774 baseEnd_7689774 := by
    simpa [prefixWord, tailWord_7689774, baseEnd_7689774] using wordTrace_append hprefix tailTrace_7689774
  have hstable : (prefixWord ++ tailWord_7689774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689774).length < 2 ^ (prefixWord ++ tailWord_7689774).sum := by decide
  have hdescent : baseEnd_7689774 < baseStart_7689774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689785 : List Nat := [1, 2, 1, 5, 1, 2, 3, 3, 1, 2, 2]
def baseStart_7689785 : Nat := 118140960795 + 7689785 * 2 ^ 59
def prefixEnd_7689785 : Nat := 4983230072969 + 3 ^ 40 * 7689785 * 2
def baseEnd_7689785 : Nat := 3948555834734301414522829

theorem tailTrace_7689785 : CollatzResearch.WordTrace tailWord_7689785 prefixEnd_7689785 3948555834734301414522829 := by
  unfold tailWord_7689785
  simp only [CollatzResearch.WordTrace]
  refine ⟨280469500446229730565102809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186979666964153153710068539 280469500446229730565102809)
  ·
    refine ⟨210352125334672297923827107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280469500446229730565102809 210352125334672297923827107)
    ·
      refine ⟨315528188002008446885740661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210352125334672297923827107 315528188002008446885740661)
      ·
        refine ⟨29580767625188291895538187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315528188002008446885740661 29580767625188291895538187)
        ·
          refine ⟨44371151437782437843307281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29580767625188291895538187 44371151437782437843307281)
          ·
            refine ⟨33278363578336828382480461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44371151437782437843307281 33278363578336828382480461)
            ·
              refine ⟨12479386341876310643430173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33278363578336828382480461 12479386341876310643430173)
              ·
                refine ⟨4679769878203616491286315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12479386341876310643430173 4679769878203616491286315)
                ·
                  refine ⟨7019654817305424736929473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679769878203616491286315 7019654817305424736929473)
                  ·
                    refine ⟨5264741112979068552697105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7019654817305424736929473 5264741112979068552697105)
                    ·
                      refine ⟨3948555834734301414522829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264741112979068552697105 3948555834734301414522829)
                      ·
                        rfl

theorem cell23_7689785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_7689785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689785 prefixEnd_7689785 := by exact prefixLift 7689785
  have htrace : WordTrace (prefixWord ++ tailWord_7689785) baseStart_7689785 baseEnd_7689785 := by
    simpa [prefixWord, tailWord_7689785, baseEnd_7689785] using wordTrace_append hprefix tailTrace_7689785
  have hstable : (prefixWord ++ tailWord_7689785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689785).length < 2 ^ (prefixWord ++ tailWord_7689785).sum := by decide
  have hdescent : baseEnd_7689785 < baseStart_7689785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689797 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_7689797 : Nat := 118140960795 + 7689797 * 2 ^ 59
def prefixEnd_7689797 : Nat := 4983230072969 + 3 ^ 40 * 7689797 * 2
def baseEnd_7689797 : Nat := 3948561996502155367572773

theorem tailTrace_7689797 : CollatzResearch.WordTrace tailWord_7689797 prefixEnd_7689797 3948561996502155367572773 := by
  unfold tailWord_7689797
  simp only [CollatzResearch.WordTrace]
  refine ⟨280469938122186256614539645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186979958748124171076359763 280469938122186256614539645)
  ·
    refine ⟨105176226795819846230452367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280469938122186256614539645 105176226795819846230452367)
    ·
      refine ⟨157764340193729769345678551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105176226795819846230452367 157764340193729769345678551)
      ·
        refine ⟨236646510290594654018517827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157764340193729769345678551 236646510290594654018517827)
        ·
          refine ⟨354969765435891981027776741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236646510290594654018517827 354969765435891981027776741)
          ·
            refine ⟨66556831019229746442708139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354969765435891981027776741 66556831019229746442708139)
            ·
              refine ⟨99835246528844619664062209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66556831019229746442708139 99835246528844619664062209)
              ·
                refine ⟨74876434896633464748046657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99835246528844619664062209 74876434896633464748046657)
                ·
                  refine ⟨56157326172475098561034993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74876434896633464748046657 56157326172475098561034993)
                  ·
                    refine ⟨42117994629356323920776245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56157326172475098561034993 42117994629356323920776245)
                    ·
                      refine ⟨3948561996502155367572773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42117994629356323920776245 3948561996502155367572773)
                      ·
                        rfl

theorem cell23_7689797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_7689797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689797 prefixEnd_7689797 := by exact prefixLift 7689797
  have htrace : WordTrace (prefixWord ++ tailWord_7689797) baseStart_7689797 baseEnd_7689797 := by
    simpa [prefixWord, tailWord_7689797, baseEnd_7689797] using wordTrace_append hprefix tailTrace_7689797
  have hstable : (prefixWord ++ tailWord_7689797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689797).length < 2 ^ (prefixWord ++ tailWord_7689797).sum := by decide
  have hdescent : baseEnd_7689797 < baseStart_7689797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689807 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_7689807 : Nat := 118140960795 + 7689807 * 2 ^ 59
def prefixEnd_7689807 : Nat := 4983230072969 + 3 ^ 40 * 7689807 * 2
def baseEnd_7689807 : Nat := 3948567131308700328447727

theorem tailTrace_7689807 : CollatzResearch.WordTrace tailWord_7689807 prefixEnd_7689807 3948567131308700328447727 := by
  unfold tailWord_7689807
  simp only [CollatzResearch.WordTrace]
  refine ⟨280470302852150028322403675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186980201901433352214935783 280470302852150028322403675)
  ·
    refine ⟨420705454278225042483605513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280470302852150028322403675 420705454278225042483605513)
    ·
      refine ⟨315529090708668781862704135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420705454278225042483605513 315529090708668781862704135)
      ·
        refine ⟨473293636063003172794056203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315529090708668781862704135 473293636063003172794056203)
        ·
          refine ⟨709940454094504759191084305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473293636063003172794056203 709940454094504759191084305)
          ·
            refine ⟨532455340570878569393313229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709940454094504759191084305 532455340570878569393313229)
            ·
              refine ⟨199670752714079463522492461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532455340570878569393313229 199670752714079463522492461)
              ·
                refine ⟨74876532267779798820934673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199670752714079463522492461 74876532267779798820934673)
                ·
                  refine ⟨56157399200834849115701005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74876532267779798820934673 56157399200834849115701005)
                  ·
                    refine ⟨21059024700313068418387877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56157399200834849115701005 21059024700313068418387877)
                    ·
                      refine ⟨3948567131308700328447727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21059024700313068418387877 3948567131308700328447727)
                      ·
                        rfl

theorem cell23_7689807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_7689807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689807 prefixEnd_7689807 := by exact prefixLift 7689807
  have htrace : WordTrace (prefixWord ++ tailWord_7689807) baseStart_7689807 baseEnd_7689807 := by
    simpa [prefixWord, tailWord_7689807, baseEnd_7689807] using wordTrace_append hprefix tailTrace_7689807
  have hstable : (prefixWord ++ tailWord_7689807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689807).length < 2 ^ (prefixWord ++ tailWord_7689807).sum := by decide
  have hdescent : baseEnd_7689807 < baseStart_7689807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689817 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 2, 6]
def baseStart_7689817 : Nat := 118140960795 + 7689817 * 2 ^ 59
def prefixEnd_7689817 : Nat := 4983230072969 + 3 ^ 40 * 7689817 * 2
def baseEnd_7689817 : Nat := 1316190755371748429774227

theorem tailTrace_7689817 : CollatzResearch.WordTrace tailWord_7689817 prefixEnd_7689817 1316190755371748429774227 := by
  unfold tailWord_7689817
  simp only [CollatzResearch.WordTrace]
  refine ⟨280470667582113800030267705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186980445054742533353511803 280470667582113800030267705)
  ·
    refine ⟨210353000686585350022700779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280470667582113800030267705 210353000686585350022700779)
    ·
      refine ⟨315529501029878025034051169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210353000686585350022700779 315529501029878025034051169)
      ·
        refine ⟨236647125772408518775538377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315529501029878025034051169 236647125772408518775538377)
        ·
          refine ⟨177485344329306389081653783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236647125772408518775538377 177485344329306389081653783)
          ·
            refine ⟨266228016493959583622480675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177485344329306389081653783 266228016493959583622480675)
            ·
              refine ⟨399342024740939375433721013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266228016493959583622480675 399342024740939375433721013)
              ·
                refine ⟨37438314819463066446911345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399342024740939375433721013 37438314819463066446911345)
                ·
                  refine ⟨28078736114597299835183509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37438314819463066446911345 28078736114597299835183509)
                  ·
                    refine ⟨1316190755371748429774227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28078736114597299835183509 1316190755371748429774227)
                    ·
                      rfl

theorem cell23_7689817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_7689817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689817 prefixEnd_7689817 := by exact prefixLift 7689817
  have htrace : WordTrace (prefixWord ++ tailWord_7689817) baseStart_7689817 baseEnd_7689817 := by
    simpa [prefixWord, tailWord_7689817, baseEnd_7689817] using wordTrace_append hprefix tailTrace_7689817
  have hstable : (prefixWord ++ tailWord_7689817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689817).length < 2 ^ (prefixWord ++ tailWord_7689817).sum := by decide
  have hdescent : baseEnd_7689817 < baseStart_7689817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689828 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_7689828 : Nat := 118140960795 + 7689828 * 2 ^ 59
def prefixEnd_7689828 : Nat := 4983230072969 + 3 ^ 40 * 7689828 * 2
def baseEnd_7689828 : Nat := 3948577914402444746285131

theorem tailTrace_7689828 : CollatzResearch.WordTrace tailWord_7689828 prefixEnd_7689828 3948577914402444746285131 := by
  unfold tailWord_7689828
  simp only [CollatzResearch.WordTrace]
  refine ⟨140235534392536974454459069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186980712523382632605945425 140235534392536974454459069)
  ·
    refine ⟨52588325397201365420422151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140235534392536974454459069 52588325397201365420422151)
    ·
      refine ⟨78882488095802048130633227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52588325397201365420422151 78882488095802048130633227)
      ·
        refine ⟨118323732143703072195949841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78882488095802048130633227 118323732143703072195949841)
        ·
          refine ⟨88742799107777304146962381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118323732143703072195949841 88742799107777304146962381)
          ·
            refine ⟨33278549665416489055110893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88742799107777304146962381 33278549665416489055110893)
            ·
              refine ⟨12479456124531183395666585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33278549665416489055110893 12479456124531183395666585)
              ·
                refine ⟨9359592093398387546749939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12479456124531183395666585 9359592093398387546749939)
                ·
                  refine ⟨14039388140097581320124909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359592093398387546749939 14039388140097581320124909)
                  ·
                    refine ⟨5264770552536592995046841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14039388140097581320124909 5264770552536592995046841)
                    ·
                      refine ⟨3948577914402444746285131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264770552536592995046841 3948577914402444746285131)
                      ·
                        rfl

theorem cell23_7689828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_7689828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689828 prefixEnd_7689828 := by exact prefixLift 7689828
  have htrace : WordTrace (prefixWord ++ tailWord_7689828) baseStart_7689828 baseEnd_7689828 := by
    simpa [prefixWord, tailWord_7689828, baseEnd_7689828] using wordTrace_append hprefix tailTrace_7689828
  have hstable : (prefixWord ++ tailWord_7689828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689828).length < 2 ^ (prefixWord ++ tailWord_7689828).sum := by decide
  have hdescent : baseEnd_7689828 < baseStart_7689828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689841 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 6, 2, 2]
def baseStart_7689841 : Nat := 118140960795 + 7689841 * 2 ^ 59
def prefixEnd_7689841 : Nat := 4983230072969 + 3 ^ 40 * 7689841 * 2
def baseEnd_7689841 : Nat := 3948584589650953195422571

theorem tailTrace_7689841 : CollatzResearch.WordTrace tailWord_7689841 prefixEnd_7689841 3948584589650953195422571 := by
  unfold tailWord_7689841
  simp only [CollatzResearch.WordTrace]
  refine ⟨280471542934026852129141377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186981028622684568086094251 280471542934026852129141377)
  ·
    refine ⟨210353657200520139096856033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280471542934026852129141377 210353657200520139096856033)
    ·
      refine ⟨157765242900390104322642025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210353657200520139096856033 157765242900390104322642025)
      ·
        refine ⟨118323932175292578241981519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157765242900390104322642025 118323932175292578241981519)
        ·
          refine ⟨177485898262938867362972279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118323932175292578241981519 177485898262938867362972279)
          ·
            refine ⟨266228847394408301044458419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177485898262938867362972279 266228847394408301044458419)
            ·
              refine ⟨399343271091612451566687629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266228847394408301044458419 399343271091612451566687629)
              ·
                refine ⟨149753726659354669337507861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399343271091612451566687629 149753726659354669337507861)
                ·
                  refine ⟨7019705937157250125195681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149753726659354669337507861 7019705937157250125195681)
                  ·
                    refine ⟨5264779452867937593896761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7019705937157250125195681 5264779452867937593896761)
                    ·
                      refine ⟨3948584589650953195422571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264779452867937593896761 3948584589650953195422571)
                      ·
                        rfl

theorem cell23_7689841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_7689841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689841 prefixEnd_7689841 := by exact prefixLift 7689841
  have htrace : WordTrace (prefixWord ++ tailWord_7689841) baseStart_7689841 baseEnd_7689841 := by
    simpa [prefixWord, tailWord_7689841, baseEnd_7689841] using wordTrace_append hprefix tailTrace_7689841
  have hstable : (prefixWord ++ tailWord_7689841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689841).length < 2 ^ (prefixWord ++ tailWord_7689841).sum := by decide
  have hdescent : baseEnd_7689841 < baseStart_7689841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689896 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7689896 : Nat := 118140960795 + 7689896 * 2 ^ 59
def prefixEnd_7689896 : Nat := 4983230072969 + 3 ^ 40 * 7689896 * 2
def baseEnd_7689896 : Nat := 3948612831086950480234819

theorem tailTrace_7689896 : CollatzResearch.WordTrace tailWord_7689896 prefixEnd_7689896 3948612831086950480234819 := by
  unfold tailWord_7689896
  simp only [CollatzResearch.WordTrace]
  refine ⟨140236774474413798261196771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186982365965885064348262361 140236774474413798261196771)
  ·
    refine ⟨210355161711620697391795157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140236774474413798261196771 210355161711620697391795157)
    ·
      refine ⟨4930199102616110095120199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 210355161711620697391795157 4930199102616110095120199)
      ·
        refine ⟨7395298653924165142680299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4930199102616110095120199 7395298653924165142680299)
        ·
          refine ⟨11092947980886247714020449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7395298653924165142680299 11092947980886247714020449)
          ·
            refine ⟨8319710985664685785515337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11092947980886247714020449 8319710985664685785515337)
            ·
              refine ⟨6239783239248514339136503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8319710985664685785515337 6239783239248514339136503)
              ·
                refine ⟨9359674858872771508704755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239783239248514339136503 9359674858872771508704755)
                ·
                  refine ⟨14039512288309157263057133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359674858872771508704755 14039512288309157263057133)
                  ·
                    refine ⟨5264817108115933973646425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14039512288309157263057133 5264817108115933973646425)
                    ·
                      refine ⟨3948612831086950480234819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264817108115933973646425 3948612831086950480234819)
                      ·
                        rfl

theorem cell23_7689896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7689896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689896 prefixEnd_7689896 := by exact prefixLift 7689896
  have htrace : WordTrace (prefixWord ++ tailWord_7689896) baseStart_7689896 baseEnd_7689896 := by
    simpa [prefixWord, tailWord_7689896, baseEnd_7689896] using wordTrace_append hprefix tailTrace_7689896
  have hstable : (prefixWord ++ tailWord_7689896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689896).length < 2 ^ (prefixWord ++ tailWord_7689896).sum := by decide
  have hdescent : baseEnd_7689896 < baseStart_7689896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689897 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_7689897 : Nat := 118140960795 + 7689897 * 2 ^ 59
def prefixEnd_7689897 : Nat := 4983230072969 + 3 ^ 40 * 7689897 * 2
def baseEnd_7689897 : Nat := 3948613344567604976322313

theorem tailTrace_7689897 : CollatzResearch.WordTrace tailWord_7689897 prefixEnd_7689897 3948613344567604976322313 := by
  unfold tailWord_7689897
  simp only [CollatzResearch.WordTrace]
  refine ⟨280473585421823973693179945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186982390281215982462119963 280473585421823973693179945)
  ·
    refine ⟨210355189066367980269884959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280473585421823973693179945 210355189066367980269884959)
    ·
      refine ⟨315532783599551970404827439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210355189066367980269884959 315532783599551970404827439)
      ·
        refine ⟨473299175399327955607241159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315532783599551970404827439 473299175399327955607241159)
        ·
          refine ⟨709948763098991933410861739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473299175399327955607241159 709948763098991933410861739)
          ·
            refine ⟨1064923144648487900116292609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709948763098991933410861739 1064923144648487900116292609)
            ·
              refine ⟨798692358486365925087219457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1064923144648487900116292609 798692358486365925087219457)
              ·
                refine ⟨599019268864774443815414593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 798692358486365925087219457 599019268864774443815414593)
                ·
                  refine ⟨449264451648580832861560945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599019268864774443815414593 449264451648580832861560945)
                  ·
                    refine ⟨336948338736435624646170709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 449264451648580832861560945 336948338736435624646170709)
                    ·
                      refine ⟨3948613344567604976322313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 336948338736435624646170709 3948613344567604976322313)
                      ·
                        rfl

theorem cell23_7689897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_7689897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689897 prefixEnd_7689897 := by exact prefixLift 7689897
  have htrace : WordTrace (prefixWord ++ tailWord_7689897) baseStart_7689897 baseEnd_7689897 := by
    simpa [prefixWord, tailWord_7689897, baseEnd_7689897] using wordTrace_append hprefix tailTrace_7689897
  have hstable : (prefixWord ++ tailWord_7689897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689897).length < 2 ^ (prefixWord ++ tailWord_7689897).sum := by decide
  have hdescent : baseEnd_7689897 < baseStart_7689897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689909 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_7689909 : Nat := 118140960795 + 7689909 * 2 ^ 59
def prefixEnd_7689909 : Nat := 4983230072969 + 3 ^ 40 * 7689909 * 2
def baseEnd_7689909 : Nat := 3948619506335458929372259

theorem tailTrace_7689909 : CollatzResearch.WordTrace tailWord_7689909 prefixEnd_7689909 3948619506335458929372259 := by
  unfold tailWord_7689909
  simp only [CollatzResearch.WordTrace]
  refine ⟨280474023097780499742616781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186982682065186999828411187 280474023097780499742616781)
  ·
    refine ⟨105177758661667687403481293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280474023097780499742616781 105177758661667687403481293)
    ·
      refine ⟨39441659498125382776305485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105177758661667687403481293 39441659498125382776305485)
      ·
        refine ⟨14790622311797018541114557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39441659498125382776305485 14790622311797018541114557)
        ·
          refine ⟨5546483366923881952917959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14790622311797018541114557 5546483366923881952917959)
          ·
            refine ⟨8319725050385822929376939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5546483366923881952917959 8319725050385822929376939)
            ·
              refine ⟨12479587575578734394065409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319725050385822929376939 12479587575578734394065409)
              ·
                refine ⟨9359690681684050795549057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12479587575578734394065409 9359690681684050795549057)
                ·
                  refine ⟨7019768011263038096661793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9359690681684050795549057 7019768011263038096661793)
                  ·
                    refine ⟨5264826008447278572496345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7019768011263038096661793 5264826008447278572496345)
                    ·
                      refine ⟨3948619506335458929372259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264826008447278572496345 3948619506335458929372259)
                      ·
                        rfl

theorem cell23_7689909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_7689909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689909 prefixEnd_7689909 := by exact prefixLift 7689909
  have htrace : WordTrace (prefixWord ++ tailWord_7689909) baseStart_7689909 baseEnd_7689909 := by
    simpa [prefixWord, tailWord_7689909, baseEnd_7689909] using wordTrace_append hprefix tailTrace_7689909
  have hstable : (prefixWord ++ tailWord_7689909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689909).length < 2 ^ (prefixWord ++ tailWord_7689909).sum := by decide
  have hdescent : baseEnd_7689909 < baseStart_7689909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689926 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_7689926 : Nat := 118140960795 + 7689926 * 2 ^ 59
def prefixEnd_7689926 : Nat := 4983230072969 + 3 ^ 40 * 7689926 * 2
def baseEnd_7689926 : Nat := 3948628235506585362859681

theorem tailTrace_7689926 : CollatzResearch.WordTrace tailWord_7689926 prefixEnd_7689926 3948628235506585362859681 := by
  unfold tailWord_7689926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8764832598084965988937051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 186983095425812607763990421 8764832598084965988937051)
  ·
    refine ⟨13147248897127448983405577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8764832598084965988937051 13147248897127448983405577)
    ·
      refine ⟨9860436672845586737554183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13147248897127448983405577 9860436672845586737554183)
      ·
        refine ⟨14790655009268380106331275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9860436672845586737554183 14790655009268380106331275)
        ·
          refine ⟨22185982513902570159496913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14790655009268380106331275 22185982513902570159496913)
          ·
            refine ⟨16639486885426927619622685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22185982513902570159496913 16639486885426927619622685)
            ·
              refine ⟨6239807582035097857358507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16639486885426927619622685 6239807582035097857358507)
              ·
                refine ⟨9359711373052646786037761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239807582035097857358507 9359711373052646786037761)
                ·
                  refine ⟨7019783529789485089528321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9359711373052646786037761 7019783529789485089528321)
                  ·
                    refine ⟨5264837647342113817146241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7019783529789485089528321 5264837647342113817146241)
                    ·
                      refine ⟨3948628235506585362859681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264837647342113817146241 3948628235506585362859681)
                      ·
                        rfl

theorem cell23_7689926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_7689926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689926 prefixEnd_7689926 := by exact prefixLift 7689926
  have htrace : WordTrace (prefixWord ++ tailWord_7689926) baseStart_7689926 baseEnd_7689926 := by
    simpa [prefixWord, tailWord_7689926, baseEnd_7689926] using wordTrace_append hprefix tailTrace_7689926
  have hstable : (prefixWord ++ tailWord_7689926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689926).length < 2 ^ (prefixWord ++ tailWord_7689926).sum := by decide
  have hdescent : baseEnd_7689926 < baseStart_7689926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689944 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_7689944 : Nat := 118140960795 + 7689944 * 2 ^ 59
def prefixEnd_7689944 : Nat := 4983230072969 + 3 ^ 40 * 7689944 * 2
def baseEnd_7689944 : Nat := 3948637478158366292434597

theorem tailTrace_7689944 : CollatzResearch.WordTrace tailWord_7689944 prefixEnd_7689944 3948637478158366292434597 := by
  unfold tailWord_7689944
  simp only [CollatzResearch.WordTrace]
  refine ⟨140237649826326850360070443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186983533101769133813427257 140237649826326850360070443)
  ·
    refine ⟨210356474739490275540105665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140237649826326850360070443 210356474739490275540105665)
    ·
      refine ⟨157767356054617706655079249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210356474739490275540105665 157767356054617706655079249)
      ·
        refine ⟨118325517040963279991309437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157767356054617706655079249 118325517040963279991309437)
        ·
          refine ⟨44372068890361229996741039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118325517040963279991309437 44372068890361229996741039)
          ·
            refine ⟨66558103335541844995111559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44372068890361229996741039 66558103335541844995111559)
            ·
              refine ⟨99837155003312767492667339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66558103335541844995111559 99837155003312767492667339)
              ·
                refine ⟨149755732504969151239001009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99837155003312767492667339 149755732504969151239001009)
                ·
                  refine ⟨112316799378726863429250757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149755732504969151239001009 112316799378726863429250757)
                  ·
                    refine ⟨21059399883511286892984517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112316799378726863429250757 21059399883511286892984517)
                    ·
                      refine ⟨3948637478158366292434597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21059399883511286892984517 3948637478158366292434597)
                      ·
                        rfl

theorem cell23_7689944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_7689944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689944 prefixEnd_7689944 := by exact prefixLift 7689944
  have htrace : WordTrace (prefixWord ++ tailWord_7689944) baseStart_7689944 baseEnd_7689944 := by
    simpa [prefixWord, tailWord_7689944, baseEnd_7689944] using wordTrace_append hprefix tailTrace_7689944
  have hstable : (prefixWord ++ tailWord_7689944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689944).length < 2 ^ (prefixWord ++ tailWord_7689944).sum := by decide
  have hdescent : baseEnd_7689944 < baseStart_7689944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689951 : List Nat := [1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 3]
def baseStart_7689951 : Nat := 118140960795 + 7689951 * 2 ^ 59
def prefixEnd_7689951 : Nat := 4983230072969 + 3 ^ 40 * 7689951 * 2
def baseEnd_7689951 : Nat := 3948641072522947765047065

theorem tailTrace_7689951 : CollatzResearch.WordTrace tailWord_7689951 prefixEnd_7689951 3948641072522947765047065 := by
  unfold tailWord_7689951
  simp only [CollatzResearch.WordTrace]
  refine ⟨280475554963628340915645707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186983703309085560610430471 280475554963628340915645707)
  ·
    refine ⟨420713332445442511373468561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280475554963628340915645707 420713332445442511373468561)
    ·
      refine ⟨315534999334081883530101421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420713332445442511373468561 315534999334081883530101421)
      ·
        refine ⟨118325624750280706323788033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315534999334081883530101421 118325624750280706323788033)
        ·
          refine ⟨88744218562710529742841025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118325624750280706323788033 88744218562710529742841025)
          ·
            refine ⟨66558163922032897307130769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88744218562710529742841025 66558163922032897307130769)
            ·
              refine ⟨49918622941524672980348077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66558163922032897307130769 49918622941524672980348077)
              ·
                refine ⟨18719483603071752367630529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49918622941524672980348077 18719483603071752367630529)
                ·
                  refine ⟨14039612702303814275722897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18719483603071752367630529 14039612702303814275722897)
                  ·
                    refine ⟨10529709526727860706792173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14039612702303814275722897 10529709526727860706792173)
                    ·
                      refine ⟨3948641072522947765047065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10529709526727860706792173 3948641072522947765047065)
                      ·
                        rfl

theorem cell23_7689951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_7689951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689951 prefixEnd_7689951 := by exact prefixLift 7689951
  have htrace : WordTrace (prefixWord ++ tailWord_7689951) baseStart_7689951 baseEnd_7689951 := by
    simpa [prefixWord, tailWord_7689951, baseEnd_7689951] using wordTrace_append hprefix tailTrace_7689951
  have hstable : (prefixWord ++ tailWord_7689951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689951).length < 2 ^ (prefixWord ++ tailWord_7689951).sum := by decide
  have hdescent : baseEnd_7689951 < baseStart_7689951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689984 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 5, 5]
def baseStart_7689984 : Nat := 118140960795 + 7689984 * 2 ^ 59
def prefixEnd_7689984 : Nat := 4983230072969 + 3 ^ 40 * 7689984 * 2
def baseEnd_7689984 : Nat := 1316219339128182045311471

theorem tailTrace_7689984 : CollatzResearch.WordTrace tailWord_7689984 prefixEnd_7689984 1316219339128182045311471 := by
  unfold tailWord_7689984
  simp only [CollatzResearch.WordTrace]
  refine ⟨140238379286254393775798503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186984505715005858367731337 140238379286254393775798503)
  ·
    refine ⟨210357568929381590663697755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140238379286254393775798503 210357568929381590663697755)
    ·
      refine ⟨315536353394072385995546633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210357568929381590663697755 315536353394072385995546633)
      ·
        refine ⟨236652265045554289496659975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315536353394072385995546633 236652265045554289496659975)
        ·
          refine ⟨354978397568331434244989963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236652265045554289496659975 354978397568331434244989963)
          ·
            refine ⟨532467596352497151367484945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354978397568331434244989963 532467596352497151367484945)
            ·
              refine ⟨399350697264372863525613709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532467596352497151367484945 399350697264372863525613709)
              ·
                refine ⟨149756511474139823822105141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399350697264372863525613709 149756511474139823822105141)
                ·
                  refine ⟨14039672950700608483322357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149756511474139823822105141 14039672950700608483322357)
                  ·
                    refine ⟨1316219339128182045311471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14039672950700608483322357 1316219339128182045311471)
                    ·
                      rfl

theorem cell23_7689984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_7689984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689984 prefixEnd_7689984 := by exact prefixLift 7689984
  have htrace : WordTrace (prefixWord ++ tailWord_7689984) baseStart_7689984 baseEnd_7689984 := by
    simpa [prefixWord, tailWord_7689984, baseEnd_7689984] using wordTrace_append hprefix tailTrace_7689984
  have hstable : (prefixWord ++ tailWord_7689984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689984).length < 2 ^ (prefixWord ++ tailWord_7689984).sum := by decide
  have hdescent : baseEnd_7689984 < baseStart_7689984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689988 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 6]
def baseStart_7689988 : Nat := 118140960795 + 7689988 * 2 ^ 59
def prefixEnd_7689988 : Nat := 4983230072969 + 3 ^ 40 * 7689988 * 2
def baseEnd_7689988 : Nat := 438740007923018235587155

theorem tailTrace_7689988 : CollatzResearch.WordTrace tailWord_7689988 prefixEnd_7689988 438740007923018235587155 := by
  unfold tailWord_7689988
  simp only [CollatzResearch.WordTrace]
  refine ⟨140238452232247148117371309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186984602976329530823161745 140238452232247148117371309)
  ·
    refine ⟨52589419587092680544014241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140238452232247148117371309 52589419587092680544014241)
    ·
      refine ⟨39442064690319510408010681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52589419587092680544014241 39442064690319510408010681)
      ·
        refine ⟨29581548517739632806008011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39442064690319510408010681 29581548517739632806008011)
        ·
          refine ⟨44372322776609449209012017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29581548517739632806008011 44372322776609449209012017)
          ·
            refine ⟨33279242082457086906759013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44372322776609449209012017 33279242082457086906759013)
            ·
              refine ⟨6239857890460703795017315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33279242082457086906759013 6239857890460703795017315)
              ·
                refine ⟨9359786835691055692525973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239857890460703795017315 9359786835691055692525973)
                ·
                  refine ⟨438740007923018235587155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9359786835691055692525973 438740007923018235587155)
                  ·
                    rfl

theorem cell23_7689988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_7689988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689988 prefixEnd_7689988 := by exact prefixLift 7689988
  have htrace : WordTrace (prefixWord ++ tailWord_7689988) baseStart_7689988 baseEnd_7689988 := by
    simpa [prefixWord, tailWord_7689988, baseEnd_7689988] using wordTrace_append hprefix tailTrace_7689988
  have hstable : (prefixWord ++ tailWord_7689988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689988).length < 2 ^ (prefixWord ++ tailWord_7689988).sum := by decide
  have hdescent : baseEnd_7689988 < baseStart_7689988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7689998 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_7689998 : Nat := 118140960795 + 7689998 * 2 ^ 59
def prefixEnd_7689998 : Nat := 4983230072969 + 3 ^ 40 * 7689998 * 2
def baseEnd_7689998 : Nat := 3948665206113709081159349

theorem tailTrace_7689998 : CollatzResearch.WordTrace tailWord_7689998 prefixEnd_7689998 3948665206113709081159349 := by
  unfold tailWord_7689998
  simp only [CollatzResearch.WordTrace]
  refine ⟨35059658649307258492825831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186984846129638711961737765 35059658649307258492825831)
  ·
    refine ⟨52589487973960887739238747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35059658649307258492825831 52589487973960887739238747)
    ·
      refine ⟨78884231960941331608858121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52589487973960887739238747 78884231960941331608858121)
      ·
        refine ⟨59163173970705998706643591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78884231960941331608858121 59163173970705998706643591)
        ·
          refine ⟨88744760956058998059965387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59163173970705998706643591 88744760956058998059965387)
          ·
            refine ⟨133117141434088497089948081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88744760956058998059965387 133117141434088497089948081)
            ·
              refine ⟨99837856075566372817461061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133117141434088497089948081 99837856075566372817461061)
              ·
                refine ⟨18719598014168694903273949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99837856075566372817461061 18719598014168694903273949)
                ·
                  refine ⟨7019849255313260588727731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18719598014168694903273949 7019849255313260588727731)
                  ·
                    refine ⟨10529773882969890883091597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7019849255313260588727731 10529773882969890883091597)
                    ·
                      refine ⟨3948665206113709081159349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10529773882969890883091597 3948665206113709081159349)
                      ·
                        rfl

theorem cell23_7689998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_7689998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7689998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7689998 prefixEnd_7689998 := by exact prefixLift 7689998
  have htrace : WordTrace (prefixWord ++ tailWord_7689998) baseStart_7689998 baseEnd_7689998 := by
    simpa [prefixWord, tailWord_7689998, baseEnd_7689998] using wordTrace_append hprefix tailTrace_7689998
  have hstable : (prefixWord ++ tailWord_7689998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7689998).length < 2 ^ (prefixWord ++ tailWord_7689998).sum := by decide
  have hdescent : baseEnd_7689998 < baseStart_7689998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7689998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690008 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 2, 3, 2]
def baseStart_7690008 : Nat := 118140960795 + 7690008 * 2 ^ 59
def prefixEnd_7690008 : Nat := 4983230072969 + 3 ^ 40 * 7690008 * 2
def baseEnd_7690008 : Nat := 3948670340920254042034303

theorem tailTrace_7690008 : CollatzResearch.WordTrace tailWord_7690008 prefixEnd_7690008 3948670340920254042034303 := by
  unfold tailWord_7690008
  simp only [CollatzResearch.WordTrace]
  refine ⟨140238816962210919825235339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186985089282947893100313785 140238816962210919825235339)
  ·
    refine ⟨210358225443316379737853009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140238816962210919825235339 210358225443316379737853009)
    ·
      refine ⟨157768669082487284803389757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210358225443316379737853009 157768669082487284803389757)
      ·
        refine ⟨59163250905932731801271159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157768669082487284803389757 59163250905932731801271159)
        ·
          refine ⟨88744876358899097701906739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59163250905932731801271159 88744876358899097701906739)
          ·
            refine ⟨133117314538348646552860109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88744876358899097701906739 133117314538348646552860109)
            ·
              refine ⟨49918992951880742457322541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133117314538348646552860109 49918992951880742457322541)
              ·
                refine ⟨18719622356955278421495953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49918992951880742457322541 18719622356955278421495953)
                ·
                  refine ⟨14039716767716458816121965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18719622356955278421495953 14039716767716458816121965)
                  ·
                    refine ⟨5264893787893672056045737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14039716767716458816121965 5264893787893672056045737)
                    ·
                      refine ⟨3948670340920254042034303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264893787893672056045737 3948670340920254042034303)
                      ·
                        rfl

theorem cell23_7690008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_7690008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690008 prefixEnd_7690008 := by exact prefixLift 7690008
  have htrace : WordTrace (prefixWord ++ tailWord_7690008) baseStart_7690008 baseEnd_7690008 := by
    simpa [prefixWord, tailWord_7690008, baseEnd_7690008] using wordTrace_append hprefix tailTrace_7690008
  have hstable : (prefixWord ++ tailWord_7690008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690008).length < 2 ^ (prefixWord ++ tailWord_7690008).sum := by decide
  have hdescent : baseEnd_7690008 < baseStart_7690008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690015 : List Nat := [1, 1, 2, 4, 2, 1, 2, 5, 1, 1, 3]
def baseStart_7690015 : Nat := 118140960795 + 7690015 * 2 ^ 59
def prefixEnd_7690015 : Nat := 4983230072969 + 3 ^ 40 * 7690015 * 2
def baseEnd_7690015 : Nat := 3948673935284835514646771

theorem tailTrace_7690015 : CollatzResearch.WordTrace tailWord_7690015 prefixEnd_7690015 3948673935284835514646771 := by
  unfold tailWord_7690015
  simp only [CollatzResearch.WordTrace]
  refine ⟨280477889235396479845975499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186985259490264319897316999 280477889235396479845975499)
  ·
    refine ⟨420716833853094719768963249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280477889235396479845975499 420716833853094719768963249)
    ·
      refine ⟨315537625389821039826722437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420716833853094719768963249 315537625389821039826722437)
      ·
        refine ⟨59163304760591444967510457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315537625389821039826722437 59163304760591444967510457)
        ·
          refine ⟨44372478570443583725632843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59163304760591444967510457 44372478570443583725632843)
          ·
            refine ⟨66558717855665375588449265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44372478570443583725632843 66558717855665375588449265)
            ·
              refine ⟨49919038391749031691336949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66558717855665375588449265 49919038391749031691336949)
              ·
                refine ⟨4679909849226471721062839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49919038391749031691336949 4679909849226471721062839)
                ·
                  refine ⟨7019864773839707581594259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4679909849226471721062839 7019864773839707581594259)
                  ·
                    refine ⟨10529797160759561372391389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7019864773839707581594259 10529797160759561372391389)
                    ·
                      refine ⟨3948673935284835514646771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10529797160759561372391389 3948673935284835514646771)
                      ·
                        rfl

theorem cell23_7690015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_7690015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690015 prefixEnd_7690015 := by exact prefixLift 7690015
  have htrace : WordTrace (prefixWord ++ tailWord_7690015) baseStart_7690015 baseEnd_7690015 := by
    simpa [prefixWord, tailWord_7690015, baseEnd_7690015] using wordTrace_append hprefix tailTrace_7690015
  have hstable : (prefixWord ++ tailWord_7690015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690015).length < 2 ^ (prefixWord ++ tailWord_7690015).sum := by decide
  have hdescent : baseEnd_7690015 < baseStart_7690015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690051 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 4]
def baseStart_7690051 : Nat := 118140960795 + 7690051 * 2 ^ 59
def prefixEnd_7690051 : Nat := 4983230072969 + 3 ^ 40 * 7690051 * 2
def baseEnd_7690051 : Nat := 3948692420588397373796605

theorem tailTrace_7690051 : CollatzResearch.WordTrace tailWord_7690051 prefixEnd_7690051 3948692420588397373796605 := by
  unfold tailWord_7690051
  simp only [CollatzResearch.WordTrace]
  refine ⟨280479202263266057994286007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186986134842177371996190671 280479202263266057994286007)
  ·
    refine ⟨420718803394899086991429011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280479202263266057994286007 420718803394899086991429011)
    ·
      refine ⟨631078205092348630487143517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420718803394899086991429011 631078205092348630487143517)
      ·
        refine ⟨236654326909630736432678819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631078205092348630487143517 236654326909630736432678819)
        ·
          refine ⟨354981490364446104649018229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236654326909630736432678819 354981490364446104649018229)
          ·
            refine ⟨33279514721666822310845459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 354981490364446104649018229 33279514721666822310845459)
            ·
              refine ⟨49919272082500233466268189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33279514721666822310845459 49919272082500233466268189)
              ·
                refine ⟨18719727030937587549850571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49919272082500233466268189 18719727030937587549850571)
                ·
                  refine ⟨28079590546406381324775857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18719727030937587549850571 28079590546406381324775857)
                  ·
                    refine ⟨21059692909804785993581893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28079590546406381324775857 21059692909804785993581893)
                    ·
                      refine ⟨3948692420588397373796605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21059692909804785993581893 3948692420588397373796605)
                      ·
                        rfl

theorem cell23_7690051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_7690051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690051 prefixEnd_7690051 := by exact prefixLift 7690051
  have htrace : WordTrace (prefixWord ++ tailWord_7690051) baseStart_7690051 baseEnd_7690051 := by
    simpa [prefixWord, tailWord_7690051, baseEnd_7690051] using wordTrace_append hprefix tailTrace_7690051
  have hstable : (prefixWord ++ tailWord_7690051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690051).length < 2 ^ (prefixWord ++ tailWord_7690051).sum := by decide
  have hdescent : baseEnd_7690051 < baseStart_7690051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690058 : List Nat := [3, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_7690058 : Nat := 118140960795 + 7690058 * 2 ^ 59
def prefixEnd_7690058 : Nat := 4983230072969 + 3 ^ 40 * 7690058 * 2
def baseEnd_7690058 : Nat := 3948696014952978846409073

theorem tailTrace_7690058 : CollatzResearch.WordTrace tailWord_7690058 prefixEnd_7690058 3948696014952978846409073 := by
  unfold tailWord_7690058
  simp only [CollatzResearch.WordTrace]
  refine ⟨70119864393560174547447707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186986305049493798793193885 70119864393560174547447707)
  ·
    refine ⟨105179796590340261821171561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70119864393560174547447707 105179796590340261821171561)
    ·
      refine ⟨78884847442755196365878671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105179796590340261821171561 78884847442755196365878671)
      ·
        refine ⟨118327271164132794548818007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78884847442755196365878671 118327271164132794548818007)
        ·
          refine ⟨177490906746199191823227011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118327271164132794548818007 177490906746199191823227011)
          ·
            refine ⟨266236360119298787734840517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177490906746199191823227011 266236360119298787734840517)
            ·
              refine ⟨49919317522368522700282597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266236360119298787734840517 49919317522368522700282597)
              ·
                refine ⟨9359872035444098006302987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49919317522368522700282597 9359872035444098006302987)
                ·
                  refine ⟨14039808053166147009454481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359872035444098006302987 14039808053166147009454481)
                  ·
                    refine ⟨10529856039874610257090861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14039808053166147009454481 10529856039874610257090861)
                    ·
                      refine ⟨3948696014952978846409073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10529856039874610257090861 3948696014952978846409073)
                      ·
                        rfl

theorem cell23_7690058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_7690058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690058 prefixEnd_7690058 := by exact prefixLift 7690058
  have htrace : WordTrace (prefixWord ++ tailWord_7690058) baseStart_7690058 baseEnd_7690058 := by
    simpa [prefixWord, tailWord_7690058, baseEnd_7690058] using wordTrace_append hprefix tailTrace_7690058
  have hstable : (prefixWord ++ tailWord_7690058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690058).length < 2 ^ (prefixWord ++ tailWord_7690058).sum := by decide
  have hdescent : baseEnd_7690058 < baseStart_7690058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690068 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_7690068 : Nat := 118140960795 + 7690068 * 2 ^ 59
def prefixEnd_7690068 : Nat := 4983230072969 + 3 ^ 40 * 7690068 * 2
def baseEnd_7690068 : Nat := 3948701149759523807284027

theorem tailTrace_7690068 : CollatzResearch.WordTrace tailWord_7690068 prefixEnd_7690068 3948701149759523807284027 := by
  unfold tailWord_7690068
  simp only [CollatzResearch.WordTrace]
  refine ⟨140239911152102234948827429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186986548202802979931769905 140239911152102234948827429)
  ·
    refine ⟨26294983341019169052905143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140239911152102234948827429 26294983341019169052905143)
    ·
      refine ⟨39442475011528753579357715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26294983341019169052905143 39442475011528753579357715)
      ·
        refine ⟨59163712517293130369036573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39442475011528753579357715 59163712517293130369036573)
        ·
          refine ⟨22186392193984923888388715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59163712517293130369036573 22186392193984923888388715)
          ·
            refine ⟨33279588290977385832583073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22186392193984923888388715 33279588290977385832583073)
            ·
              refine ⟨24959691218233039374437305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33279588290977385832583073 24959691218233039374437305)
              ·
                refine ⟨18719768413674779530827979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24959691218233039374437305 18719768413674779530827979)
                ·
                  refine ⟨28079652620512169296241969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18719768413674779530827979 28079652620512169296241969)
                  ·
                    refine ⟨21059739465384126972181477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28079652620512169296241969 21059739465384126972181477)
                    ·
                      refine ⟨3948701149759523807284027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21059739465384126972181477 3948701149759523807284027)
                      ·
                        rfl

theorem cell23_7690068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_7690068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690068 prefixEnd_7690068 := by exact prefixLift 7690068
  have htrace : WordTrace (prefixWord ++ tailWord_7690068) baseStart_7690068 baseEnd_7690068 := by
    simpa [prefixWord, tailWord_7690068, baseEnd_7690068] using wordTrace_append hprefix tailTrace_7690068
  have hstable : (prefixWord ++ tailWord_7690068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690068).length < 2 ^ (prefixWord ++ tailWord_7690068).sum := by decide
  have hdescent : baseEnd_7690068 < baseStart_7690068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690082 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7690082 : Nat := 118140960795 + 7690082 * 2 ^ 59
def prefixEnd_7690082 : Nat := 4983230072969 + 3 ^ 40 * 7690082 * 2
def baseEnd_7690082 : Nat := 1316236112829562250836321

theorem tailTrace_7690082 : CollatzResearch.WordTrace tailWord_7690082 prefixEnd_7690082 1316236112829562250836321 := by
  unfold tailWord_7690082
  simp only [CollatzResearch.WordTrace]
  refine ⟨70120083231538437572166125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186986888617435833525776333 70120083231538437572166125)
  ·
    refine ⟨26295031211826914089562297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70120083231538437572166125 26295031211826914089562297)
    ·
      refine ⟨19721273408870185567171723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26295031211826914089562297 19721273408870185567171723)
      ·
        refine ⟨29581910113305278350757585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19721273408870185567171723 29581910113305278350757585)
        ·
          refine ⟨22186432584978958763068189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29581910113305278350757585 22186432584978958763068189)
          ·
            refine ⟨8319912219367109536150571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22186432584978958763068189 8319912219367109536150571)
            ·
              refine ⟨12479868329050664304225857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319912219367109536150571 12479868329050664304225857)
              ·
                refine ⟨9359901246787998228169393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12479868329050664304225857 9359901246787998228169393)
                ·
                  refine ⟨7019925935090998671127045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9359901246787998228169393 7019925935090998671127045)
                  ·
                    refine ⟨1316236112829562250836321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7019925935090998671127045 1316236112829562250836321)
                    ·
                      rfl

theorem cell23_7690082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7690082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690082 prefixEnd_7690082 := by exact prefixLift 7690082
  have htrace : WordTrace (prefixWord ++ tailWord_7690082) baseStart_7690082 baseEnd_7690082 := by
    simpa [prefixWord, tailWord_7690082, baseEnd_7690082] using wordTrace_append hprefix tailTrace_7690082
  have hstable : (prefixWord ++ tailWord_7690082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690082).length < 2 ^ (prefixWord ++ tailWord_7690082).sum := by decide
  have hdescent : baseEnd_7690082 < baseStart_7690082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690102 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7690102 : Nat := 118140960795 + 7690102 * 2 ^ 59
def prefixEnd_7690102 : Nat := 4983230072969 + 3 ^ 40 * 7690102 * 2
def baseEnd_7690102 : Nat := 3948718608101776674258871

theorem tailTrace_7690102 : CollatzResearch.WordTrace tailWord_7690102 prefixEnd_7690102 3948718608101776674258871 := by
  unfold tailWord_7690102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17530066399130080856524535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186987374924054195802928373 17530066399130080856524535)
  ·
    refine ⟨26295099598695121284786803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17530066399130080856524535 26295099598695121284786803)
    ·
      refine ⟨39442649398042681927180205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26295099598695121284786803 39442649398042681927180205)
      ·
        refine ⟨14790993524266005722692577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39442649398042681927180205 14790993524266005722692577)
        ·
          refine ⟨11093245143199504292019433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14790993524266005722692577 11093245143199504292019433)
          ·
            refine ⟨8319933857399628219014575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093245143199504292019433 8319933857399628219014575)
            ·
              refine ⟨12479900786099442328521863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8319933857399628219014575 12479900786099442328521863)
              ·
                refine ⟨18719851179149163492782795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12479900786099442328521863 18719851179149163492782795)
                ·
                  refine ⟨28079776768723745239174193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18719851179149163492782795 28079776768723745239174193)
                  ·
                    refine ⟨21059832576542808929380645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28079776768723745239174193 21059832576542808929380645)
                    ·
                      refine ⟨3948718608101776674258871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21059832576542808929380645 3948718608101776674258871)
                      ·
                        rfl

theorem cell23_7690102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7690102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690102 prefixEnd_7690102 := by exact prefixLift 7690102
  have htrace : WordTrace (prefixWord ++ tailWord_7690102) baseStart_7690102 baseEnd_7690102 := by
    simpa [prefixWord, tailWord_7690102, baseEnd_7690102] using wordTrace_append hprefix tailTrace_7690102
  have hstable : (prefixWord ++ tailWord_7690102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690102).length < 2 ^ (prefixWord ++ tailWord_7690102).sum := by decide
  have hdescent : baseEnd_7690102 < baseStart_7690102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690115 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 1, 3, 2]
def baseStart_7690115 : Nat := 118140960795 + 7690115 * 2 ^ 59
def prefixEnd_7690115 : Nat := 4983230072969 + 3 ^ 40 * 7690115 * 2
def baseEnd_7690115 : Nat := 3948725283350285123396311

theorem tailTrace_7690115 : CollatzResearch.WordTrace tailWord_7690115 prefixEnd_7690115 3948725283350285123396311 := by
  unfold tailWord_7690115
  simp only [CollatzResearch.WordTrace]
  refine ⟨280481536535034196924615799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186987691023356131283077199 280481536535034196924615799)
  ·
    refine ⟨420722304802551295386923699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280481536535034196924615799 420722304802551295386923699)
    ·
      refine ⟨631083457203826943080385549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420722304802551295386923699 631083457203826943080385549)
      ·
        refine ⟨236656296451435103655144581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631083457203826943080385549 236656296451435103655144581)
        ·
          refine ⟨44373055584644081935339609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236656296451435103655144581 44373055584644081935339609)
          ·
            refine ⟨33279791688483061451504707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44373055584644081935339609 33279791688483061451504707)
            ·
              refine ⟨49919687532724592177257061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33279791688483061451504707 49919687532724592177257061)
              ·
                refine ⟨9359941412385861033235699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49919687532724592177257061 9359941412385861033235699)
                ·
                  refine ⟨14039912118578791549853549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359941412385861033235699 14039912118578791549853549)
                  ·
                    refine ⟨5264967044467046831195081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14039912118578791549853549 5264967044467046831195081)
                    ·
                      refine ⟨3948725283350285123396311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264967044467046831195081 3948725283350285123396311)
                      ·
                        rfl

theorem cell23_7690115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_7690115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690115 prefixEnd_7690115 := by exact prefixLift 7690115
  have htrace : WordTrace (prefixWord ++ tailWord_7690115) baseStart_7690115 baseEnd_7690115 := by
    simpa [prefixWord, tailWord_7690115, baseEnd_7690115] using wordTrace_append hprefix tailTrace_7690115
  have hstable : (prefixWord ++ tailWord_7690115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690115).length < 2 ^ (prefixWord ++ tailWord_7690115).sum := by decide
  have hdescent : baseEnd_7690115 < baseStart_7690115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690132 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_7690132 : Nat := 118140960795 + 7690132 * 2 ^ 59
def prefixEnd_7690132 : Nat := 4983230072969 + 3 ^ 40 * 7690132 * 2
def baseEnd_7690132 : Nat := 3948734012521411556883733

theorem tailTrace_7690132 : CollatzResearch.WordTrace tailWord_7690132 prefixEnd_7690132 3948734012521411556883733 := by
  unfold tailWord_7690132
  simp only [CollatzResearch.WordTrace]
  refine ⟨140241078287986304413992325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186988104383981739218656433 140241078287986304413992325)
  ·
    refine ⟨26295202178997432077623561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140241078287986304413992325 26295202178997432077623561)
    ·
      refine ⟨19721401634248074058217671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26295202178997432077623561 19721401634248074058217671)
      ·
        refine ⟨29582102451372111087326507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19721401634248074058217671 29582102451372111087326507)
        ·
          refine ⟨44373153677058166630989761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29582102451372111087326507 44373153677058166630989761)
          ·
            refine ⟨33279865257793624973242321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44373153677058166630989761 33279865257793624973242321)
            ·
              refine ⟨24959898943345218729931741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33279865257793624973242321 24959898943345218729931741)
              ·
                refine ⟨9359962103754457023724403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24959898943345218729931741 9359962103754457023724403)
                ·
                  refine ⟨14039943155631685535586605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9359962103754457023724403 14039943155631685535586605)
                  ·
                    refine ⟨5264978683361882075844977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14039943155631685535586605 5264978683361882075844977)
                    ·
                      refine ⟨3948734012521411556883733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5264978683361882075844977 3948734012521411556883733)
                      ·
                        rfl

theorem cell23_7690132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_7690132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690132 prefixEnd_7690132 := by exact prefixLift 7690132
  have htrace : WordTrace (prefixWord ++ tailWord_7690132) baseStart_7690132 baseEnd_7690132 := by
    simpa [prefixWord, tailWord_7690132, baseEnd_7690132] using wordTrace_append hprefix tailTrace_7690132
  have hstable : (prefixWord ++ tailWord_7690132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690132).length < 2 ^ (prefixWord ++ tailWord_7690132).sum := by decide
  have hdescent : baseEnd_7690132 < baseStart_7690132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690191 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_7690191 : Nat := 118140960795 + 7690191 * 2 ^ 59
def prefixEnd_7690191 : Nat := 4983230072969 + 3 ^ 40 * 7690191 * 2
def baseEnd_7690191 : Nat := 3948764307880026826045961

theorem tailTrace_7690191 : CollatzResearch.WordTrace tailWord_7690191 prefixEnd_7690191 3948764307880026826045961 := by
  unfold tailWord_7690191
  simp only [CollatzResearch.WordTrace]
  refine ⟨280484308482758861904382427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186989538988505907936254951 280484308482758861904382427)
  ·
    refine ⟨420726462724138292856573641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280484308482758861904382427 420726462724138292856573641)
    ·
      refine ⟨315544847043103719642430231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420726462724138292856573641 315544847043103719642430231)
      ·
        refine ⟨473317270564655579463645347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315544847043103719642430231 473317270564655579463645347)
        ·
          refine ⟨709975905846983369195468021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473317270564655579463645347 709975905846983369195468021)
          ·
            refine ⟨66560241173154690862075127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 709975905846983369195468021 66560241173154690862075127)
            ·
              refine ⟨99840361759732036293112691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66560241173154690862075127 99840361759732036293112691)
              ·
                refine ⟨149760542639598054439669037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99840361759732036293112691 149760542639598054439669037)
                ·
                  refine ⟨56160203489849270414875889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149760542639598054439669037 56160203489849270414875889)
                  ·
                    refine ⟨42120152617386952811156917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56160203489849270414875889 42120152617386952811156917)
                    ·
                      refine ⟨3948764307880026826045961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42120152617386952811156917 3948764307880026826045961)
                      ·
                        rfl

theorem cell23_7690191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_7690191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690191 prefixEnd_7690191 := by exact prefixLift 7690191
  have htrace : WordTrace (prefixWord ++ tailWord_7690191) baseStart_7690191 baseEnd_7690191 := by
    simpa [prefixWord, tailWord_7690191, baseEnd_7690191] using wordTrace_append hprefix tailTrace_7690191
  have hstable : (prefixWord ++ tailWord_7690191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690191).length < 2 ^ (prefixWord ++ tailWord_7690191).sum := by decide
  have hdescent : baseEnd_7690191 < baseStart_7690191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690218 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_7690218 : Nat := 118140960795 + 7690218 * 2 ^ 59
def prefixEnd_7690218 : Nat := 4983230072969 + 3 ^ 40 * 7690218 * 2
def baseEnd_7690218 : Nat := 3948778171857698220408337

theorem tailTrace_7690218 : CollatzResearch.WordTrace tailWord_7690218 prefixEnd_7690218 3948778171857698220408337 := by
  unfold tailWord_7690218
  simp only [CollatzResearch.WordTrace]
  refine ⟨70121323313415261378903827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186990195502440697010410205 70121323313415261378903827)
  ·
    refine ⟨105181984970122892068355741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70121323313415261378903827 105181984970122892068355741)
    ·
      refine ⟨39443244363796084525633403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105181984970122892068355741 39443244363796084525633403)
      ·
        refine ⟨59164866545694126788450105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39443244363796084525633403 59164866545694126788450105)
        ·
          refine ⟨44373649909270595091337579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59164866545694126788450105 44373649909270595091337579)
          ·
            refine ⟨66560474863905892637006369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44373649909270595091337579 66560474863905892637006369)
            ·
              refine ⟨49920356147929419477754777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66560474863905892637006369 49920356147929419477754777)
              ·
                refine ⟨37440267110947064608316083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49920356147929419477754777 37440267110947064608316083)
                ·
                  refine ⟨56160400666420596912474125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37440267110947064608316083 56160400666420596912474125)
                  ·
                    refine ⟨21060150249907723842177797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56160400666420596912474125 21060150249907723842177797)
                    ·
                      refine ⟨3948778171857698220408337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21060150249907723842177797 3948778171857698220408337)
                      ·
                        rfl

theorem cell23_7690218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_7690218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690218 prefixEnd_7690218 := by exact prefixLift 7690218
  have htrace : WordTrace (prefixWord ++ tailWord_7690218) baseStart_7690218 baseEnd_7690218 := by
    simpa [prefixWord, tailWord_7690218, baseEnd_7690218] using wordTrace_append hprefix tailTrace_7690218
  have hstable : (prefixWord ++ tailWord_7690218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690218).length < 2 ^ (prefixWord ++ tailWord_7690218).sum := by decide
  have hdescent : baseEnd_7690218 < baseStart_7690218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690231 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_7690231 : Nat := 118140960795 + 7690231 * 2 ^ 59
def prefixEnd_7690231 : Nat := 4983230072969 + 3 ^ 40 * 7690231 * 2
def baseEnd_7690231 : Nat := 3948784847106206669545777

theorem tailTrace_7690231 : CollatzResearch.WordTrace tailWord_7690231 prefixEnd_7690231 3948784847106206669545777 := by
  unfold tailWord_7690231
  simp only [CollatzResearch.WordTrace]
  refine ⟨280485767402613948735838547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186990511601742632490559031 280485767402613948735838547)
  ·
    refine ⟨420728651103920923103757821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280485767402613948735838547 420728651103920923103757821)
    ·
      refine ⟨157773244163970346163909183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420728651103920923103757821 157773244163970346163909183)
      ·
        refine ⟨236659866245955519245863775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157773244163970346163909183 236659866245955519245863775)
        ·
          refine ⟨354989799368933278868795663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236659866245955519245863775 354989799368933278868795663)
          ·
            refine ⟨532484699053399918303193495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354989799368933278868795663 532484699053399918303193495)
            ·
              refine ⟨798727048580099877454790243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532484699053399918303193495 798727048580099877454790243)
              ·
                refine ⟨1198090572870149816182185365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798727048580099877454790243 1198090572870149816182185365)
                ·
                  refine ⟨56160495603288272633539939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1198090572870149816182185365 56160495603288272633539939)
                  ·
                    refine ⟨84240743404932408950309909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56160495603288272633539939 84240743404932408950309909)
                    ·
                      refine ⟨3948784847106206669545777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84240743404932408950309909 3948784847106206669545777)
                      ·
                        rfl

theorem cell23_7690231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_7690231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690231 prefixEnd_7690231 := by exact prefixLift 7690231
  have htrace : WordTrace (prefixWord ++ tailWord_7690231) baseStart_7690231 baseEnd_7690231 := by
    simpa [prefixWord, tailWord_7690231, baseEnd_7690231] using wordTrace_append hprefix tailTrace_7690231
  have hstable : (prefixWord ++ tailWord_7690231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690231).length < 2 ^ (prefixWord ++ tailWord_7690231).sum := by decide
  have hdescent : baseEnd_7690231 < baseStart_7690231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690275 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 6]
def baseStart_7690275 : Nat := 118140960795 + 7690275 * 2 ^ 59
def prefixEnd_7690275 : Nat := 4983230072969 + 3 ^ 40 * 7690275 * 2
def baseEnd_7690275 : Nat := 438756382250556055266175

theorem tailTrace_7690275 : CollatzResearch.WordTrace tailWord_7690275 prefixEnd_7690275 438756382250556055266175 := by
  unfold tailWord_7690275
  simp only [CollatzResearch.WordTrace]
  refine ⟨280487372214454544250440279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186991581476303029500293519 280487372214454544250440279)
  ·
    refine ⟨420731058321681816375660419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280487372214454544250440279 420731058321681816375660419)
    ·
      refine ⟨631096587482522724563490629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420731058321681816375660419 631096587482522724563490629)
      ·
        refine ⟨118330610152973010855654493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 631096587482522724563490629 118330610152973010855654493)
        ·
          refine ⟨44373978807364879070870435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118330610152973010855654493 44373978807364879070870435)
          ·
            refine ⟨66560968211047318606305653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44373978807364879070870435 66560968211047318606305653)
            ·
              refine ⟨6240090769785686119341155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66560968211047318606305653 6240090769785686119341155)
              ·
                refine ⟨9360136154678529179011733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240090769785686119341155 9360136154678529179011733)
                ·
                  refine ⟨438756382250556055266175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9360136154678529179011733 438756382250556055266175)
                  ·
                    rfl

theorem cell23_7690275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 6].length) (baseStart_7690275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690275 prefixEnd_7690275 := by exact prefixLift 7690275
  have htrace : WordTrace (prefixWord ++ tailWord_7690275) baseStart_7690275 baseEnd_7690275 := by
    simpa [prefixWord, tailWord_7690275, baseEnd_7690275] using wordTrace_append hprefix tailTrace_7690275
  have hstable : (prefixWord ++ tailWord_7690275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690275).length < 2 ^ (prefixWord ++ tailWord_7690275).sum := by decide
  have hdescent : baseEnd_7690275 < baseStart_7690275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690295 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 1, 5, 2]
def baseStart_7690295 : Nat := 118140960795 + 7690295 * 2 ^ 59
def prefixEnd_7690295 : Nat := 4983230072969 + 3 ^ 40 * 7690295 * 2
def baseEnd_7690295 : Nat := 3948817709868094419145483

theorem tailTrace_7690295 : CollatzResearch.WordTrace tailWord_7690295 prefixEnd_7690295 3948817709868094419145483 := by
  unfold tailWord_7690295
  simp only [CollatzResearch.WordTrace]
  refine ⟨280488101674382087666168339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186992067782921391777445559 280488101674382087666168339)
  ·
    refine ⟨420732152511573131499252509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280488101674382087666168339 420732152511573131499252509)
    ·
      refine ⟨157774557191839924312219691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420732152511573131499252509 157774557191839924312219691)
      ·
        refine ⟨236661835787759886468329537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157774557191839924312219691 236661835787759886468329537)
        ·
          refine ⟨177496376840819914851247153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236661835787759886468329537 177496376840819914851247153)
          ·
            refine ⟨133122282630614936138435365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177496376840819914851247153 133122282630614936138435365)
            ·
              refine ⟨24960427993240300525956631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133122282630614936138435365 24960427993240300525956631)
              ·
                refine ⟨37440641989860450788934947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24960427993240300525956631 37440641989860450788934947)
                ·
                  refine ⟨56160962984790676183402421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37440641989860450788934947 56160962984790676183402421)
                  ·
                    refine ⟨5265090279824125892193977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56160962984790676183402421 5265090279824125892193977)
                    ·
                      refine ⟨3948817709868094419145483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265090279824125892193977 3948817709868094419145483)
                      ·
                        rfl

theorem cell23_7690295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_7690295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690295 prefixEnd_7690295 := by exact prefixLift 7690295
  have htrace : WordTrace (prefixWord ++ tailWord_7690295) baseStart_7690295 baseEnd_7690295 := by
    simpa [prefixWord, tailWord_7690295, baseEnd_7690295] using wordTrace_append hprefix tailTrace_7690295
  have hstable : (prefixWord ++ tailWord_7690295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690295).length < 2 ^ (prefixWord ++ tailWord_7690295).sum := by decide
  have hdescent : baseEnd_7690295 < baseStart_7690295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690296 : List Nat := [2, 1, 2, 1, 7, 1, 1, 3, 1, 4]
def baseStart_7690296 : Nat := 118140960795 + 7690296 * 2 ^ 59
def prefixEnd_7690296 : Nat := 4983230072969 + 3 ^ 40 * 7690296 * 2
def baseEnd_7690296 : Nat := 1316272741116249638410993

theorem tailTrace_7690296 : CollatzResearch.WordTrace tailWord_7690296 prefixEnd_7690296 1316272741116249638410993 := by
  unfold tailWord_7690296
  simp only [CollatzResearch.WordTrace]
  refine ⟨140244069073689232418477371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186992092098252309891303161 140244069073689232418477371)
  ·
    refine ⟨210366103610533848627716057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140244069073689232418477371 210366103610533848627716057)
    ·
      refine ⟨157774577707900386470787043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210366103610533848627716057 157774577707900386470787043)
      ·
        refine ⟨236661866561850579706180565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157774577707900386470787043 236661866561850579706180565)
        ·
          refine ⟨5546762497543372961863607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 236661866561850579706180565 5546762497543372961863607)
          ·
            refine ⟨8320143746315059442795411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5546762497543372961863607 8320143746315059442795411)
            ·
              refine ⟨12480215619472589164193117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8320143746315059442795411 12480215619472589164193117)
              ·
                refine ⟨4680080857302220936572419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12480215619472589164193117 4680080857302220936572419)
                ·
                  refine ⟨7020121285953331404858629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680080857302220936572419 7020121285953331404858629)
                  ·
                    refine ⟨1316272741116249638410993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020121285953331404858629 1316272741116249638410993)
                    ·
                      rfl

theorem cell23_7690296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_7690296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690296 prefixEnd_7690296 := by exact prefixLift 7690296
  have htrace : WordTrace (prefixWord ++ tailWord_7690296) baseStart_7690296 baseEnd_7690296 := by
    simpa [prefixWord, tailWord_7690296, baseEnd_7690296] using wordTrace_append hprefix tailTrace_7690296
  have hstable : (prefixWord ++ tailWord_7690296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690296).length < 2 ^ (prefixWord ++ tailWord_7690296).sum := by decide
  have hdescent : baseEnd_7690296 < baseStart_7690296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690326 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_7690326 : Nat := 118140960795 + 7690326 * 2 ^ 59
def prefixEnd_7690326 : Nat := 4983230072969 + 3 ^ 40 * 7690326 * 2
def baseEnd_7690326 : Nat := 438759291974264866428649

theorem tailTrace_7690326 : CollatzResearch.WordTrace tailWord_7690326 prefixEnd_7690326 438759291974264866428649 := by
  unfold tailWord_7690326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17530577021079361247534177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186992821558179853307031221 17530577021079361247534177)
  ·
    refine ⟨13147932765809520935650633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17530577021079361247534177 13147932765809520935650633)
    ·
      refine ⟨9860949574357140701737975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13147932765809520935650633 9860949574357140701737975)
      ·
        refine ⟨14791424361535711052606963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9860949574357140701737975 14791424361535711052606963)
        ·
          refine ⟨22187136542303566578910445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14791424361535711052606963 22187136542303566578910445)
          ·
            refine ⟨8320176203363837467091417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22187136542303566578910445 8320176203363837467091417)
            ·
              refine ⟨6240132152522878100318563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8320176203363837467091417 6240132152522878100318563)
              ·
                refine ⟨9360198228784317150477845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240132152522878100318563 9360198228784317150477845)
                ·
                  refine ⟨438759291974264866428649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9360198228784317150477845 438759291974264866428649)
                  ·
                    rfl

theorem cell23_7690326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_7690326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690326 prefixEnd_7690326 := by exact prefixLift 7690326
  have htrace : WordTrace (prefixWord ++ tailWord_7690326) baseStart_7690326 baseEnd_7690326 := by
    simpa [prefixWord, tailWord_7690326, baseEnd_7690326] using wordTrace_append hprefix tailTrace_7690326
  have hstable : (prefixWord ++ tailWord_7690326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690326).length < 2 ^ (prefixWord ++ tailWord_7690326).sum := by decide
  have hdescent : baseEnd_7690326 < baseStart_7690326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690345 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 3]
def baseStart_7690345 : Nat := 118140960795 + 7690345 * 2 ^ 59
def prefixEnd_7690345 : Nat := 4983230072969 + 3 ^ 40 * 7690345 * 2
def baseEnd_7690345 : Nat := 3948843383900819223520253

theorem tailTrace_7690345 : CollatzResearch.WordTrace tailWord_7690345 prefixEnd_7690345 3948843383900819223520253 := by
  unfold tailWord_7690345
  simp only [CollatzResearch.WordTrace]
  refine ⟨280489925324200946205488489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186993283549467297470325659 280489925324200946205488489)
  ·
    refine ⟨210367443993150709654116367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280489925324200946205488489 210367443993150709654116367)
    ·
      refine ⟨315551165989726064481174551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210367443993150709654116367 315551165989726064481174551)
      ·
        refine ⟨473326748984589096721761827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315551165989726064481174551 473326748984589096721761827)
        ·
          refine ⟨709990123476883645082642741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473326748984589096721761827 709990123476883645082642741)
          ·
            refine ⟨66561574075957841726497757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 709990123476883645082642741 66561574075957841726497757)
            ·
              refine ⟨24960590278484190647436659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66561574075957841726497757 24960590278484190647436659)
              ·
                refine ⟨37440885417726285971154989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24960590278484190647436659 37440885417726285971154989)
                ·
                  refine ⟨14040332031647357239183121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37440885417726285971154989 14040332031647357239183121)
                  ·
                    refine ⟨10530249023735517929387341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14040332031647357239183121 10530249023735517929387341)
                    ·
                      refine ⟨3948843383900819223520253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10530249023735517929387341 3948843383900819223520253)
                      ·
                        rfl

theorem cell23_7690345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_7690345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690345 prefixEnd_7690345 := by exact prefixLift 7690345
  have htrace : WordTrace (prefixWord ++ tailWord_7690345) baseStart_7690345 baseEnd_7690345 := by
    simpa [prefixWord, tailWord_7690345, baseEnd_7690345] using wordTrace_append hprefix tailTrace_7690345
  have hstable : (prefixWord ++ tailWord_7690345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690345).length < 2 ^ (prefixWord ++ tailWord_7690345).sum := by decide
  have hdescent : baseEnd_7690345 < baseStart_7690345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690348 : List Nat := [2, 2, 1, 1, 3, 3, 2, 9]
def baseStart_7690348 : Nat := 118140960795 + 7690348 * 2 ^ 59
def prefixEnd_7690348 : Nat := 4983230072969 + 3 ^ 40 * 7690348 * 2
def baseEnd_7690348 : Nat := 146253515716399359695657

theorem tailTrace_7690348 : CollatzResearch.WordTrace tailWord_7690348 prefixEnd_7690348 146253515716399359695657 := by
  unfold tailWord_7690348
  simp only [CollatzResearch.WordTrace]
  refine ⟨140245017371595038858923849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186993356495460051811898465 140245017371595038858923849)
  ·
    refine ⟨105183763028696279144192887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140245017371595038858923849 105183763028696279144192887)
    ·
      refine ⟨157775644543044418716289331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105183763028696279144192887 157775644543044418716289331)
      ·
        refine ⟨236663466814566628074433997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157775644543044418716289331 236663466814566628074433997)
        ·
          refine ⟨88748800055462485527912749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236663466814566628074433997 88748800055462485527912749)
          ·
            refine ⟨33280800020798432072967281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88748800055462485527912749 33280800020798432072967281)
            ·
              refine ⟨24960600015598824054725461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33280800020798432072967281 24960600015598824054725461)
              ·
                refine ⟨146253515716399359695657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24960600015598824054725461 146253515716399359695657)
                ·
                  rfl

theorem cell23_7690348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 9].length) (baseStart_7690348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690348 prefixEnd_7690348 := by exact prefixLift 7690348
  have htrace : WordTrace (prefixWord ++ tailWord_7690348) baseStart_7690348 baseEnd_7690348 := by
    simpa [prefixWord, tailWord_7690348, baseEnd_7690348] using wordTrace_append hprefix tailTrace_7690348
  have hstable : (prefixWord ++ tailWord_7690348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690348).length < 2 ^ (prefixWord ++ tailWord_7690348).sum := by decide
  have hdescent : baseEnd_7690348 < baseStart_7690348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690369 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 2, 4]
def baseStart_7690369 : Nat := 118140960795 + 7690369 * 2 ^ 59
def prefixEnd_7690369 : Nat := 4983230072969 + 3 ^ 40 * 7690369 * 2
def baseEnd_7690369 : Nat := 1316285235812175709873381

theorem tailTrace_7690369 : CollatzResearch.WordTrace tailWord_7690369 prefixEnd_7690369 1316285235812175709873381 := by
  unfold tailWord_7690369
  simp only [CollatzResearch.WordTrace]
  refine ⟨280490800676113998304362161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186993867117409332202908107 280490800676113998304362161)
  ·
    refine ⟨210368100507085498728271621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280490800676113998304362161 210368100507085498728271621)
    ·
      refine ⟨39444018845078531011550929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210368100507085498728271621 39444018845078531011550929)
      ·
        refine ⟨29583014133808898258663197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39444018845078531011550929 29583014133808898258663197)
        ·
          refine ⟨11093630300178336846998699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29583014133808898258663197 11093630300178336846998699)
          ·
            refine ⟨16640445450267505270498049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11093630300178336846998699 16640445450267505270498049)
            ·
              refine ⟨12480334087700628952873537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16640445450267505270498049 12480334087700628952873537)
              ·
                refine ⟨9360250565775471714655153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12480334087700628952873537 9360250565775471714655153)
                ·
                  refine ⟨7020187924331603785991365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9360250565775471714655153 7020187924331603785991365)
                  ·
                    refine ⟨1316285235812175709873381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020187924331603785991365 1316285235812175709873381)
                    ·
                      rfl

theorem cell23_7690369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_7690369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690369 prefixEnd_7690369 := by exact prefixLift 7690369
  have htrace : WordTrace (prefixWord ++ tailWord_7690369) baseStart_7690369 baseEnd_7690369 := by
    simpa [prefixWord, tailWord_7690369, baseEnd_7690369] using wordTrace_append hprefix tailTrace_7690369
  have hstable : (prefixWord ++ tailWord_7690369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690369).length < 2 ^ (prefixWord ++ tailWord_7690369).sum := by decide
  have hdescent : baseEnd_7690369 < baseStart_7690369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690382 : List Nat := [4, 1, 1, 3, 3, 2, 1, 8]
def baseStart_7690382 : Nat := 118140960795 + 7690382 * 2 ^ 59
def prefixEnd_7690382 : Nat := 4983230072969 + 3 ^ 40 * 7690382 * 2
def baseEnd_7690382 : Nat := 146254162321667984398429

theorem tailTrace_7690382 : CollatzResearch.WordTrace tailWord_7690382 prefixEnd_7690382 146254162321667984398429 := by
  unfold tailWord_7690382
  simp only [CollatzResearch.WordTrace]
  refine ⟨35061409353133362690573175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186994183216711267683056933 35061409353133362690573175)
  ·
    refine ⟨52592114029700044035859763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35061409353133362690573175 52592114029700044035859763)
    ·
      refine ⟨78888171044550066053789645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52592114029700044035859763 78888171044550066053789645)
      ·
        refine ⟨29583064141706274770171117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78888171044550066053789645 29583064141706274770171117)
        ·
          refine ⟨11093649053139853038814169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29583064141706274770171117 11093649053139853038814169)
          ·
            refine ⟨8320236789854889779110627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093649053139853038814169 8320236789854889779110627)
            ·
              refine ⟨12480355184782334668665941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8320236789854889779110627 12480355184782334668665941)
              ·
                refine ⟨146254162321667984398429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12480355184782334668665941 146254162321667984398429)
                ·
                  rfl

theorem cell23_7690382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_7690382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690382 prefixEnd_7690382 := by exact prefixLift 7690382
  have htrace : WordTrace (prefixWord ++ tailWord_7690382) baseStart_7690382 baseEnd_7690382 := by
    simpa [prefixWord, tailWord_7690382, baseEnd_7690382] using wordTrace_append hprefix tailTrace_7690382
  have hstable : (prefixWord ++ tailWord_7690382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690382).length < 2 ^ (prefixWord ++ tailWord_7690382).sum := by decide
  have hdescent : baseEnd_7690382 < baseStart_7690382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690410 : List Nat := [3, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_7690410 : Nat := 118140960795 + 7690410 * 2 ^ 59
def prefixEnd_7690410 : Nat := 4983230072969 + 3 ^ 40 * 7690410 * 2
def baseEnd_7690410 : Nat := 3948876760143361469207455

theorem tailTrace_7690410 : CollatzResearch.WordTrace tailWord_7690410 prefixEnd_7690410 3948876760143361469207455 := by
  unfold tailWord_7690410
  simp only [CollatzResearch.WordTrace]
  refine ⟨70123074017241365576651171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186994864045976974871069789 70123074017241365576651171)
  ·
    refine ⟨105184611025862048364976757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70123074017241365576651171 105184611025862048364976757)
    ·
      refine ⟨9861057283674567034216571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105184611025862048364976757 9861057283674567034216571)
      ·
        refine ⟨14791585925511850551324857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9861057283674567034216571 14791585925511850551324857)
        ·
          refine ⟨11093689444133887913493643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14791585925511850551324857 11093689444133887913493643)
          ·
            refine ⟨16640534166200831870240465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11093689444133887913493643 16640534166200831870240465)
            ·
              refine ⟨12480400624650623902680349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16640534166200831870240465 12480400624650623902680349)
              ·
                refine ⟨4680150234243983963505131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12480400624650623902680349 4680150234243983963505131)
                ·
                  refine ⟨7020225351365975945257697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680150234243983963505131 7020225351365975945257697)
                  ·
                    refine ⟨5265169013524481958943273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7020225351365975945257697 5265169013524481958943273)
                    ·
                      refine ⟨3948876760143361469207455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265169013524481958943273 3948876760143361469207455)
                      ·
                        rfl

theorem cell23_7690410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_7690410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690410 prefixEnd_7690410 := by exact prefixLift 7690410
  have htrace : WordTrace (prefixWord ++ tailWord_7690410) baseStart_7690410 baseEnd_7690410 := by
    simpa [prefixWord, tailWord_7690410, baseEnd_7690410] using wordTrace_append hprefix tailTrace_7690410
  have hstable : (prefixWord ++ tailWord_7690410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690410).length < 2 ^ (prefixWord ++ tailWord_7690410).sum := by decide
  have hdescent : baseEnd_7690410 < baseStart_7690410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690420 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7690420 : Nat := 118140960795 + 7690420 * 2 ^ 59
def prefixEnd_7690420 : Nat := 4983230072969 + 3 ^ 40 * 7690420 * 2
def baseEnd_7690420 : Nat := 1316293964983302143360803

theorem tailTrace_7690420 : CollatzResearch.WordTrace tailWord_7690420 prefixEnd_7690420 1316293964983302143360803 := by
  unfold tailWord_7690420
  simp only [CollatzResearch.WordTrace]
  refine ⟨140246330399464617007234357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186995107199286156009645809 140246330399464617007234357)
  ·
    refine ⟨13148093474949807844428221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140246330399464617007234357 13148093474949807844428221)
    ·
      refine ⟨4930535053106177941660583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13148093474949807844428221 4930535053106177941660583)
      ·
        refine ⟨7395802579659266912490875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4930535053106177941660583 7395802579659266912490875)
        ·
          refine ⟨11093703869488900368736313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7395802579659266912490875 11093703869488900368736313)
          ·
            refine ⟨8320277902116675276552235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093703869488900368736313 8320277902116675276552235)
            ·
              refine ⟨12480416853175012914828353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8320277902116675276552235 12480416853175012914828353)
              ·
                refine ⟨9360312639881259686121265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12480416853175012914828353 9360312639881259686121265)
                ·
                  refine ⟨7020234479910944764590949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9360312639881259686121265 7020234479910944764590949)
                  ·
                    refine ⟨1316293964983302143360803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020234479910944764590949 1316293964983302143360803)
                    ·
                      rfl

theorem cell23_7690420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7690420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690420 prefixEnd_7690420 := by exact prefixLift 7690420
  have htrace : WordTrace (prefixWord ++ tailWord_7690420) baseStart_7690420 baseEnd_7690420 := by
    simpa [prefixWord, tailWord_7690420, baseEnd_7690420] using wordTrace_append hprefix tailTrace_7690420
  have hstable : (prefixWord ++ tailWord_7690420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690420).length < 2 ^ (prefixWord ++ tailWord_7690420).sum := by decide
  have hdescent : baseEnd_7690420 < baseStart_7690420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690448 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_7690448 : Nat := 118140960795 + 7690448 * 2 ^ 59
def prefixEnd_7690448 : Nat := 4983230072969 + 3 ^ 40 * 7690448 * 2
def baseEnd_7690448 : Nat := 3948896272408232320532279

theorem tailTrace_7690448 : CollatzResearch.WordTrace tailWord_7690448 prefixEnd_7690448 3948896272408232320532279 := by
  unfold tailWord_7690448
  simp only [CollatzResearch.WordTrace]
  refine ⟨140246841021413897398243999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186995788028551863197658665 140246841021413897398243999)
  ·
    refine ⟨210370261532120846097365999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140246841021413897398243999 210370261532120846097365999)
    ·
      refine ⟨315555392298181269146048999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210370261532120846097365999 315555392298181269146048999)
      ·
        refine ⟨473333088447271903719073499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315555392298181269146048999 473333088447271903719073499)
        ·
          refine ⟨709999632670907855578610249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473333088447271903719073499 709999632670907855578610249)
          ·
            refine ⟨532499724503180891683957687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709999632670907855578610249 532499724503180891683957687)
            ·
              refine ⟨798749586754771337525936531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532499724503180891683957687 798749586754771337525936531)
              ·
                refine ⟨1198124380132157006288904797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798749586754771337525936531 1198124380132157006288904797)
                ·
                  refine ⟨449296642549558877358339299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1198124380132157006288904797 449296642549558877358339299)
                  ·
                    refine ⟨673944963824338316037508949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 449296642549558877358339299 673944963824338316037508949)
                    ·
                      refine ⟨3948896272408232320532279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 673944963824338316037508949 3948896272408232320532279)
                      ·
                        rfl

theorem cell23_7690448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_7690448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690448 prefixEnd_7690448 := by exact prefixLift 7690448
  have htrace : WordTrace (prefixWord ++ tailWord_7690448) baseStart_7690448 baseEnd_7690448 := by
    simpa [prefixWord, tailWord_7690448, baseEnd_7690448] using wordTrace_append hprefix tailTrace_7690448
  have hstable : (prefixWord ++ tailWord_7690448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690448).length < 2 ^ (prefixWord ++ tailWord_7690448).sum := by decide
  have hdescent : baseEnd_7690448 < baseStart_7690448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690449 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 2, 2, 2]
def baseStart_7690449 : Nat := 118140960795 + 7690449 * 2 ^ 59
def prefixEnd_7690449 : Nat := 4983230072969 + 3 ^ 40 * 7690449 * 2
def baseEnd_7690449 : Nat := 3948896785888886816619775

theorem tailTrace_7690449 : CollatzResearch.WordTrace tailWord_7690449 prefixEnd_7690449 3948896785888886816619775 := by
  unfold tailWord_7690449
  simp only [CollatzResearch.WordTrace]
  refine ⟨280493718515824171967274401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186995812343882781311516267 280493718515824171967274401)
  ·
    refine ⟨210370288886868128975455801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280493718515824171967274401 210370288886868128975455801)
    ·
      refine ⟨157777716665151096731591851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210370288886868128975455801 157777716665151096731591851)
      ·
        refine ⟨236666574997726645097387777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157777716665151096731591851 236666574997726645097387777)
        ·
          refine ⟨177499931248294983823040833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236666574997726645097387777 177499931248294983823040833)
          ·
            refine ⟨133124948436221237867280625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177499931248294983823040833 133124948436221237867280625)
            ·
              refine ⟨99843711327165928400460469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133124948436221237867280625 99843711327165928400460469)
              ·
                refine ⟨9360347936921805787543169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99843711327165928400460469 9360347936921805787543169)
                ·
                  refine ⟨7020260952691354340657377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9360347936921805787543169 7020260952691354340657377)
                  ·
                    refine ⟨5265195714518515755493033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7020260952691354340657377 5265195714518515755493033)
                    ·
                      refine ⟨3948896785888886816619775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265195714518515755493033 3948896785888886816619775)
                      ·
                        rfl

theorem cell23_7690449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_7690449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690449 prefixEnd_7690449 := by exact prefixLift 7690449
  have htrace : WordTrace (prefixWord ++ tailWord_7690449) baseStart_7690449 baseEnd_7690449 := by
    simpa [prefixWord, tailWord_7690449, baseEnd_7690449] using wordTrace_append hprefix tailTrace_7690449
  have hstable : (prefixWord ++ tailWord_7690449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690449).length < 2 ^ (prefixWord ++ tailWord_7690449).sum := by decide
  have hdescent : baseEnd_7690449 < baseStart_7690449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690495 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_7690495 : Nat := 118140960795 + 7690495 * 2 ^ 59
def prefixEnd_7690495 : Nat := 4983230072969 + 3 ^ 40 * 7690495 * 2
def baseEnd_7690495 : Nat := 3948920405998993636644563

theorem tailTrace_7690495 : CollatzResearch.WordTrace tailWord_7690495 prefixEnd_7690495 3948920405998993636644563 := by
  unfold tailWord_7690495
  simp only [CollatzResearch.WordTrace]
  refine ⟨280495396273657521823448939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186996930849105014548965959 280495396273657521823448939)
  ·
    refine ⟨420743094410486282735173409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280495396273657521823448939 420743094410486282735173409)
    ·
      refine ⟨315557320807864712051380057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420743094410486282735173409 315557320807864712051380057)
      ·
        refine ⟨236667990605898534038535043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315557320807864712051380057 236667990605898534038535043)
        ·
          refine ⟨355001985908847801057802565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236667990605898534038535043 355001985908847801057802565)
          ·
            refine ⟨66562872357908962698337981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355001985908847801057802565 66562872357908962698337981)
            ·
              refine ⟨24961077134215861011876743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66562872357908962698337981 24961077134215861011876743)
              ·
                refine ⟨37441615701323791517815115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24961077134215861011876743 37441615701323791517815115)
                ·
                  refine ⟨56162423551985687276722673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37441615701323791517815115 56162423551985687276722673)
                  ·
                    refine ⟨42121817663989265457542005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56162423551985687276722673 42121817663989265457542005)
                    ·
                      refine ⟨3948920405998993636644563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42121817663989265457542005 3948920405998993636644563)
                      ·
                        rfl

theorem cell23_7690495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_7690495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690495 prefixEnd_7690495 := by exact prefixLift 7690495
  have htrace : WordTrace (prefixWord ++ tailWord_7690495) baseStart_7690495 baseEnd_7690495 := by
    simpa [prefixWord, tailWord_7690495, baseEnd_7690495] using wordTrace_append hprefix tailTrace_7690495
  have hstable : (prefixWord ++ tailWord_7690495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690495).length < 2 ^ (prefixWord ++ tailWord_7690495).sum := by decide
  have hdescent : baseEnd_7690495 < baseStart_7690495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690500 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_7690500 : Nat := 118140960795 + 7690500 * 2 ^ 59
def prefixEnd_7690500 : Nat := 4983230072969 + 3 ^ 40 * 7690500 * 2
def baseEnd_7690500 : Nat := 3948922973402266117082041

theorem tailTrace_7690500 : CollatzResearch.WordTrace tailWord_7690500 prefixEnd_7690500 3948922973402266117082041 := by
  unfold tailWord_7690500
  simp only [CollatzResearch.WordTrace]
  refine ⟨140247789319319703838690477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186997052425759605118253969 140247789319319703838690477)
  ·
    refine ⟨52592920994744888939508929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140247789319319703838690477 52592920994744888939508929)
    ·
      refine ⟨39444690746058666704631697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52592920994744888939508929 39444690746058666704631697)
      ·
        refine ⟨29583518059544000028473773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39444690746058666704631697 29583518059544000028473773)
        ·
          refine ⟨11093819272329000010677665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29583518059544000028473773 11093819272329000010677665)
          ·
            refine ⟨8320364454246750008008249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11093819272329000010677665 8320364454246750008008249)
            ·
              refine ⟨6240273340685062506006187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8320364454246750008008249 6240273340685062506006187)
              ·
                refine ⟨9360410011027593759009281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240273340685062506006187 9360410011027593759009281)
                ·
                  refine ⟨7020307508270695319256961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9360410011027593759009281 7020307508270695319256961)
                  ·
                    refine ⟨5265230631203021489442721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7020307508270695319256961 5265230631203021489442721)
                    ·
                      refine ⟨3948922973402266117082041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265230631203021489442721 3948922973402266117082041)
                      ·
                        rfl

theorem cell23_7690500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_7690500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690500 prefixEnd_7690500 := by exact prefixLift 7690500
  have htrace : WordTrace (prefixWord ++ tailWord_7690500) baseStart_7690500 baseEnd_7690500 := by
    simpa [prefixWord, tailWord_7690500, baseEnd_7690500] using wordTrace_append hprefix tailTrace_7690500
  have hstable : (prefixWord ++ tailWord_7690500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690500).length < 2 ^ (prefixWord ++ tailWord_7690500).sum := by decide
  have hdescent : baseEnd_7690500 < baseStart_7690500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690585 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_7690585 : Nat := 118140960795 + 7690585 * 2 ^ 59
def prefixEnd_7690585 : Nat := 4983230072969 + 3 ^ 40 * 7690585 * 2
def baseEnd_7690585 : Nat := 3948966619257898284519149

theorem tailTrace_7690585 : CollatzResearch.WordTrace tailWord_7690585 prefixEnd_7690585 3948966619257898284519149 := by
  unfold tailWord_7690585
  simp only [CollatzResearch.WordTrace]
  refine ⟨280498678843331467194225209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186999119228887644796150139 280498678843331467194225209)
  ·
    refine ⟨210374009132498600395668907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280498678843331467194225209 210374009132498600395668907)
    ·
      refine ⟨315561013698747900593503361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210374009132498600395668907 315561013698747900593503361)
      ·
        refine ⟨236670760274060925445127521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315561013698747900593503361 236670760274060925445127521)
        ·
          refine ⟨177503070205545694083845641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236670760274060925445127521 177503070205545694083845641)
          ·
            refine ⟨133127302654159270562884231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177503070205545694083845641 133127302654159270562884231)
            ·
              refine ⟨199690953981238905844326347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133127302654159270562884231 199690953981238905844326347)
              ·
                refine ⟨299536430971858358766489521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199690953981238905844326347 299536430971858358766489521)
                ·
                  refine ⟨224652323228893769074867141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299536430971858358766489521 224652323228893769074867141)
                  ·
                    refine ⟨42122310605417581701537589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224652323228893769074867141 42122310605417581701537589)
                    ·
                      refine ⟨3948966619257898284519149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42122310605417581701537589 3948966619257898284519149)
                      ·
                        rfl

theorem cell23_7690585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_7690585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690585 prefixEnd_7690585 := by exact prefixLift 7690585
  have htrace : WordTrace (prefixWord ++ tailWord_7690585) baseStart_7690585 baseEnd_7690585 := by
    simpa [prefixWord, tailWord_7690585, baseEnd_7690585] using wordTrace_append hprefix tailTrace_7690585
  have hstable : (prefixWord ++ tailWord_7690585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690585).length < 2 ^ (prefixWord ++ tailWord_7690585).sum := by decide
  have hdescent : baseEnd_7690585 < baseStart_7690585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690632 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7690632 : Nat := 118140960795 + 7690632 * 2 ^ 59
def prefixEnd_7690632 : Nat := 4983230072969 + 3 ^ 40 * 7690632 * 2
def baseEnd_7690632 : Nat := 3948990752848659600631433

theorem tailTrace_7690632 : CollatzResearch.WordTrace tailWord_7690632 prefixEnd_7690632 3948990752848659600631433 := by
  unfold tailWord_7690632
  simp only [CollatzResearch.WordTrace]
  refine ⟨140250196537080597110593075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187000262049440796147457433 140250196537080597110593075)
  ·
    refine ⟨210375294805620895665889613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140250196537080597110593075 210375294805620895665889613)
    ·
      refine ⟨78890735552107835874708605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210375294805620895665889613 78890735552107835874708605)
      ·
        refine ⟨29584025832040438453015727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78890735552107835874708605 29584025832040438453015727)
        ·
          refine ⟨44376038748060657679523591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29584025832040438453015727 44376038748060657679523591)
          ·
            refine ⟨66564058122090986519285387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44376038748060657679523591 66564058122090986519285387)
            ·
              refine ⟨99846087183136479778928081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66564058122090986519285387 99846087183136479778928081)
              ·
                refine ⟨74884565387352359834196061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99846087183136479778928081 74884565387352359834196061)
                ·
                  refine ⟨28081712020257134937823523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74884565387352359834196061 28081712020257134937823523)
                  ·
                    refine ⟨42122568030385702406735285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28081712020257134937823523 42122568030385702406735285)
                    ·
                      refine ⟨3948990752848659600631433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42122568030385702406735285 3948990752848659600631433)
                      ·
                        rfl

theorem cell23_7690632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7690632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690632 prefixEnd_7690632 := by exact prefixLift 7690632
  have htrace : WordTrace (prefixWord ++ tailWord_7690632) baseStart_7690632 baseEnd_7690632 := by
    simpa [prefixWord, tailWord_7690632, baseEnd_7690632] using wordTrace_append hprefix tailTrace_7690632
  have hstable : (prefixWord ++ tailWord_7690632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690632).length < 2 ^ (prefixWord ++ tailWord_7690632).sum := by decide
  have hdescent : baseEnd_7690632 < baseStart_7690632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690649 : List Nat := [1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 3]
def baseStart_7690649 : Nat := 118140960795 + 7690649 * 2 ^ 59
def prefixEnd_7690649 : Nat := 4983230072969 + 3 ^ 40 * 7690649 * 2
def baseEnd_7690649 : Nat := 3948999482019786034118855

theorem tailTrace_7690649 : CollatzResearch.WordTrace tailWord_7690649 prefixEnd_7690649 3948999482019786034118855 := by
  unfold tailWord_7690649
  simp only [CollatzResearch.WordTrace]
  refine ⟨280501013115099606124555001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187000675410066404083036667 280501013115099606124555001)
  ·
    refine ⟨210375759836324704593416251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280501013115099606124555001 210375759836324704593416251)
    ·
      refine ⟨315563639754487056890124377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210375759836324704593416251 315563639754487056890124377)
      ·
        refine ⟨236672729815865292667593283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315563639754487056890124377 236672729815865292667593283)
        ·
          refine ⟨355009094723797939001389925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236672729815865292667593283 355009094723797939001389925)
          ·
            refine ⟨66564205260712113562760611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355009094723797939001389925 66564205260712113562760611)
            ·
              refine ⟨99846307891068170344140917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66564205260712113562760611 99846307891068170344140917)
              ·
                refine ⟨9360591364787640969763211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99846307891068170344140917 9360591364787640969763211)
                ·
                  refine ⟨14040887047181461454644817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9360591364787640969763211 14040887047181461454644817)
                  ·
                    refine ⟨10530665285386096090983613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14040887047181461454644817 10530665285386096090983613)
                    ·
                      refine ⟨3948999482019786034118855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10530665285386096090983613 3948999482019786034118855)
                      ·
                        rfl

theorem cell23_7690649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_7690649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690649 prefixEnd_7690649 := by exact prefixLift 7690649
  have htrace : WordTrace (prefixWord ++ tailWord_7690649) baseStart_7690649 baseEnd_7690649 := by
    simpa [prefixWord, tailWord_7690649, baseEnd_7690649] using wordTrace_append hprefix tailTrace_7690649
  have hstable : (prefixWord ++ tailWord_7690649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690649).length < 2 ^ (prefixWord ++ tailWord_7690649).sum := by decide
  have hdescent : baseEnd_7690649 < baseStart_7690649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690657 : List Nat := [1, 2, 3, 5, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7690657 : Nat := 118140960795 + 7690657 * 2 ^ 59
def prefixEnd_7690657 : Nat := 4983230072969 + 3 ^ 40 * 7690657 * 2
def baseEnd_7690657 : Nat := 3949003589865022002818819

theorem tailTrace_7690657 : CollatzResearch.WordTrace tailWord_7690657 prefixEnd_7690657 3949003589865022002818819 := by
  unfold tailWord_7690657
  simp only [CollatzResearch.WordTrace]
  refine ⟨280501304899070623490846225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187000869932713748993897483 280501304899070623490846225)
  ·
    refine ⟨210375978674302967618134669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280501304899070623490846225 210375978674302967618134669)
    ·
      refine ⟨78890992002863612856800501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210375978674302967618134669 78890992002863612856800501)
      ·
        refine ⟨7396030500268463705325047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78890992002863612856800501 7396030500268463705325047)
        ·
          refine ⟨11094045750402695557987571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396030500268463705325047 11094045750402695557987571)
          ·
            refine ⟨16641068625604043336981357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094045750402695557987571 16641068625604043336981357)
            ·
              refine ⟨6240400734601516251368009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16641068625604043336981357 6240400734601516251368009)
              ·
                refine ⟨4680300550951137188526007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6240400734601516251368009 4680300550951137188526007)
                ·
                  refine ⟨7020450826426705782789011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680300550951137188526007 7020450826426705782789011)
                  ·
                    refine ⟨10530676239640058674183517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7020450826426705782789011 10530676239640058674183517)
                    ·
                      refine ⟨3949003589865022002818819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10530676239640058674183517 3949003589865022002818819)
                      ·
                        rfl

theorem cell23_7690657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7690657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690657 prefixEnd_7690657 := by exact prefixLift 7690657
  have htrace : WordTrace (prefixWord ++ tailWord_7690657) baseStart_7690657 baseEnd_7690657 := by
    simpa [prefixWord, tailWord_7690657, baseEnd_7690657] using wordTrace_append hprefix tailTrace_7690657
  have hstable : (prefixWord ++ tailWord_7690657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690657).length < 2 ^ (prefixWord ++ tailWord_7690657).sum := by decide
  have hdescent : baseEnd_7690657 < baseStart_7690657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690663 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_7690663 : Nat := 118140960795 + 7690663 * 2 ^ 59
def prefixEnd_7690663 : Nat := 4983230072969 + 3 ^ 40 * 7690663 * 2
def baseEnd_7690663 : Nat := 3949006670748948979343791

theorem tailTrace_7690663 : CollatzResearch.WordTrace tailWord_7690663 prefixEnd_7690663 3949006670748948979343791 := by
  unfold tailWord_7690663
  simp only [CollatzResearch.WordTrace]
  refine ⟨280501523737048886515564643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187001015824699257677043095 280501523737048886515564643)
  ·
    refine ⟨420752285605573329773346965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280501523737048886515564643 420752285605573329773346965)
    ·
      refine ⟨19722763387761249833125639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 420752285605573329773346965 19722763387761249833125639)
      ·
        refine ⟨29584145081641874749688459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19722763387761249833125639 29584145081641874749688459)
        ·
          refine ⟨44376217622462812124532689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29584145081641874749688459 44376217622462812124532689)
          ·
            refine ⟨33282163216847109093399517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44376217622462812124532689 33282163216847109093399517)
            ·
              refine ⟨12480811206317665910024819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33282163216847109093399517 12480811206317665910024819)
              ·
                refine ⟨18721216809476498865037229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12480811206317665910024819 18721216809476498865037229)
                ·
                  refine ⟨7020456303553687074388961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18721216809476498865037229 7020456303553687074388961)
                  ·
                    refine ⟨5265342227665265305791721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7020456303553687074388961 5265342227665265305791721)
                    ·
                      refine ⟨3949006670748948979343791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265342227665265305791721 3949006670748948979343791)
                      ·
                        rfl

theorem cell23_7690663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_7690663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690663 prefixEnd_7690663 := by exact prefixLift 7690663
  have htrace : WordTrace (prefixWord ++ tailWord_7690663) baseStart_7690663 baseEnd_7690663 := by
    simpa [prefixWord, tailWord_7690663, baseEnd_7690663] using wordTrace_append hprefix tailTrace_7690663
  have hstable : (prefixWord ++ tailWord_7690663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690663).length < 2 ^ (prefixWord ++ tailWord_7690663).sum := by decide
  have hdescent : baseEnd_7690663 < baseStart_7690663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690673 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 2, 4]
def baseStart_7690673 : Nat := 118140960795 + 7690673 * 2 ^ 59
def prefixEnd_7690673 : Nat := 4983230072969 + 3 ^ 40 * 7690673 * 2
def baseEnd_7690673 : Nat := 1316337268518497980072915

theorem tailTrace_7690673 : CollatzResearch.WordTrace tailWord_7690673 prefixEnd_7690673 1316337268518497980072915 := by
  unfold tailWord_7690673
  simp only [CollatzResearch.WordTrace]
  refine ⟨280501888467012658223428673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187001258978008438815619115 280501888467012658223428673)
  ·
    refine ⟨210376416350259493667571505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280501888467012658223428673 210376416350259493667571505)
    ·
      refine ⟨157782312262694620250678629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210376416350259493667571505 157782312262694620250678629)
      ·
        refine ⟨29584183549255241297002243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157782312262694620250678629 29584183549255241297002243)
        ·
          refine ⟨44376275323882861945503365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29584183549255241297002243 44376275323882861945503365)
          ·
            refine ⟨8320551623228036614781881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44376275323882861945503365 8320551623228036614781881)
            ·
              refine ⟨6240413717421027461086411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8320551623228036614781881 6240413717421027461086411)
              ·
                refine ⟨9360620576131541191629617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240413717421027461086411 9360620576131541191629617)
                ·
                  refine ⟨7020465432098655893722213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9360620576131541191629617 7020465432098655893722213)
                  ·
                    refine ⟨1316337268518497980072915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020465432098655893722213 1316337268518497980072915)
                    ·
                      rfl

theorem cell23_7690673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_7690673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690673 prefixEnd_7690673 := by exact prefixLift 7690673
  have htrace : WordTrace (prefixWord ++ tailWord_7690673) baseStart_7690673 baseEnd_7690673 := by
    simpa [prefixWord, tailWord_7690673, baseEnd_7690673] using wordTrace_append hprefix tailTrace_7690673
  have hstable : (prefixWord ++ tailWord_7690673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690673).length < 2 ^ (prefixWord ++ tailWord_7690673).sum := by decide
  have hdescent : baseEnd_7690673 < baseStart_7690673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690712 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 2, 6]
def baseStart_7690712 : Nat := 118140960795 + 7690712 * 2 ^ 59
def prefixEnd_7690712 : Nat := 4983230072969 + 3 ^ 40 * 7690712 * 2
def baseEnd_7690712 : Nat := 1316343943767006429210355

theorem tailTrace_7690712 : CollatzResearch.WordTrace tailWord_7690712 prefixEnd_7690712 1316343943767006429210355 := by
  unfold tailWord_7690712
  simp only [CollatzResearch.WordTrace]
  refine ⟨140251655456935683942049195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187002207275914245256065593 140251655456935683942049195)
  ·
    refine ⟨210377483185403525913073793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140251655456935683942049195 210377483185403525913073793)
    ·
      refine ⟨157783112389052644434805345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210377483185403525913073793 157783112389052644434805345)
      ·
        refine ⟨118337334291789483326104009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157783112389052644434805345 118337334291789483326104009)
        ·
          refine ⟨88753000718842112494578007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118337334291789483326104009 88753000718842112494578007)
          ·
            refine ⟨133129501078263168741867011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88753000718842112494578007 133129501078263168741867011)
            ·
              refine ⟨199694251617394753112800517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133129501078263168741867011 199694251617394753112800517)
              ·
                refine ⟨37442672178261516208650097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199694251617394753112800517 37442672178261516208650097)
                ·
                  refine ⟨28082004133696137156487573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37442672178261516208650097 28082004133696137156487573)
                  ·
                    refine ⟨1316343943767006429210355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28082004133696137156487573 1316343943767006429210355)
                    ·
                      rfl

theorem cell23_7690712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_7690712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690712 prefixEnd_7690712 := by exact prefixLift 7690712
  have htrace : WordTrace (prefixWord ++ tailWord_7690712) baseStart_7690712 baseEnd_7690712 := by
    simpa [prefixWord, tailWord_7690712, baseEnd_7690712] using wordTrace_append hprefix tailTrace_7690712
  have hstable : (prefixWord ++ tailWord_7690712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690712).length < 2 ^ (prefixWord ++ tailWord_7690712).sum := by decide
  have hdescent : baseEnd_7690712 < baseStart_7690712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690736 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 1, 4, 2]
def baseStart_7690736 : Nat := 118140960795 + 7690736 * 2 ^ 59
def prefixEnd_7690736 : Nat := 4983230072969 + 3 ^ 40 * 7690736 * 2
def baseEnd_7690736 : Nat := 3949044154836727193730955

theorem tailTrace_7690736 : CollatzResearch.WordTrace tailWord_7690736 prefixEnd_7690736 3949044154836727193730955 := by
  unfold tailWord_7690736
  simp only [CollatzResearch.WordTrace]
  refine ⟨140252093132892209991486031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187002790843856279988648041 140252093132892209991486031)
  ·
    refine ⟨210378139699338314987229047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140252093132892209991486031 210378139699338314987229047)
    ·
      refine ⟨315567209549007472480843571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210378139699338314987229047 315567209549007472480843571)
      ·
        refine ⟨473350814323511208721265357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315567209549007472480843571 473350814323511208721265357)
        ·
          refine ⟨177506555371316703270474509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473350814323511208721265357 177506555371316703270474509)
          ·
            refine ⟨66564958264243763726427941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177506555371316703270474509 66564958264243763726427941)
            ·
              refine ⟨12480929674545705698705239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66564958264243763726427941 12480929674545705698705239)
              ·
                refine ⟨18721394511818558548057859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12480929674545705698705239 18721394511818558548057859)
                ·
                  refine ⟨28082091767727837822086789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18721394511818558548057859 28082091767727837822086789)
                  ·
                    refine ⟨5265392206448969591641273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28082091767727837822086789 5265392206448969591641273)
                    ·
                      refine ⟨3949044154836727193730955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265392206448969591641273 3949044154836727193730955)
                      ·
                        rfl

theorem cell23_7690736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 4, 2].length) (baseStart_7690736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690736 prefixEnd_7690736 := by exact prefixLift 7690736
  have htrace : WordTrace (prefixWord ++ tailWord_7690736) baseStart_7690736 baseEnd_7690736 := by
    simpa [prefixWord, tailWord_7690736, baseEnd_7690736] using wordTrace_append hprefix tailTrace_7690736
  have hstable : (prefixWord ++ tailWord_7690736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690736).length < 2 ^ (prefixWord ++ tailWord_7690736).sum := by decide
  have hdescent : baseEnd_7690736 < baseStart_7690736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690776 : List Nat := [2, 1, 2, 3, 3, 1, 2, 4, 5]
def baseStart_7690776 : Nat := 118140960795 + 7690776 * 2 ^ 59
def prefixEnd_7690776 : Nat := 4983230072969 + 3 ^ 40 * 7690776 * 2
def baseEnd_7690776 : Nat := 438784966006989670803419

theorem tailTrace_7690776 : CollatzResearch.WordTrace tailWord_7690776 prefixEnd_7690776 438784966006989670803419 := by
  unfold tailWord_7690776
  simp only [CollatzResearch.WordTrace]
  refine ⟨140252822592819753407214091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187003763457093004542952121 140252822592819753407214091)
  ·
    refine ⟨210379233889229630110821137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140252822592819753407214091 210379233889229630110821137)
    ·
      refine ⟨157784425416922222583115853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210379233889229630110821137 157784425416922222583115853)
      ·
        refine ⟨59169159531345833468668445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157784425416922222583115853 59169159531345833468668445)
        ·
          refine ⟨22188434824254687550750667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59169159531345833468668445 22188434824254687550750667)
          ·
            refine ⟨33282652236382031326126001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22188434824254687550750667 33282652236382031326126001)
            ·
              refine ⟨24961989177286523494594501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33282652236382031326126001 24961989177286523494594501)
              ·
                refine ⟨4680372970741223155236469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24961989177286523494594501 4680372970741223155236469)
                ·
                  refine ⟨438784966006989670803419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4680372970741223155236469 438784966006989670803419)
                  ·
                    rfl

theorem cell23_7690776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 5].length) (baseStart_7690776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690776 prefixEnd_7690776 := by exact prefixLift 7690776
  have htrace : WordTrace (prefixWord ++ tailWord_7690776) baseStart_7690776 baseEnd_7690776 := by
    simpa [prefixWord, tailWord_7690776, baseEnd_7690776] using wordTrace_append hprefix tailTrace_7690776
  have hstable : (prefixWord ++ tailWord_7690776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690776).length < 2 ^ (prefixWord ++ tailWord_7690776).sum := by decide
  have hdescent : baseEnd_7690776 < baseStart_7690776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690806 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_7690806 : Nat := 118140960795 + 7690806 * 2 ^ 59
def prefixEnd_7690806 : Nat := 4983230072969 + 3 ^ 40 * 7690806 * 2
def baseEnd_7690806 : Nat := 1316360032827513973285211

theorem tailTrace_7690806 : CollatzResearch.WordTrace tailWord_7690806 prefixEnd_7690806 1316360032827513973285211 := by
  unfold tailWord_7690806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17531671210970676371126267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187004492917020547958680181 17531671210970676371126267)
  ·
    refine ⟨26297506816456014556689401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17531671210970676371126267 26297506816456014556689401)
    ·
      refine ⟨19723130112342010917517051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26297506816456014556689401 19723130112342010917517051)
      ·
        refine ⟨29584695168513016376275577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19723130112342010917517051 29584695168513016376275577)
        ·
          refine ⟨22188521376384762282206683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29584695168513016376275577 22188521376384762282206683)
          ·
            refine ⟨33282782064577143423310025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22188521376384762282206683 33282782064577143423310025)
            ·
              refine ⟨24962086548432857567482519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33282782064577143423310025 24962086548432857567482519)
              ·
                refine ⟨37443129822649286351223779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24962086548432857567482519 37443129822649286351223779)
                ·
                  refine ⟨56164694733973929526835669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37443129822649286351223779 56164694733973929526835669)
                  ·
                    refine ⟨1316360032827513973285211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56164694733973929526835669 1316360032827513973285211)
                    ·
                      rfl

theorem cell23_7690806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_7690806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690806 prefixEnd_7690806 := by exact prefixLift 7690806
  have htrace : WordTrace (prefixWord ++ tailWord_7690806) baseStart_7690806 baseEnd_7690806 := by
    simpa [prefixWord, tailWord_7690806, baseEnd_7690806] using wordTrace_append hprefix tailTrace_7690806
  have hstable : (prefixWord ++ tailWord_7690806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690806).length < 2 ^ (prefixWord ++ tailWord_7690806).sum := by decide
  have hdescent : baseEnd_7690806 < baseStart_7690806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690809 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7690809 : Nat := 118140960795 + 7690809 * 2 ^ 59
def prefixEnd_7690809 : Nat := 4983230072969 + 3 ^ 40 * 7690809 * 2
def baseEnd_7690809 : Nat := 3949081638924505408118119

theorem tailTrace_7690809 : CollatzResearch.WordTrace tailWord_7690809 prefixEnd_7690809 3949081638924505408118119 := by
  unfold tailWord_7690809
  simp only [CollatzResearch.WordTrace]
  refine ⟨280506848794519953450379481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187004565863013302300252987 280506848794519953450379481)
  ·
    refine ⟨210380136595889965087784611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280506848794519953450379481 210380136595889965087784611)
    ·
      refine ⟨315570204893834947631676917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210380136595889965087784611 315570204893834947631676917)
      ·
        refine ⟨29584706708797026340469711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315570204893834947631676917 29584706708797026340469711)
        ·
          refine ⟨44377060063195539510704567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29584706708797026340469711 44377060063195539510704567)
          ·
            refine ⟨66565590094793309266056851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44377060063195539510704567 66565590094793309266056851)
            ·
              refine ⟨99848385142189963899085277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66565590094793309266056851 99848385142189963899085277)
              ·
                refine ⟨37443144428321236462156979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99848385142189963899085277 37443144428321236462156979)
                ·
                  refine ⟨56164716642481854693235469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37443144428321236462156979 56164716642481854693235469)
                  ·
                    refine ⟨21061768740930695509963301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56164716642481854693235469 21061768740930695509963301)
                    ·
                      refine ⟨3949081638924505408118119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21061768740930695509963301 3949081638924505408118119)
                      ·
                        rfl

theorem cell23_7690809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7690809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690809 prefixEnd_7690809 := by exact prefixLift 7690809
  have htrace : WordTrace (prefixWord ++ tailWord_7690809) baseStart_7690809 baseEnd_7690809 := by
    simpa [prefixWord, tailWord_7690809, baseEnd_7690809] using wordTrace_append hprefix tailTrace_7690809
  have hstable : (prefixWord ++ tailWord_7690809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690809).length < 2 ^ (prefixWord ++ tailWord_7690809).sum := by decide
  have hdescent : baseEnd_7690809 < baseStart_7690809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690819 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 5, 4]
def baseStart_7690819 : Nat := 118140960795 + 7690819 * 2 ^ 59
def prefixEnd_7690819 : Nat := 4983230072969 + 3 ^ 40 * 7690819 * 2
def baseEnd_7690819 : Nat := 1316362257910350122997691

theorem tailTrace_7690819 : CollatzResearch.WordTrace tailWord_7690819 prefixEnd_7690819 1316362257910350122997691 := by
  unfold tailWord_7690819
  simp only [CollatzResearch.WordTrace]
  refine ⟨280507213524483725158243511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187004809016322483438829007 280507213524483725158243511)
  ·
    refine ⟨420760820286725587737365267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280507213524483725158243511 420760820286725587737365267)
    ·
      refine ⟨631141230430088381606047901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420760820286725587737365267 631141230430088381606047901)
      ·
        refine ⟨236677961411283143102267963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631141230430088381606047901 236677961411283143102267963)
        ·
          refine ⟨355016942116924714653401945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236677961411283143102267963 355016942116924714653401945)
          ·
            refine ⟨266262706587693535990051459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355016942116924714653401945 266262706587693535990051459)
            ·
              refine ⟨399394059881540303985077189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266262706587693535990051459 399394059881540303985077189)
              ·
                refine ⟨74886386227788806997201973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399394059881540303985077189 74886386227788806997201973)
                ·
                  refine ⟨7020598708855200655987685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74886386227788806997201973 7020598708855200655987685)
                  ·
                    refine ⟨1316362257910350122997691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020598708855200655987685 1316362257910350122997691)
                    ·
                      rfl

theorem cell23_7690819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 4].length) (baseStart_7690819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690819 prefixEnd_7690819 := by exact prefixLift 7690819
  have htrace : WordTrace (prefixWord ++ tailWord_7690819) baseStart_7690819 baseEnd_7690819 := by
    simpa [prefixWord, tailWord_7690819, baseEnd_7690819] using wordTrace_append hprefix tailTrace_7690819
  have hstable : (prefixWord ++ tailWord_7690819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690819).length < 2 ^ (prefixWord ++ tailWord_7690819).sum := by decide
  have hdescent : baseEnd_7690819 < baseStart_7690819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690826 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_7690826 : Nat := 118140960795 + 7690826 * 2 ^ 59
def prefixEnd_7690826 : Nat := 4983230072969 + 3 ^ 40 * 7690826 * 2
def baseEnd_7690826 : Nat := 3949090368095631841605541

theorem tailTrace_7690826 : CollatzResearch.WordTrace tailWord_7690826 prefixEnd_7690826 3949090368095631841605541 := by
  unfold tailWord_7690826
  simp only [CollatzResearch.WordTrace]
  refine ⟨70126867208864591338437083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187004979223638910235832221 70126867208864591338437083)
  ·
    refine ⟨105190300813296887007655625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70126867208864591338437083 105190300813296887007655625)
    ·
      refine ⟨78892725609972665255741719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105190300813296887007655625 78892725609972665255741719)
      ·
        refine ⟨118339088414958997883612579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78892725609972665255741719 118339088414958997883612579)
        ·
          refine ⟨177508632622438496825418869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118339088414958997883612579 177508632622438496825418869)
          ·
            refine ⟨16641434308353609077383019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177508632622438496825418869 16641434308353609077383019)
            ·
              refine ⟨24962151462530413616074529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16641434308353609077383019 24962151462530413616074529)
              ·
                refine ⟨18721613596897810212055897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24962151462530413616074529 18721613596897810212055897)
                ·
                  refine ⟨14041210197673357659041923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18721613596897810212055897 14041210197673357659041923)
                  ·
                    refine ⟨21061815296510036488562885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14041210197673357659041923 21061815296510036488562885)
                    ·
                      refine ⟨3949090368095631841605541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21061815296510036488562885 3949090368095631841605541)
                      ·
                        rfl

theorem cell23_7690826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_7690826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690826 prefixEnd_7690826 := by exact prefixLift 7690826
  have htrace : WordTrace (prefixWord ++ tailWord_7690826) baseStart_7690826 baseEnd_7690826 := by
    simpa [prefixWord, tailWord_7690826, baseEnd_7690826] using wordTrace_append hprefix tailTrace_7690826
  have hstable : (prefixWord ++ tailWord_7690826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690826).length < 2 ^ (prefixWord ++ tailWord_7690826).sum := by decide
  have hdescent : baseEnd_7690826 < baseStart_7690826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690910 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_7690910 : Nat := 118140960795 + 7690910 * 2 ^ 59
def prefixEnd_7690910 : Nat := 4983230072969 + 3 ^ 40 * 7690910 * 2
def baseEnd_7690910 : Nat := 3949133500470609512955155

theorem tailTrace_7690910 : CollatzResearch.WordTrace tailWord_7690910 prefixEnd_7690910 3949133500470609512955155 := by
  unfold tailWord_7690910
  simp only [CollatzResearch.WordTrace]
  refine ⟨35063816570894255962475773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187007021711436031799870789 35063816570894255962475773)
  ·
    refine ⟨13148931214085345985928415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35063816570894255962475773 13148931214085345985928415)
    ·
      refine ⟨19723396821128018978892623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13148931214085345985928415 19723396821128018978892623)
      ·
        refine ⟨29585095231692028468338935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19723396821128018978892623 29585095231692028468338935)
        ·
          refine ⟨44377642847538042702508403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29585095231692028468338935 44377642847538042702508403)
          ·
            refine ⟨66566464271307064053762605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44377642847538042702508403 66566464271307064053762605)
            ·
              refine ⟨24962424101740149020160977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66566464271307064053762605 24962424101740149020160977)
              ·
                refine ⟨18721818076305111765120733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24962424101740149020160977 18721818076305111765120733)
                ·
                  refine ⟨7020681778614416911920275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18721818076305111765120733 7020681778614416911920275)
                  ·
                    refine ⟨10531022667921625367880413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7020681778614416911920275 10531022667921625367880413)
                    ·
                      refine ⟨3949133500470609512955155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10531022667921625367880413 3949133500470609512955155)
                      ·
                        rfl

theorem cell23_7690910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_7690910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690910 prefixEnd_7690910 := by exact prefixLift 7690910
  have htrace : WordTrace (prefixWord ++ tailWord_7690910) baseStart_7690910 baseEnd_7690910 := by
    simpa [prefixWord, tailWord_7690910, baseEnd_7690910] using wordTrace_append hprefix tailTrace_7690910
  have hstable : (prefixWord ++ tailWord_7690910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690910).length < 2 ^ (prefixWord ++ tailWord_7690910).sum := by decide
  have hdescent : baseEnd_7690910 < baseStart_7690910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690916 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_7690916 : Nat := 118140960795 + 7690916 * 2 ^ 59
def prefixEnd_7690916 : Nat := 4983230072969 + 3 ^ 40 * 7690916 * 2
def baseEnd_7690916 : Nat := 3949136581354536489480127

theorem tailTrace_7690916 : CollatzResearch.WordTrace tailWord_7690916 prefixEnd_7690916 3949136581354536489480127 := by
  unfold tailWord_7690916
  simp only [CollatzResearch.WordTrace]
  refine ⟨140255375702566155362262301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187007167603421540483016401 140255375702566155362262301)
  ·
    refine ⟨52595765888462308260848363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140255375702566155362262301 52595765888462308260848363)
    ·
      refine ⟨78893648832693462391272545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52595765888462308260848363 78893648832693462391272545)
      ·
        refine ⟨59170236624520096793454409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78893648832693462391272545 59170236624520096793454409)
        ·
          refine ⟨44377677468390072595090807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59170236624520096793454409 44377677468390072595090807)
          ·
            refine ⟨66566516202585108892636211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44377677468390072595090807 66566516202585108892636211)
            ·
              refine ⟨99849774303877663338954317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66566516202585108892636211 99849774303877663338954317)
              ·
                refine ⟨37443665363954123752107869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99849774303877663338954317 37443665363954123752107869)
                ·
                  refine ⟨14041374511482796407040451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37443665363954123752107869 14041374511482796407040451)
                  ·
                    refine ⟨21062061767224194610560677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14041374511482796407040451 21062061767224194610560677)
                    ·
                      refine ⟨3949136581354536489480127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21062061767224194610560677 3949136581354536489480127)
                      ·
                        rfl

theorem cell23_7690916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_7690916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690916 prefixEnd_7690916 := by exact prefixLift 7690916
  have htrace : WordTrace (prefixWord ++ tailWord_7690916) baseStart_7690916 baseEnd_7690916 := by
    simpa [prefixWord, tailWord_7690916, baseEnd_7690916] using wordTrace_append hprefix tailTrace_7690916
  have hstable : (prefixWord ++ tailWord_7690916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690916).length < 2 ^ (prefixWord ++ tailWord_7690916).sum := by decide
  have hdescent : baseEnd_7690916 < baseStart_7690916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7690943 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 2, 4]
def baseStart_7690943 : Nat := 118140960795 + 7690943 * 2 ^ 59
def prefixEnd_7690943 : Nat := 4983230072969 + 3 ^ 40 * 7690943 * 2
def baseEnd_7690943 : Nat := 1316383481777402627947501

theorem tailTrace_7690943 : CollatzResearch.WordTrace tailWord_7690943 prefixEnd_7690943 1316383481777402627947501 := by
  unfold tailWord_7690943
  simp only [CollatzResearch.WordTrace]
  refine ⟨280511736176034494335757483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187007824117356329557171655 280511736176034494335757483)
  ·
    refine ⟨420767604264051741503636225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280511736176034494335757483 420767604264051741503636225)
    ·
      refine ⟨315575703198038806127727169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420767604264051741503636225 315575703198038806127727169)
      ·
        refine ⟨236681777398529104595795377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315575703198038806127727169 236681777398529104595795377)
        ·
          refine ⟨177511333048896828446846533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236681777398529104595795377 177511333048896828446846533)
          ·
            refine ⟨33283374946668155333783725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177511333048896828446846533 33283374946668155333783725)
            ·
              refine ⟨12481265605000558250168897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33283374946668155333783725 12481265605000558250168897)
              ·
                refine ⟨9360949203750418687626673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12481265605000558250168897 9360949203750418687626673)
                ·
                  refine ⟨7020711902812814015720005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9360949203750418687626673 7020711902812814015720005)
                  ·
                    refine ⟨1316383481777402627947501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020711902812814015720005 1316383481777402627947501)
                    ·
                      rfl

theorem cell23_7690943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 4].length) (baseStart_7690943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7690943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7690943 prefixEnd_7690943 := by exact prefixLift 7690943
  have htrace : WordTrace (prefixWord ++ tailWord_7690943) baseStart_7690943 baseEnd_7690943 := by
    simpa [prefixWord, tailWord_7690943, baseEnd_7690943] using wordTrace_append hprefix tailTrace_7690943
  have hstable : (prefixWord ++ tailWord_7690943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7690943).length < 2 ^ (prefixWord ++ tailWord_7690943).sum := by decide
  have hdescent : baseEnd_7690943 < baseStart_7690943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7690943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691023 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 1, 4, 2]
def baseStart_7691023 : Nat := 118140960795 + 7691023 * 2 ^ 59
def prefixEnd_7691023 : Nat := 4983230072969 + 3 ^ 40 * 7691023 * 2
def baseEnd_7691023 : Nat := 3949191523784567570842135

theorem tailTrace_7691023 : CollatzResearch.WordTrace tailWord_7691023 prefixEnd_7691023 3949191523784567570842135 := by
  unfold tailWord_7691023
  simp only [CollatzResearch.WordTrace]
  refine ⟨280514654015744667998669723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187009769343829778665779815 280514654015744667998669723)
  ·
    refine ⟨420771981023617001998004585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280514654015744667998669723 420771981023617001998004585)
    ·
      refine ⟨315578985767712751498503439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420771981023617001998004585 315578985767712751498503439)
      ·
        refine ⟨473368478651569127247755159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315578985767712751498503439 473368478651569127247755159)
        ·
          refine ⟨710052717977353690871632739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473368478651569127247755159 710052717977353690871632739)
          ·
            refine ⟨1065079076966030536307449109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710052717977353690871632739 1065079076966030536307449109)
            ·
              refine ⟨49925581732782681389411677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1065079076966030536307449109 49925581732782681389411677)
              ·
                refine ⟨18722093149793505521029379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49925581732782681389411677 18722093149793505521029379)
                ·
                  refine ⟨28083139724690258281544069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18722093149793505521029379 28083139724690258281544069)
                  ·
                    refine ⟨5265588698379423427789513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28083139724690258281544069 5265588698379423427789513)
                    ·
                      refine ⟨3949191523784567570842135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265588698379423427789513 3949191523784567570842135)
                      ·
                        rfl

theorem cell23_7691023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 4, 2].length) (baseStart_7691023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691023 prefixEnd_7691023 := by exact prefixLift 7691023
  have htrace : WordTrace (prefixWord ++ tailWord_7691023) baseStart_7691023 baseEnd_7691023 := by
    simpa [prefixWord, tailWord_7691023, baseEnd_7691023] using wordTrace_append hprefix tailTrace_7691023
  have hstable : (prefixWord ++ tailWord_7691023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691023).length < 2 ^ (prefixWord ++ tailWord_7691023).sum := by decide
  have hdescent : baseEnd_7691023 < baseStart_7691023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691040 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 1, 4, 2]
def baseStart_7691040 : Nat := 118140960795 + 7691040 * 2 ^ 59
def prefixEnd_7691040 : Nat := 4983230072969 + 3 ^ 40 * 7691040 * 2
def baseEnd_7691040 : Nat := 3949200252955694004329557

theorem tailTrace_7691040 : CollatzResearch.WordTrace tailWord_7691040 prefixEnd_7691040 3949200252955694004329557 := by
  unfold tailWord_7691040
  simp only [CollatzResearch.WordTrace]
  refine ⟨140257637028341539951019287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187010182704455386601359049 140257637028341539951019287)
  ·
    refine ⟨210386455542512309926528931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140257637028341539951019287 210386455542512309926528931)
    ·
      refine ⟨315579683313768464889793397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210386455542512309926528931 315579683313768464889793397)
      ·
        refine ⟨29585595310665793583418131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315579683313768464889793397 29585595310665793583418131)
        ·
          refine ⟨44378392965998690375127197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29585595310665793583418131 44378392965998690375127197)
          ·
            refine ⟨16641897362249508890672699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44378392965998690375127197 16641897362249508890672699)
            ·
              refine ⟨24962846043374263336009049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16641897362249508890672699 24962846043374263336009049)
              ·
                refine ⟨18722134532530697502006787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24962846043374263336009049 18722134532530697502006787)
                ·
                  refine ⟨28083201798796046253010181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18722134532530697502006787 28083201798796046253010181)
                  ·
                    refine ⟨5265600337274258672439409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28083201798796046253010181 5265600337274258672439409)
                    ·
                      refine ⟨3949200252955694004329557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265600337274258672439409 3949200252955694004329557)
                      ·
                        rfl

theorem cell23_7691040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_7691040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691040 prefixEnd_7691040 := by exact prefixLift 7691040
  have htrace : WordTrace (prefixWord ++ tailWord_7691040) baseStart_7691040 baseEnd_7691040 := by
    simpa [prefixWord, tailWord_7691040, baseEnd_7691040] using wordTrace_append hprefix tailTrace_7691040
  have hstable : (prefixWord ++ tailWord_7691040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691040).length < 2 ^ (prefixWord ++ tailWord_7691040).sum := by decide
  have hdescent : baseEnd_7691040 < baseStart_7691040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691044 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_7691044 : Nat := 118140960795 + 7691044 * 2 ^ 59
def prefixEnd_7691044 : Nat := 4983230072969 + 3 ^ 40 * 7691044 * 2
def baseEnd_7691044 : Nat := 3949202306878311988679539

theorem tailTrace_7691044 : CollatzResearch.WordTrace tailWord_7691044 prefixEnd_7691044 3949202306878311988679539 := by
  unfold tailWord_7691044
  simp only [CollatzResearch.WordTrace]
  refine ⟨140257709974334294292592093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187010279965779059056789457 140257709974334294292592093)
  ·
    refine ⟨52596641240375360359722035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140257709974334294292592093 52596641240375360359722035)
    ·
      refine ⟨78894961860563040539583053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52596641240375360359722035 78894961860563040539583053)
      ·
        refine ⟨29585610697711140202343645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78894961860563040539583053 29585610697711140202343645)
        ·
          refine ⟨11094604011641677575878867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29585610697711140202343645 11094604011641677575878867)
          ·
            refine ⟨16641906017462516363818301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094604011641677575878867 16641906017462516363818301)
            ·
              refine ⟨6240714756548443636431863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16641906017462516363818301 6240714756548443636431863)
              ·
                refine ⟨9361072134822665454647795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240714756548443636431863 9361072134822665454647795)
                ·
                  refine ⟨14041608202233998181971693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9361072134822665454647795 14041608202233998181971693)
                  ·
                    refine ⟨5265603075837749318239385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14041608202233998181971693 5265603075837749318239385)
                    ·
                      refine ⟨3949202306878311988679539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265603075837749318239385 3949202306878311988679539)
                      ·
                        rfl

theorem cell23_7691044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_7691044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691044 prefixEnd_7691044 := by exact prefixLift 7691044
  have htrace : WordTrace (prefixWord ++ tailWord_7691044) baseStart_7691044 baseEnd_7691044 := by
    simpa [prefixWord, tailWord_7691044, baseEnd_7691044] using wordTrace_append hprefix tailTrace_7691044
  have hstable : (prefixWord ++ tailWord_7691044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691044).length < 2 ^ (prefixWord ++ tailWord_7691044).sum := by decide
  have hdescent : baseEnd_7691044 < baseStart_7691044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691056 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 3]
def baseStart_7691056 : Nat := 118140960795 + 7691056 * 2 ^ 59
def prefixEnd_7691056 : Nat := 4983230072969 + 3 ^ 40 * 7691056 * 2
def baseEnd_7691056 : Nat := 3949208468646165941729483

theorem tailTrace_7691056 : CollatzResearch.WordTrace tailWord_7691056 prefixEnd_7691056 3949208468646165941729483 := by
  unfold tailWord_7691056
  simp only [CollatzResearch.WordTrace]
  refine ⟨140257928812312557317310511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187010571749750076423080681 140257928812312557317310511)
  ·
    refine ⟨210386893218468835975965767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140257928812312557317310511 210386893218468835975965767)
    ·
      refine ⟨315580339827703253963948651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210386893218468835975965767 315580339827703253963948651)
      ·
        refine ⟨473370509741554880945922977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315580339827703253963948651 473370509741554880945922977)
        ·
          refine ⟨355027882306166160709442233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473370509741554880945922977 355027882306166160709442233)
          ·
            refine ⟨266270911729624620532081675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355027882306166160709442233 266270911729624620532081675)
            ·
              refine ⟨399406367594436930798122513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266270911729624620532081675 399406367594436930798122513)
              ·
                refine ⟨299554775695827698098591885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399406367594436930798122513 299554775695827698098591885)
                ·
                  refine ⟨112333040885935386786971957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299554775695827698098591885 112333040885935386786971957)
                  ·
                    refine ⟨10531222583056442511278621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112333040885935386786971957 10531222583056442511278621)
                    ·
                      refine ⟨3949208468646165941729483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10531222583056442511278621 3949208468646165941729483)
                      ·
                        rfl

theorem cell23_7691056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_7691056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691056 prefixEnd_7691056 := by exact prefixLift 7691056
  have htrace : WordTrace (prefixWord ++ tailWord_7691056) baseStart_7691056 baseEnd_7691056 := by
    simpa [prefixWord, tailWord_7691056, baseEnd_7691056] using wordTrace_append hprefix tailTrace_7691056
  have hstable : (prefixWord ++ tailWord_7691056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691056).length < 2 ^ (prefixWord ++ tailWord_7691056).sum := by decide
  have hdescent : baseEnd_7691056 < baseStart_7691056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691057 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 2, 2, 2]
def baseStart_7691057 : Nat := 118140960795 + 7691057 * 2 ^ 59
def prefixEnd_7691057 : Nat := 4983230072969 + 3 ^ 40 * 7691057 * 2
def baseEnd_7691057 : Nat := 3949208982126820437816979

theorem tailTrace_7691057 : CollatzResearch.WordTrace tailWord_7691057 prefixEnd_7691057 3949208982126820437816979 := by
  unfold tailWord_7691057
  simp only [CollatzResearch.WordTrace]
  refine ⟨280515894097621491805407425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187010596065080994536938283 280515894097621491805407425)
  ·
    refine ⟨210386920573216118854055569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280515894097621491805407425 210386920573216118854055569)
    ·
      refine ⟨157790190429912089140541677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210386920573216118854055569 157790190429912089140541677)
      ·
        refine ⟨59171321411217033427703129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157790190429912089140541677 59171321411217033427703129)
        ·
          refine ⟨44378491058412775070777347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59171321411217033427703129 44378491058412775070777347)
          ·
            refine ⟨66567736587619162606166021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44378491058412775070777347 66567736587619162606166021)
            ·
              refine ⟨12481450610178592988656129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66567736587619162606166021 12481450610178592988656129)
              ·
                refine ⟨9361087957633944741492097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12481450610178592988656129 9361087957633944741492097)
                ·
                  refine ⟨7020815968225458556119073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9361087957633944741492097 7020815968225458556119073)
                  ·
                    refine ⟨5265611976169093917089305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7020815968225458556119073 5265611976169093917089305)
                    ·
                      refine ⟨3949208982126820437816979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265611976169093917089305 3949208982126820437816979)
                      ·
                        rfl

theorem cell23_7691057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_7691057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691057 prefixEnd_7691057 := by exact prefixLift 7691057
  have htrace : WordTrace (prefixWord ++ tailWord_7691057) baseStart_7691057 baseEnd_7691057 := by
    simpa [prefixWord, tailWord_7691057, baseEnd_7691057] using wordTrace_append hprefix tailTrace_7691057
  have hstable : (prefixWord ++ tailWord_7691057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691057).length < 2 ^ (prefixWord ++ tailWord_7691057).sum := by decide
  have hdescent : baseEnd_7691057 < baseStart_7691057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691063 : List Nat := [1, 1, 3, 1, 2, 1, 5, 4, 5]
def baseStart_7691063 : Nat := 118140960795 + 7691063 * 2 ^ 59
def prefixEnd_7691063 : Nat := 4983230072969 + 3 ^ 40 * 7691063 * 2
def baseEnd_7691063 : Nat := 438801340334527490482439

theorem tailTrace_7691063 : CollatzResearch.WordTrace tailWord_7691063 prefixEnd_7691063 438801340334527490482439 := by
  unfold tailWord_7691063
  simp only [CollatzResearch.WordTrace]
  refine ⟨280516112935599754830125843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187010741957066503220083895 280516112935599754830125843)
  ·
    refine ⟨420774169403399632245188765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280516112935599754830125843 420774169403399632245188765)
    ·
      refine ⟨157790313526274862091945787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420774169403399632245188765 157790313526274862091945787)
      ·
        refine ⟨236685470289412293137918681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157790313526274862091945787 236685470289412293137918681)
        ·
          refine ⟨177514102717059219853439011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236685470289412293137918681 177514102717059219853439011)
          ·
            refine ⟨266271154075588829780158517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177514102717059219853439011 266271154075588829780158517)
            ·
              refine ⟨24962920694586452791889861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266271154075588829780158517 24962920694586452791889861)
              ·
                refine ⟨4680547630234959898479349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24962920694586452791889861 4680547630234959898479349)
                ·
                  refine ⟨438801340334527490482439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4680547630234959898479349 438801340334527490482439)
                  ·
                    rfl

theorem cell23_7691063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 5].length) (baseStart_7691063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691063 prefixEnd_7691063 := by exact prefixLift 7691063
  have htrace : WordTrace (prefixWord ++ tailWord_7691063) baseStart_7691063 baseEnd_7691063 := by
    simpa [prefixWord, tailWord_7691063, baseEnd_7691063] using wordTrace_append hprefix tailTrace_7691063
  have hstable : (prefixWord ++ tailWord_7691063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691063).length < 2 ^ (prefixWord ++ tailWord_7691063).sum := by decide
  have hdescent : baseEnd_7691063 < baseStart_7691063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691070 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_7691070 : Nat := 118140960795 + 7691070 * 2 ^ 59
def prefixEnd_7691070 : Nat := 4983230072969 + 3 ^ 40 * 7691070 * 2
def baseEnd_7691070 : Nat := 3949215657375328886954419

theorem tailTrace_7691070 : CollatzResearch.WordTrace tailWord_7691070 prefixEnd_7691070 3949215657375328886954419 := by
  unfold tailWord_7691070
  simp only [CollatzResearch.WordTrace]
  refine ⟨35064546030821799378203833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187010912164382930017087109 35064546030821799378203833)
  ·
    refine ⟨26298409523116349533652875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35064546030821799378203833 26298409523116349533652875)
    ·
      refine ⟨39447614284674524300479313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26298409523116349533652875 39447614284674524300479313)
      ·
        refine ⟨29585710713505893225359485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39447614284674524300479313 29585710713505893225359485)
        ·
          refine ⟨11094641517564709959509807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29585710713505893225359485 11094641517564709959509807)
          ·
            refine ⟨16641962276347064939264711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11094641517564709959509807 16641962276347064939264711)
            ·
              refine ⟨24962943414520597408897067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16641962276347064939264711 24962943414520597408897067)
              ·
                refine ⟨37444415121780896113345601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24962943414520597408897067 37444415121780896113345601)
                ·
                  refine ⟨28083311341335672085009201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37444415121780896113345601 28083311341335672085009201)
                  ·
                    refine ⟨21062483506001754063756901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28083311341335672085009201 21062483506001754063756901)
                    ·
                      refine ⟨3949215657375328886954419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21062483506001754063756901 3949215657375328886954419)
                      ·
                        rfl

theorem cell23_7691070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_7691070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691070 prefixEnd_7691070 := by exact prefixLift 7691070
  have htrace : WordTrace (prefixWord ++ tailWord_7691070) baseStart_7691070 baseEnd_7691070 := by
    simpa [prefixWord, tailWord_7691070, baseEnd_7691070] using wordTrace_append hprefix tailTrace_7691070
  have hstable : (prefixWord ++ tailWord_7691070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691070).length < 2 ^ (prefixWord ++ tailWord_7691070).sum := by decide
  have hdescent : baseEnd_7691070 < baseStart_7691070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691086 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_7691086 : Nat := 118140960795 + 7691086 * 2 ^ 59
def prefixEnd_7691086 : Nat := 4983230072969 + 3 ^ 40 * 7691086 * 2
def baseEnd_7691086 : Nat := 3949223873065800824354345

theorem tailTrace_7691086 : CollatzResearch.WordTrace tailWord_7691086 prefixEnd_7691086 3949223873065800824354345 := by
  unfold tailWord_7691086
  simp only [CollatzResearch.WordTrace]
  refine ⟨35064618976814553719776639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187011301209677619838808741 35064618976814553719776639)
  ·
    refine ⟨52596928465221830579664959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35064618976814553719776639 52596928465221830579664959)
    ·
      refine ⟨78895392697832745869497439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52596928465221830579664959 78895392697832745869497439)
      ·
        refine ⟨118343089046749118804246159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78895392697832745869497439 118343089046749118804246159)
        ·
          refine ⟨177514633570123678206369239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118343089046749118804246159 177514633570123678206369239)
          ·
            refine ⟨266271950355185517309553859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177514633570123678206369239 266271950355185517309553859)
            ·
              refine ⟨399407925532778275964330789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266271950355185517309553859 399407925532778275964330789)
              ·
                refine ⟨74888986037395926743312023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399407925532778275964330789 74888986037395926743312023)
                ·
                  refine ⟨112333479056093890114968035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74888986037395926743312023 112333479056093890114968035)
                  ·
                    refine ⟨168500218584140835172452053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112333479056093890114968035 168500218584140835172452053)
                    ·
                      refine ⟨3949223873065800824354345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168500218584140835172452053 3949223873065800824354345)
                      ·
                        rfl

theorem cell23_7691086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_7691086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691086 prefixEnd_7691086 := by exact prefixLift 7691086
  have htrace : WordTrace (prefixWord ++ tailWord_7691086) baseStart_7691086 baseEnd_7691086 := by
    simpa [prefixWord, tailWord_7691086, baseEnd_7691086] using wordTrace_append hprefix tailTrace_7691086
  have hstable : (prefixWord ++ tailWord_7691086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691086).length < 2 ^ (prefixWord ++ tailWord_7691086).sum := by decide
  have hdescent : baseEnd_7691086 < baseStart_7691086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691123 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 3, 4]
def baseStart_7691123 : Nat := 118140960795 + 7691123 * 2 ^ 59
def prefixEnd_7691123 : Nat := 4983230072969 + 3 ^ 40 * 7691123 * 2
def baseEnd_7691123 : Nat := 1316414290616672393197225

theorem tailTrace_7691123 : CollatzResearch.WordTrace tailWord_7691123 prefixEnd_7691123 1316414290616672393197225 := by
  unfold tailWord_7691123
  simp only [CollatzResearch.WordTrace]
  refine ⟨280518301315382385077310023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187012200876921590051540015 280518301315382385077310023)
  ·
    refine ⟨420777451973073577615965035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280518301315382385077310023 420777451973073577615965035)
    ·
      refine ⟨631166177959610366423947553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420777451973073577615965035 631166177959610366423947553)
      ·
        refine ⟨473374633469707774817960665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631166177959610366423947553 473374633469707774817960665)
        ·
          refine ⟨355030975102280831113470499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473374633469707774817960665 355030975102280831113470499)
          ·
            refine ⟨532546462653421246670205749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355030975102280831113470499 532546462653421246670205749)
            ·
              refine ⟨49926230873758241875331789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 532546462653421246670205749 49926230873758241875331789)
              ·
                refine ⟨18722336577659340703249421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49926230873758241875331789 18722336577659340703249421)
                ·
                  refine ⟨7020876216622252763718533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18722336577659340703249421 7020876216622252763718533)
                  ·
                    refine ⟨1316414290616672393197225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020876216622252763718533 1316414290616672393197225)
                    ·
                      rfl

theorem cell23_7691123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 4].length) (baseStart_7691123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691123 prefixEnd_7691123 := by exact prefixLift 7691123
  have htrace : WordTrace (prefixWord ++ tailWord_7691123) baseStart_7691123 baseEnd_7691123 := by
    simpa [prefixWord, tailWord_7691123, baseEnd_7691123] using wordTrace_append hprefix tailTrace_7691123
  have hstable : (prefixWord ++ tailWord_7691123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691123).length < 2 ^ (prefixWord ++ tailWord_7691123).sum := by decide
  have hdescent : baseEnd_7691123 < baseStart_7691123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691133 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_7691133 : Nat := 118140960795 + 7691133 * 2 ^ 59
def prefixEnd_7691133 : Nat := 4983230072969 + 3 ^ 40 * 7691133 * 2
def baseEnd_7691133 : Nat := 3949248006656562140466629

theorem tailTrace_7691133 : CollatzResearch.WordTrace tailWord_7691133 prefixEnd_7691133 3949248006656562140466629 := by
  unfold tailWord_7691133
  simp only [CollatzResearch.WordTrace]
  refine ⟨280518666045346156785174053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187012444030230771190116035 280518666045346156785174053)
  ·
    refine ⟨52597249883502404397220135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280518666045346156785174053 52597249883502404397220135)
    ·
      refine ⟨78895874825253606595830203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52597249883502404397220135 78895874825253606595830203)
      ·
        refine ⟨118343812237880409893745305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78895874825253606595830203 118343812237880409893745305)
        ·
          refine ⟨88757859178410307420308979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118343812237880409893745305 88757859178410307420308979)
          ·
            refine ⟨133136788767615461130463469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88757859178410307420308979 133136788767615461130463469)
            ·
              refine ⟨49926295787855797923923801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133136788767615461130463469 49926295787855797923923801)
              ·
                refine ⟨37444721840891848442942851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49926295787855797923923801 37444721840891848442942851)
                ·
                  refine ⟨56167082761337772664414277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37444721840891848442942851 56167082761337772664414277)
                  ·
                    refine ⟨10531328017750832374577677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56167082761337772664414277 10531328017750832374577677)
                    ·
                      refine ⟨3949248006656562140466629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10531328017750832374577677 3949248006656562140466629)
                      ·
                        rfl

theorem cell23_7691133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_7691133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691133 prefixEnd_7691133 := by exact prefixLift 7691133
  have htrace : WordTrace (prefixWord ++ tailWord_7691133) baseStart_7691133 baseEnd_7691133 := by
    simpa [prefixWord, tailWord_7691133, baseEnd_7691133] using wordTrace_append hprefix tailTrace_7691133
  have hstable : (prefixWord ++ tailWord_7691133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691133).length < 2 ^ (prefixWord ++ tailWord_7691133).sum := by decide
  have hdescent : baseEnd_7691133 < baseStart_7691133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691157 : List Nat := [1, 3, 2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_7691157 : Nat := 118140960795 + 7691157 * 2 ^ 59
def prefixEnd_7691157 : Nat := 4983230072969 + 3 ^ 40 * 7691157 * 2
def baseEnd_7691157 : Nat := 1316420110064090015522173

theorem tailTrace_7691157 : CollatzResearch.WordTrace tailWord_7691157 prefixEnd_7691157 1316420110064090015522173 := by
  unfold tailWord_7691157
  simp only [CollatzResearch.WordTrace]
  refine ⟨280519541397259208884047725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187013027598172805922698483 280519541397259208884047725)
  ·
    refine ⟨105194828023972203331517897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280519541397259208884047725 105194828023972203331517897)
    ·
      refine ⟨78896121017979152498638423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105194828023972203331517897 78896121017979152498638423)
      ·
        refine ⟨118344181526968728747957635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78896121017979152498638423 118344181526968728747957635)
        ·
          refine ⟨177516272290453093121936453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118344181526968728747957635 177516272290453093121936453)
          ·
            refine ⟨33284301054459954960363085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177516272290453093121936453 33284301054459954960363085)
            ·
              refine ⟨12481612895422483110136157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33284301054459954960363085 12481612895422483110136157)
              ·
                refine ⟨4680604835783431166301059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12481612895422483110136157 4680604835783431166301059)
                ·
                  refine ⟨7020907253675146749451589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680604835783431166301059 7020907253675146749451589)
                  ·
                    refine ⟨1316420110064090015522173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7020907253675146749451589 1316420110064090015522173)
                    ·
                      rfl

theorem cell23_7691157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_7691157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691157 prefixEnd_7691157 := by exact prefixLift 7691157
  have htrace : WordTrace (prefixWord ++ tailWord_7691157) baseStart_7691157 baseEnd_7691157 := by
    simpa [prefixWord, tailWord_7691157, baseEnd_7691157] using wordTrace_append hprefix tailTrace_7691157
  have hstable : (prefixWord ++ tailWord_7691157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691157).length < 2 ^ (prefixWord ++ tailWord_7691157).sum := by decide
  have hdescent : baseEnd_7691157 < baseStart_7691157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691200 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 1, 5]
def baseStart_7691200 : Nat := 118140960795 + 7691200 * 2 ^ 59
def prefixEnd_7691200 : Nat := 4983230072969 + 3 ^ 40 * 7691200 * 2
def baseEnd_7691200 : Nat := 1316427469953471126109607

theorem tailTrace_7691200 : CollatzResearch.WordTrace tailWord_7691200 prefixEnd_7691200 1316427469953471126109607 := by
  unfold tailWord_7691200
  simp only [CollatzResearch.WordTrace]
  refine ⟨140260554868051713613931527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187014073157402284818575369 140260554868051713613931527)
  ·
    refine ⟨210390832302077570420897291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140260554868051713613931527 210390832302077570420897291)
    ·
      refine ⟨315586248453116355631345937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210390832302077570420897291 315586248453116355631345937)
      ·
        refine ⟨236689686339837266723509453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315586248453116355631345937 236689686339837266723509453)
        ·
          refine ⟨88758632377438975021316045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236689686339837266723509453 88758632377438975021316045)
          ·
            refine ⟨33284487141539615632993517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88758632377438975021316045 33284487141539615632993517)
            ·
              refine ⟨12481682678077355862372569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33284487141539615632993517 12481682678077355862372569)
              ·
                refine ⟨9361262008558016896779427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12481682678077355862372569 9361262008558016896779427)
                ·
                  refine ⟨14041893012837025345169141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9361262008558016896779427 14041893012837025345169141)
                  ·
                    refine ⟨1316427469953471126109607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14041893012837025345169141 1316427469953471126109607)
                    ·
                      rfl

theorem cell23_7691200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 5].length) (baseStart_7691200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691200 prefixEnd_7691200 := by exact prefixLift 7691200
  have htrace : WordTrace (prefixWord ++ tailWord_7691200) baseStart_7691200 baseEnd_7691200 := by
    simpa [prefixWord, tailWord_7691200, baseEnd_7691200] using wordTrace_append hprefix tailTrace_7691200
  have hstable : (prefixWord ++ tailWord_7691200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691200).length < 2 ^ (prefixWord ++ tailWord_7691200).sum := by decide
  have hdescent : baseEnd_7691200 < baseStart_7691200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691203 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 4]
def baseStart_7691203 : Nat := 118140960795 + 7691203 * 2 ^ 59
def prefixEnd_7691203 : Nat := 4983230072969 + 3 ^ 40 * 7691203 * 2
def baseEnd_7691203 : Nat := 3949283950302376866591307

theorem tailTrace_7691203 : CollatzResearch.WordTrace tailWord_7691203 prefixEnd_7691203 3949283950302376866591307 := by
  unfold tailWord_7691203
  simp only [CollatzResearch.WordTrace]
  refine ⟨280521219155092558740222263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187014146103395039160148175 280521219155092558740222263)
  ·
    refine ⟨420781828732638838110333395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280521219155092558740222263 420781828732638838110333395)
    ·
      refine ⟨631172743098958257165500093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420781828732638838110333395 631172743098958257165500093)
      ·
        refine ⟨236689778662109346437062535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631172743098958257165500093 236689778662109346437062535)
        ·
          refine ⟨355034667993164019655593803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236689778662109346437062535 355034667993164019655593803)
          ·
            refine ⟨532552001989746029483390705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355034667993164019655593803 532552001989746029483390705)
            ·
              refine ⟨399414001492309522112543029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532552001989746029483390705 399414001492309522112543029)
              ·
                refine ⟨37445062639904017698050909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399414001492309522112543029 37445062639904017698050909)
                ·
                  refine ⟨14041898489964006636769091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37445062639904017698050909 14041898489964006636769091)
                  ·
                    refine ⟨21062847734946009955153637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14041898489964006636769091 21062847734946009955153637)
                    ·
                      refine ⟨3949283950302376866591307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21062847734946009955153637 3949283950302376866591307)
                      ·
                        rfl

theorem cell23_7691203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_7691203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691203 prefixEnd_7691203 := by exact prefixLift 7691203
  have htrace : WordTrace (prefixWord ++ tailWord_7691203) baseStart_7691203 baseEnd_7691203 := by
    simpa [prefixWord, tailWord_7691203, baseEnd_7691203] using wordTrace_append hprefix tailTrace_7691203
  have hstable : (prefixWord ++ tailWord_7691203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691203).length < 2 ^ (prefixWord ++ tailWord_7691203).sum := by decide
  have hdescent : baseEnd_7691203 < baseStart_7691203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691223 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_7691223 : Nat := 118140960795 + 7691223 * 2 ^ 59
def prefixEnd_7691223 : Nat := 4983230072969 + 3 ^ 40 * 7691223 * 2
def baseEnd_7691223 : Nat := 3949294219915466788341215

theorem tailTrace_7691223 : CollatzResearch.WordTrace tailWord_7691223 prefixEnd_7691223 3949294219915466788341215 := by
  unfold tailWord_7691223
  simp only [CollatzResearch.WordTrace]
  refine ⟨280521948615020102155950323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187014632410013401437300215 280521948615020102155950323)
  ·
    refine ⟨420782922922530153233925485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280521948615020102155950323 420782922922530153233925485)
    ·
      refine ⟨157793596095948807462722057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420782922922530153233925485 157793596095948807462722057)
      ·
        refine ⟨118345197071961605597041543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157793596095948807462722057 118345197071961605597041543)
        ·
          refine ⟨177517795607942408395562315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118345197071961605597041543 177517795607942408395562315)
          ·
            refine ⟨266276693411913612593343473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177517795607942408395562315 266276693411913612593343473)
            ·
              refine ⟨199707520058935209445007605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266276693411913612593343473 199707520058935209445007605)
              ·
                refine ⟨18722580005525175885469463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199707520058935209445007605 18722580005525175885469463)
                ·
                  refine ⟨28083870008287763828204195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18722580005525175885469463 28083870008287763828204195)
                  ·
                    refine ⟨42125805012431645742306293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28083870008287763828204195 42125805012431645742306293)
                    ·
                      refine ⟨3949294219915466788341215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42125805012431645742306293 3949294219915466788341215)
                      ·
                        rfl

theorem cell23_7691223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_7691223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691223 prefixEnd_7691223 := by exact prefixLift 7691223
  have htrace : WordTrace (prefixWord ++ tailWord_7691223) baseStart_7691223 baseEnd_7691223 := by
    simpa [prefixWord, tailWord_7691223, baseEnd_7691223] using wordTrace_append hprefix tailTrace_7691223
  have hstable : (prefixWord ++ tailWord_7691223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691223).length < 2 ^ (prefixWord ++ tailWord_7691223).sum := by decide
  have hdescent : baseEnd_7691223 < baseStart_7691223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691233 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_7691233 : Nat := 118140960795 + 7691233 * 2 ^ 59
def prefixEnd_7691233 : Nat := 4983230072969 + 3 ^ 40 * 7691233 * 2
def baseEnd_7691233 : Nat := 3949299354722011749216169

theorem tailTrace_7691233 : CollatzResearch.WordTrace tailWord_7691233 prefixEnd_7691233 3949299354722011749216169 := by
  unfold tailWord_7691233
  simp only [CollatzResearch.WordTrace]
  refine ⟨280522313344983873863814353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187014875563322582575876235 280522313344983873863814353)
  ·
    refine ⟨210391735008737905397860765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280522313344983873863814353 210391735008737905397860765)
    ·
      refine ⟨78896900628276714524197787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210391735008737905397860765 78896900628276714524197787)
      ·
        refine ⟨118345350942415071786296681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78896900628276714524197787 118345350942415071786296681)
        ·
          refine ⟨88759013206811303839722511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118345350942415071786296681 88759013206811303839722511)
          ·
            refine ⟨133138519810216955759583767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88759013206811303839722511 133138519810216955759583767)
            ·
              refine ⟨199707779715325433639375651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133138519810216955759583767 199707779715325433639375651)
              ·
                refine ⟨299561669572988150459063477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199707779715325433639375651 299561669572988150459063477)
                ·
                  refine ⟨28083906522467639105537201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 299561669572988150459063477 28083906522467639105537201)
                  ·
                    refine ⟨21062929891850729329152901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28083906522467639105537201 21062929891850729329152901)
                    ·
                      refine ⟨3949299354722011749216169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21062929891850729329152901 3949299354722011749216169)
                      ·
                        rfl

theorem cell23_7691233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_7691233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691233 prefixEnd_7691233 := by exact prefixLift 7691233
  have htrace : WordTrace (prefixWord ++ tailWord_7691233) baseStart_7691233 baseEnd_7691233 := by
    simpa [prefixWord, tailWord_7691233, baseEnd_7691233] using wordTrace_append hprefix tailTrace_7691233
  have hstable : (prefixWord ++ tailWord_7691233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691233).length < 2 ^ (prefixWord ++ tailWord_7691233).sum := by decide
  have hdescent : baseEnd_7691233 < baseStart_7691233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691240 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_7691240 : Nat := 118140960795 + 7691240 * 2 ^ 59
def prefixEnd_7691240 : Nat := 4983230072969 + 3 ^ 40 * 7691240 * 2
def baseEnd_7691240 : Nat := 3949302949086593221828637

theorem tailTrace_7691240 : CollatzResearch.WordTrace tailWord_7691240 prefixEnd_7691240 3949302949086593221828637 := by
  unfold tailWord_7691240
  simp only [CollatzResearch.WordTrace]
  refine ⟨140261284327979257029659587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187015045770639009372879449 140261284327979257029659587)
  ·
    refine ⟨210391926491968885544489381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140261284327979257029659587 210391926491968885544489381)
    ·
      refine ⟨39448486217244166039591759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210391926491968885544489381 39448486217244166039591759)
      ·
        refine ⟨59172729325866249059387639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39448486217244166039591759 59172729325866249059387639)
        ·
          refine ⟨88759093988799373589081459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59172729325866249059387639 88759093988799373589081459)
          ·
            refine ⟨133138640983199060383622189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88759093988799373589081459 133138640983199060383622189)
            ·
              refine ⟨49926990368699647643858321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133138640983199060383622189 49926990368699647643858321)
              ·
                refine ⟨37445242776524735732893741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49926990368699647643858321 37445242776524735732893741)
                ·
                  refine ⟨14041966041196775899835153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37445242776524735732893741 14041966041196775899835153)
                  ·
                    refine ⟨10531474530897581924876365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14041966041196775899835153 10531474530897581924876365)
                    ·
                      refine ⟨3949302949086593221828637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10531474530897581924876365 3949302949086593221828637)
                      ·
                        rfl

theorem cell23_7691240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_7691240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691240 prefixEnd_7691240 := by exact prefixLift 7691240
  have htrace : WordTrace (prefixWord ++ tailWord_7691240) baseStart_7691240 baseEnd_7691240 := by
    simpa [prefixWord, tailWord_7691240, baseEnd_7691240] using wordTrace_append hprefix tailTrace_7691240
  have hstable : (prefixWord ++ tailWord_7691240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691240).length < 2 ^ (prefixWord ++ tailWord_7691240).sum := by decide
  have hdescent : baseEnd_7691240 < baseStart_7691240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691254 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_7691254 : Nat := 118140960795 + 7691254 * 2 ^ 59
def prefixEnd_7691254 : Nat := 4983230072969 + 3 ^ 40 * 7691254 * 2
def baseEnd_7691254 : Nat := 3949310137815756167053573

theorem tailTrace_7691254 : CollatzResearch.WordTrace tailWord_7691254 prefixEnd_7691254 3949310137815756167053573 := by
  unfold tailWord_7691254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17532692454869237153145551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187015386185271862966885877 17532692454869237153145551)
  ·
    refine ⟨26299038682303855729718327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17532692454869237153145551 26299038682303855729718327)
    ·
      refine ⟨39448558023455783594577491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26299038682303855729718327 39448558023455783594577491)
      ·
        refine ⟨59172837035183675391866237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39448558023455783594577491 59172837035183675391866237)
        ·
          refine ⟨22189813888193878271949839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59172837035183675391866237 22189813888193878271949839)
          ·
            refine ⟨33284720832290817407924759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22189813888193878271949839 33284720832290817407924759)
            ·
              refine ⟨49927081248436226111887139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33284720832290817407924759 49927081248436226111887139)
              ·
                refine ⟨74890621872654339167830709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49927081248436226111887139 74890621872654339167830709)
                ·
                  refine ⟨7020995800561344296984129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74890621872654339167830709 7020995800561344296984129)
                  ·
                    refine ⟨5265746850421008222738097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7020995800561344296984129 5265746850421008222738097)
                    ·
                      refine ⟨3949310137815756167053573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265746850421008222738097 3949310137815756167053573)
                      ·
                        rfl

theorem cell23_7691254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_7691254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691254 prefixEnd_7691254 := by exact prefixLift 7691254
  have htrace : WordTrace (prefixWord ++ tailWord_7691254) baseStart_7691254 baseEnd_7691254 := by
    simpa [prefixWord, tailWord_7691254, baseEnd_7691254] using wordTrace_append hprefix tailTrace_7691254
  have hstable : (prefixWord ++ tailWord_7691254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691254).length < 2 ^ (prefixWord ++ tailWord_7691254).sum := by decide
  have hdescent : baseEnd_7691254 < baseStart_7691254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691260 : List Nat := [2, 2, 2, 1, 2, 4, 3, 7]
def baseStart_7691260 : Nat := 118140960795 + 7691260 * 2 ^ 59
def prefixEnd_7691260 : Nat := 4983230072969 + 3 ^ 40 * 7691260 * 2
def baseEnd_7691260 : Nat := 146270859951840116428835

theorem tailTrace_7691260 : CollatzResearch.WordTrace tailWord_7691260 prefixEnd_7691260 146270859951840116428835 := by
  unfold tailWord_7691260
  simp only [CollatzResearch.WordTrace]
  refine ⟨140261649057943028737523617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187015532077257371650031489 140261649057943028737523617)
  ·
    refine ⟨105196236793457271553142713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140261649057943028737523617 105196236793457271553142713)
    ·
      refine ⟨78897177595092953664857035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105196236793457271553142713 78897177595092953664857035)
      ·
        refine ⟨118345766392639430497285553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78897177595092953664857035 118345766392639430497285553)
        ·
          refine ⟨88759324794479572872964165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118345766392639430497285553 88759324794479572872964165)
          ·
            refine ⟨16642373398964919913680781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88759324794479572872964165 16642373398964919913680781)
            ·
              refine ⟨6240890024611844967630293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16642373398964919913680781 6240890024611844967630293)
              ·
                refine ⟨146270859951840116428835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6240890024611844967630293 146270859951840116428835)
                ·
                  rfl

theorem cell23_7691260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 7].length) (baseStart_7691260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691260 prefixEnd_7691260 := by exact prefixLift 7691260
  have htrace : WordTrace (prefixWord ++ tailWord_7691260) baseStart_7691260 baseEnd_7691260 := by
    simpa [prefixWord, tailWord_7691260, baseEnd_7691260] using wordTrace_append hprefix tailTrace_7691260
  have hstable : (prefixWord ++ tailWord_7691260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691260).length < 2 ^ (prefixWord ++ tailWord_7691260).sum := by decide
  have hdescent : baseEnd_7691260 < baseStart_7691260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691271 : List Nat := [1, 1, 4, 3, 1, 1, 4, 3, 1, 2, 2]
def baseStart_7691271 : Nat := 118140960795 + 7691271 * 2 ^ 59
def prefixEnd_7691271 : Nat := 4983230072969 + 3 ^ 40 * 7691271 * 2
def baseEnd_7691271 : Nat := 3949318866986882600540995

theorem tailTrace_7691271 : CollatzResearch.WordTrace tailWord_7691271 prefixEnd_7691271 3949318866986882600540995 := by
  unfold tailWord_7691271
  simp only [CollatzResearch.WordTrace]
  refine ⟨280523699318846206353697667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187015799545897470902465111 280523699318846206353697667)
  ·
    refine ⟨420785548978269309530546501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280523699318846206353697667 420785548978269309530546501)
    ·
      refine ⟨78897290433425495536977469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420785548978269309530546501 78897290433425495536977469)
      ·
        refine ⟨29586483912534560826366551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78897290433425495536977469 29586483912534560826366551)
        ·
          refine ⟨44379725868801841239549827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29586483912534560826366551 44379725868801841239549827)
          ·
            refine ⟨66569588803202761859324741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44379725868801841239549827 66569588803202761859324741)
            ·
              refine ⟨12481797900600517848623389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66569588803202761859324741 12481797900600517848623389)
              ·
                refine ⟨4680674212725194193233771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12481797900600517848623389 4680674212725194193233771)
                ·
                  refine ⟨7021011319087791289850657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680674212725194193233771 7021011319087791289850657)
                  ·
                    refine ⟨5265758489315843467387993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7021011319087791289850657 5265758489315843467387993)
                    ·
                      refine ⟨3949318866986882600540995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265758489315843467387993 3949318866986882600540995)
                      ·
                        rfl

theorem cell23_7691271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_7691271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691271 prefixEnd_7691271 := by exact prefixLift 7691271
  have htrace : WordTrace (prefixWord ++ tailWord_7691271) baseStart_7691271 baseEnd_7691271 := by
    simpa [prefixWord, tailWord_7691271, baseEnd_7691271] using wordTrace_append hprefix tailTrace_7691271
  have hstable : (prefixWord ++ tailWord_7691271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691271).length < 2 ^ (prefixWord ++ tailWord_7691271).sum := by decide
  have hdescent : baseEnd_7691271 < baseStart_7691271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691274 : List Nat := [3, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3]
def baseStart_7691274 : Nat := 118140960795 + 7691274 * 2 ^ 59
def prefixEnd_7691274 : Nat := 4983230072969 + 3 ^ 40 * 7691274 * 2
def baseEnd_7691274 : Nat := 3949320407428846088803481

theorem tailTrace_7691274 : CollatzResearch.WordTrace tailWord_7691274 prefixEnd_7691274 3949320407428846088803481 := by
  unfold tailWord_7691274
  simp only [CollatzResearch.WordTrace]
  refine ⟨70130952184458834466514219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187015872491890225244037917 70130952184458834466514219)
  ·
    refine ⟨105196428276688251699771329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70130952184458834466514219 105196428276688251699771329)
    ·
      refine ⟨78897321207516188774828497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105196428276688251699771329 78897321207516188774828497)
      ·
        refine ⟨59172990905637141581121373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78897321207516188774828497 59172990905637141581121373)
        ·
          refine ⟨22189871589613928092920515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59172990905637141581121373 22189871589613928092920515)
          ·
            refine ⟨33284807384420892139380773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22189871589613928092920515 33284807384420892139380773)
            ·
              refine ⟨6240901384578917276133895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33284807384420892139380773 6240901384578917276133895)
              ·
                refine ⟨9361352076868375914200843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240901384578917276133895 9361352076868375914200843)
                ·
                  refine ⟨14042028115302563871301265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9361352076868375914200843 14042028115302563871301265)
                  ·
                    refine ⟨10531521086476922903475949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14042028115302563871301265 10531521086476922903475949)
                    ·
                      refine ⟨3949320407428846088803481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10531521086476922903475949 3949320407428846088803481)
                      ·
                        rfl

theorem cell23_7691274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_7691274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691274 prefixEnd_7691274 := by exact prefixLift 7691274
  have htrace : WordTrace (prefixWord ++ tailWord_7691274) baseStart_7691274 baseEnd_7691274 := by
    simpa [prefixWord, tailWord_7691274, baseEnd_7691274] using wordTrace_append hprefix tailTrace_7691274
  have hstable : (prefixWord ++ tailWord_7691274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691274).length < 2 ^ (prefixWord ++ tailWord_7691274).sum := by decide
  have hdescent : baseEnd_7691274 < baseStart_7691274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691314 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2]
def baseStart_7691314 : Nat := 118140960795 + 7691314 * 2 ^ 59
def prefixEnd_7691314 : Nat := 4983230072969 + 3 ^ 40 * 7691314 * 2
def baseEnd_7691314 : Nat := 3949340946655025932303297

theorem tailTrace_7691314 : CollatzResearch.WordTrace tailWord_7691314 prefixEnd_7691314 3949340946655025932303297 := by
  unfold tailWord_7691314
  simp only [CollatzResearch.WordTrace]
  refine ⟨70131316914422606174378249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187016845105126949798341997 70131316914422606174378249)
  ·
    refine ⟨52598487685816954630783687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70131316914422606174378249 52598487685816954630783687)
    ·
      refine ⟨78897731528725431946175531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52598487685816954630783687 78897731528725431946175531)
      ·
        refine ⟨118346597293088147919263297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78897731528725431946175531 118346597293088147919263297)
        ·
          refine ⟨88759947969816110939447473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118346597293088147919263297 88759947969816110939447473)
          ·
            refine ⟨66569960977362083204585605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88759947969816110939447473 66569960977362083204585605)
            ·
              refine ⟨12481867683255390600859801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66569960977362083204585605 12481867683255390600859801)
              ·
                refine ⟨9361400762441542950644851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12481867683255390600859801 9361400762441542950644851)
                ·
                  refine ⟨14042101143662314425967277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9361400762441542950644851 14042101143662314425967277)
                  ·
                    refine ⟨5265787928873367909737729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14042101143662314425967277 5265787928873367909737729)
                    ·
                      refine ⟨3949340946655025932303297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265787928873367909737729 3949340946655025932303297)
                      ·
                        rfl

theorem cell23_7691314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_7691314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691314 prefixEnd_7691314 := by exact prefixLift 7691314
  have htrace : WordTrace (prefixWord ++ tailWord_7691314) baseStart_7691314 baseEnd_7691314 := by
    simpa [prefixWord, tailWord_7691314, baseEnd_7691314] using wordTrace_append hprefix tailTrace_7691314
  have hstable : (prefixWord ++ tailWord_7691314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691314).length < 2 ^ (prefixWord ++ tailWord_7691314).sum := by decide
  have hdescent : baseEnd_7691314 < baseStart_7691314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691333 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 9]
def baseStart_7691333 : Nat := 118140960795 + 7691333 * 2 ^ 59
def prefixEnd_7691333 : Nat := 4983230072969 + 3 ^ 40 * 7691333 * 2
def baseEnd_7691333 : Nat := 438816744754162373107301

theorem tailTrace_7691333 : CollatzResearch.WordTrace tailWord_7691333 prefixEnd_7691333 438816744754162373107301 := by
  unfold tailWord_7691333
  simp only [CollatzResearch.WordTrace]
  refine ⟨280525960644621590942454653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187017307096414393961636435 280525960644621590942454653)
  ·
    refine ⟨105197235241733096603420495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280525960644621590942454653 105197235241733096603420495)
    ·
      refine ⟨157795852862599644905130743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105197235241733096603420495 157795852862599644905130743)
      ·
        refine ⟨236693779293899467357696115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157795852862599644905130743 236693779293899467357696115)
        ·
          refine ⟨355040668940849201036544173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236693779293899467357696115 355040668940849201036544173)
          ·
            refine ⟨133140250852818450388704065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355040668940849201036544173 133140250852818450388704065)
            ·
              refine ⟨99855188139613837791528049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133140250852818450388704065 99855188139613837791528049)
              ·
                refine ⟨74891391104710378343646037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99855188139613837791528049 74891391104710378343646037)
                ·
                  refine ⟨438816744754162373107301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74891391104710378343646037 438816744754162373107301)
                  ·
                    rfl

theorem cell23_7691333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_7691333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691333 prefixEnd_7691333 := by exact prefixLift 7691333
  have htrace : WordTrace (prefixWord ++ tailWord_7691333) baseStart_7691333 baseEnd_7691333 := by
    simpa [prefixWord, tailWord_7691333, baseEnd_7691333] using wordTrace_append hprefix tailTrace_7691333
  have hstable : (prefixWord ++ tailWord_7691333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691333).length < 2 ^ (prefixWord ++ tailWord_7691333).sum := by decide
  have hdescent : baseEnd_7691333 < baseStart_7691333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691353 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_7691353 : Nat := 118140960795 + 7691353 * 2 ^ 59
def prefixEnd_7691353 : Nat := 4983230072969 + 3 ^ 40 * 7691353 * 2
def baseEnd_7691353 : Nat := 3949360972400551279715617

theorem tailTrace_7691353 : CollatzResearch.WordTrace tailWord_7691353 prefixEnd_7691353 3949360972400551279715617 := by
  unfold tailWord_7691353
  simp only [CollatzResearch.WordTrace]
  refine ⟨280526690104549134358182713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187017793403032756238788475 280526690104549134358182713)
  ·
    refine ⟨210395017578411850768637035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280526690104549134358182713 210395017578411850768637035)
    ·
      refine ⟨315592526367617776152955553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210395017578411850768637035 315592526367617776152955553)
      ·
        refine ⟨236694394775713332114716665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315592526367617776152955553 236694394775713332114716665)
        ·
          refine ⟨177520796081784999086037499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236694394775713332114716665 177520796081784999086037499)
          ·
            refine ⟨266281194122677498629056249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177520796081784999086037499 266281194122677498629056249)
            ·
              refine ⟨199710895592008123971792187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266281194122677498629056249 199710895592008123971792187)
              ·
                refine ⟨299566343388012185957688281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199710895592008123971792187 299566343388012185957688281)
                ·
                  refine ⟨224674757541009139468266211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299566343388012185957688281 224674757541009139468266211)
                  ·
                    refine ⟨337012136311513709202399317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 224674757541009139468266211 337012136311513709202399317)
                    ·
                      refine ⟨3949360972400551279715617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 337012136311513709202399317 3949360972400551279715617)
                      ·
                        rfl

theorem cell23_7691353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_7691353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691353 prefixEnd_7691353 := by exact prefixLift 7691353
  have htrace : WordTrace (prefixWord ++ tailWord_7691353) baseStart_7691353 baseEnd_7691353 := by
    simpa [prefixWord, tailWord_7691353, baseEnd_7691353] using wordTrace_append hprefix tailTrace_7691353
  have hstable : (prefixWord ++ tailWord_7691353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691353).length < 2 ^ (prefixWord ++ tailWord_7691353).sum := by decide
  have hdescent : baseEnd_7691353 < baseStart_7691353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691360 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 3]
def baseStart_7691360 : Nat := 118140960795 + 7691360 * 2 ^ 59
def prefixEnd_7691360 : Nat := 4983230072969 + 3 ^ 40 * 7691360 * 2
def baseEnd_7691360 : Nat := 3949364566765132752328085

theorem tailTrace_7691360 : CollatzResearch.WordTrace tailWord_7691360 prefixEnd_7691360 3949364566765132752328085 := by
  unfold tailWord_7691360
  simp only [CollatzResearch.WordTrace]
  refine ⟨140263472707761887276843767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187017963610349183035791689 140263472707761887276843767)
  ·
    refine ⟨210395209061642830915265651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140263472707761887276843767 210395209061642830915265651)
    ·
      refine ⟨315592813592464246372898477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210395209061642830915265651 315592813592464246372898477)
      ·
        refine ⟨118347305097174092389836929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315592813592464246372898477 118347305097174092389836929)
        ·
          refine ⟨88760478822880569292377697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118347305097174092389836929 88760478822880569292377697)
          ·
            refine ⟨66570359117160426969283273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88760478822880569292377697 66570359117160426969283273)
            ·
              refine ⟨49927769337870320226962455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66570359117160426969283273 49927769337870320226962455)
              ·
                refine ⟨74891654006805480340443683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49927769337870320226962455 74891654006805480340443683)
                ·
                  refine ⟨112337481010208220510665525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74891654006805480340443683 112337481010208220510665525)
                  ·
                    refine ⟨10531638844707020672874893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112337481010208220510665525 10531638844707020672874893)
                    ·
                      refine ⟨3949364566765132752328085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10531638844707020672874893 3949364566765132752328085)
                      ·
                        rfl

theorem cell23_7691360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_7691360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691360 prefixEnd_7691360 := by exact prefixLift 7691360
  have htrace : WordTrace (prefixWord ++ tailWord_7691360) baseStart_7691360 baseEnd_7691360 := by
    simpa [prefixWord, tailWord_7691360, baseEnd_7691360] using wordTrace_append hprefix tailTrace_7691360
  have hstable : (prefixWord ++ tailWord_7691360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691360).length < 2 ^ (prefixWord ++ tailWord_7691360).sum := by decide
  have hdescent : baseEnd_7691360 < baseStart_7691360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691361 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_7691361 : Nat := 118140960795 + 7691361 * 2 ^ 59
def prefixEnd_7691361 : Nat := 4983230072969 + 3 ^ 40 * 7691361 * 2
def baseEnd_7691361 : Nat := 3949365080245787248415581

theorem tailTrace_7691361 : CollatzResearch.WordTrace tailWord_7691361 prefixEnd_7691361 3949365080245787248415581 := by
  unfold tailWord_7691361
  simp only [CollatzResearch.WordTrace]
  refine ⟨280526981888520151724473937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187017987925680101149649291 280526981888520151724473937)
  ·
    refine ⟨210395236416390113793355453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280526981888520151724473937 210395236416390113793355453)
    ·
      refine ⟨78898213656146292672508295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210395236416390113793355453 78898213656146292672508295)
      ·
        refine ⟨118347320484219439008762443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78898213656146292672508295 118347320484219439008762443)
        ·
          refine ⟨177520980726329158513143665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118347320484219439008762443 177520980726329158513143665)
          ·
            refine ⟨133140735544746868884857749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177520980726329158513143665 133140735544746868884857749)
            ·
              refine ⟨6240971978660009478977707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133140735544746868884857749 6240971978660009478977707)
              ·
                refine ⟨9361457967990014218466561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6240971978660009478977707 9361457967990014218466561)
                ·
                  refine ⟨7021093475992510663849921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9361457967990014218466561 7021093475992510663849921)
                  ·
                    refine ⟨5265820106994382997887441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7021093475992510663849921 5265820106994382997887441)
                    ·
                      refine ⟨3949365080245787248415581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265820106994382997887441 3949365080245787248415581)
                      ·
                        rfl

theorem cell23_7691361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_7691361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691361 prefixEnd_7691361 := by exact prefixLift 7691361
  have htrace : WordTrace (prefixWord ++ tailWord_7691361) baseStart_7691361 baseEnd_7691361 := by
    simpa [prefixWord, tailWord_7691361, baseEnd_7691361] using wordTrace_append hprefix tailTrace_7691361
  have hstable : (prefixWord ++ tailWord_7691361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691361).length < 2 ^ (prefixWord ++ tailWord_7691361).sum := by decide
  have hdescent : baseEnd_7691361 < baseStart_7691361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691434 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7691434 : Nat := 118140960795 + 7691434 * 2 ^ 59
def prefixEnd_7691434 : Nat := 4983230072969 + 3 ^ 40 * 7691434 * 2
def baseEnd_7691434 : Nat := 3949402564333565462802745

theorem tailTrace_7691434 : CollatzResearch.WordTrace tailWord_7691434 prefixEnd_7691434 3949402564333565462802745 := by
  unfold tailWord_7691434
  simp only [CollatzResearch.WordTrace]
  refine ⟨70132411104313921297970339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187019762944837123461254237 70132411104313921297970339)
  ·
    refine ⟨105198616656470881946955509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70132411104313921297970339 105198616656470881946955509)
    ·
      refine ⟨9862370311544145182527079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105198616656470881946955509 9862370311544145182527079)
      ·
        refine ⟨14793555467316217773790619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9862370311544145182527079 14793555467316217773790619)
        ·
          refine ⟨22190333200974326660685929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14793555467316217773790619 22190333200974326660685929)
          ·
            refine ⟨16642749900730744995514447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22190333200974326660685929 16642749900730744995514447)
            ·
              refine ⟨24964124851096117493271671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16642749900730744995514447 24964124851096117493271671)
              ·
                refine ⟨37446187276644176239907507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24964124851096117493271671 37446187276644176239907507)
                ·
                  refine ⟨56169280914966264359861261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37446187276644176239907507 56169280914966264359861261)
                  ·
                    refine ⟨21063480343112349134947973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56169280914966264359861261 21063480343112349134947973)
                    ·
                      refine ⟨3949402564333565462802745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21063480343112349134947973 3949402564333565462802745)
                      ·
                        rfl

theorem cell23_7691434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7691434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691434 prefixEnd_7691434 := by exact prefixLift 7691434
  have htrace : WordTrace (prefixWord ++ tailWord_7691434) baseStart_7691434 baseEnd_7691434 := by
    simpa [prefixWord, tailWord_7691434, baseEnd_7691434] using wordTrace_append hprefix tailTrace_7691434
  have hstable : (prefixWord ++ tailWord_7691434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691434).length < 2 ^ (prefixWord ++ tailWord_7691434).sum := by decide
  have hdescent : baseEnd_7691434 < baseStart_7691434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691474 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 6]
def baseStart_7691474 : Nat := 118140960795 + 7691474 * 2 ^ 59
def prefixEnd_7691474 : Nat := 4983230072969 + 3 ^ 40 * 7691474 * 2
def baseEnd_7691474 : Nat := 438824789284416145144729

theorem tailTrace_7691474 : CollatzResearch.WordTrace tailWord_7691474 prefixEnd_7691474 438824789284416145144729 := by
  unfold tailWord_7691474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70132775834277693005834369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187020735558073848015558317 70132775834277693005834369)
  ·
    refine ⟨52599581875708269754375777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70132775834277693005834369 52599581875708269754375777)
    ·
      refine ⟨39449686406781202315781833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52599581875708269754375777 39449686406781202315781833)
      ·
        refine ⟨29587264805085901736836375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39449686406781202315781833 29587264805085901736836375)
        ·
          refine ⟨44380897207628852605254563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29587264805085901736836375 44380897207628852605254563)
          ·
            refine ⟨66571345811443278907881845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44380897207628852605254563 66571345811443278907881845)
            ·
              refine ⟨6241063669822807397613923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66571345811443278907881845 6241063669822807397613923)
              ·
                refine ⟨9361595504734211096420885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6241063669822807397613923 9361595504734211096420885)
                ·
                  refine ⟨438824789284416145144729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9361595504734211096420885 438824789284416145144729)
                  ·
                    rfl

theorem cell23_7691474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_7691474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691474 prefixEnd_7691474 := by exact prefixLift 7691474
  have htrace : WordTrace (prefixWord ++ tailWord_7691474) baseStart_7691474 baseEnd_7691474 := by
    simpa [prefixWord, tailWord_7691474, baseEnd_7691474] using wordTrace_append hprefix tailTrace_7691474
  have hstable : (prefixWord ++ tailWord_7691474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691474).length < 2 ^ (prefixWord ++ tailWord_7691474).sum := by decide
  have hdescent : baseEnd_7691474 < baseStart_7691474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691487 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 1, 5]
def baseStart_7691487 : Nat := 118140960795 + 7691487 * 2 ^ 59
def prefixEnd_7691487 : Nat := 4983230072969 + 3 ^ 40 * 7691487 * 2
def baseEnd_7691487 : Nat := 1316476592936084585146667

theorem tailTrace_7691487 : CollatzResearch.WordTrace tailWord_7691487 prefixEnd_7691487 1316476592936084585146667 := by
  unfold tailWord_7691487
  simp only [CollatzResearch.WordTrace]
  refine ⟨280531577486063675243560715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187021051657375783495707143 280531577486063675243560715)
  ·
    refine ⟨420797366229095512865341073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280531577486063675243560715 420797366229095512865341073)
    ·
      refine ⟨315598024671821634649005805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420797366229095512865341073 315598024671821634649005805)
      ·
        refine ⟨118349259251933112993377177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315598024671821634649005805 118349259251933112993377177)
        ·
          refine ⟨88761944438949834745032883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118349259251933112993377177 88761944438949834745032883)
          ·
            refine ⟨133142916658424752117549325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88761944438949834745032883 133142916658424752117549325)
            ·
              refine ⟨49928593746909282044080997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133142916658424752117549325 49928593746909282044080997)
              ·
                refine ⟨9361611327545490383265187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49928593746909282044080997 9361611327545490383265187)
                ·
                  refine ⟨14042416991318235574897781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9361611327545490383265187 14042416991318235574897781)
                  ·
                    refine ⟨1316476592936084585146667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14042416991318235574897781 1316476592936084585146667)
                    ·
                      rfl

theorem cell23_7691487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 5].length) (baseStart_7691487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691487 prefixEnd_7691487 := by exact prefixLift 7691487
  have htrace : WordTrace (prefixWord ++ tailWord_7691487) baseStart_7691487 baseEnd_7691487 := by
    simpa [prefixWord, tailWord_7691487, baseEnd_7691487] using wordTrace_append hprefix tailTrace_7691487
  have hstable : (prefixWord ++ tailWord_7691487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691487).length < 2 ^ (prefixWord ++ tailWord_7691487).sum := by decide
  have hdescent : baseEnd_7691487 < baseStart_7691487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691495 : List Nat := [1, 1, 5, 3, 3, 1, 1, 3, 1, 4]
def baseStart_7691495 : Nat := 118140960795 + 7691495 * 2 ^ 59
def prefixEnd_7691495 : Nat := 4983230072969 + 3 ^ 40 * 7691495 * 2
def baseEnd_7691495 : Nat := 1316477962217829908046655

theorem tailTrace_7691495 : CollatzResearch.WordTrace tailWord_7691495 prefixEnd_7691495 1316477962217829908046655 := by
  unfold tailWord_7691495
  simp only [CollatzResearch.WordTrace]
  refine ⟨280531869270034692609851939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187021246180023128406567959 280531869270034692609851939)
  ·
    refine ⟨420797803905052038914777909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280531869270034692609851939 420797803905052038914777909)
    ·
      refine ⟨39449794116098628648260429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 420797803905052038914777909 39449794116098628648260429)
      ·
        refine ⟨14793672793536985743097661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39449794116098628648260429 14793672793536985743097661)
        ·
          refine ⟨5547627297576369653661623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14793672793536985743097661 5547627297576369653661623)
          ·
            refine ⟨8321440946364554480492435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547627297576369653661623 8321440946364554480492435)
            ·
              refine ⟨12482161419546831720738653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8321440946364554480492435 12482161419546831720738653)
              ·
                refine ⟨4680810532330061895276995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12482161419546831720738653 4680810532330061895276995)
                ·
                  refine ⟨7021215798495092842915493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680810532330061895276995 7021215798495092842915493)
                  ·
                    refine ⟨1316477962217829908046655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7021215798495092842915493 1316477962217829908046655)
                    ·
                      rfl

theorem cell23_7691495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_7691495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691495 prefixEnd_7691495 := by exact prefixLift 7691495
  have htrace : WordTrace (prefixWord ++ tailWord_7691495) baseStart_7691495 baseEnd_7691495 := by
    simpa [prefixWord, tailWord_7691495, baseEnd_7691495] using wordTrace_append hprefix tailTrace_7691495
  have hstable : (prefixWord ++ tailWord_7691495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691495).length < 2 ^ (prefixWord ++ tailWord_7691495).sum := by decide
  have hdescent : baseEnd_7691495 < baseStart_7691495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691518 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_7691518 : Nat := 118140960795 + 7691518 * 2 ^ 59
def prefixEnd_7691518 : Nat := 4983230072969 + 3 ^ 40 * 7691518 * 2
def baseEnd_7691518 : Nat := 3949445696708543134152359

theorem tailTrace_7691518 : CollatzResearch.WordTrace tailWord_7691518 prefixEnd_7691518 3949445696708543134152359 := by
  unfold tailWord_7691518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35066588518618920942242401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187021805432634245025292805 35066588518618920942242401)
  ·
    refine ⟨26299941388964190706681801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35066588518618920942242401 26299941388964190706681801)
    ·
      refine ⟨19724956041723143030011351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26299941388964190706681801 19724956041723143030011351)
      ·
        refine ⟨29587434062584714545017027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19724956041723143030011351 29587434062584714545017027)
        ·
          refine ⟨44381151093877071817525541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29587434062584714545017027 44381151093877071817525541)
          ·
            refine ⟨8321465830101950965786039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44381151093877071817525541 8321465830101950965786039)
            ·
              refine ⟨12482198745152926448679059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8321465830101950965786039 12482198745152926448679059)
              ·
                refine ⟨18723298117729389673018589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12482198745152926448679059 18723298117729389673018589)
                ·
                  refine ⟨7021236794148521127381971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18723298117729389673018589 7021236794148521127381971)
                  ·
                    refine ⟨10531855191222781691072957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7021236794148521127381971 10531855191222781691072957)
                    ·
                      refine ⟨3949445696708543134152359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10531855191222781691072957 3949445696708543134152359)
                      ·
                        rfl

theorem cell23_7691518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_7691518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691518 prefixEnd_7691518 := by exact prefixLift 7691518
  have htrace : WordTrace (prefixWord ++ tailWord_7691518) baseStart_7691518 baseEnd_7691518 := by
    simpa [prefixWord, tailWord_7691518, baseEnd_7691518] using wordTrace_append hprefix tailTrace_7691518
  have hstable : (prefixWord ++ tailWord_7691518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691518).length < 2 ^ (prefixWord ++ tailWord_7691518).sum := by decide
  have hdescent : baseEnd_7691518 < baseStart_7691518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691537 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_7691537 : Nat := 118140960795 + 7691537 * 2 ^ 59
def prefixEnd_7691537 : Nat := 4983230072969 + 3 ^ 40 * 7691537 * 2
def baseEnd_7691537 : Nat := 3949455452840978559814771

theorem tailTrace_7691537 : CollatzResearch.WordTrace tailWord_7691537 prefixEnd_7691537 3949455452840978559814771 := by
  unfold tailWord_7691537
  simp only [CollatzResearch.WordTrace]
  refine ⟨280533401135882533782880865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187022267423921689188587243 280533401135882533782880865)
  ·
    refine ⟨210400050851911900337160649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280533401135882533782880865 210400050851911900337160649)
    ·
      refine ⟨157800038138933925252870487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210400050851911900337160649 157800038138933925252870487)
      ·
        refine ⟨236700057208400887879305731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157800038138933925252870487 236700057208400887879305731)
        ·
          refine ⟨355050085812601331818958597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236700057208400887879305731 355050085812601331818958597)
          ·
            refine ⟨66571891089862749716054737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355050085812601331818958597 66571891089862749716054737)
            ·
              refine ⟨49928918317397062287041053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66571891089862749716054737 49928918317397062287041053)
              ·
                refine ⟨18723344369023898357640395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49928918317397062287041053 18723344369023898357640395)
                ·
                  refine ⟨28085016553535847536460593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18723344369023898357640395 28085016553535847536460593)
                  ·
                    refine ⟨21063762415151885652345445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28085016553535847536460593 21063762415151885652345445)
                    ·
                      refine ⟨3949455452840978559814771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21063762415151885652345445 3949455452840978559814771)
                      ·
                        rfl

theorem cell23_7691537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_7691537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691537 prefixEnd_7691537 := by exact prefixLift 7691537
  have htrace : WordTrace (prefixWord ++ tailWord_7691537) baseStart_7691537 baseEnd_7691537 := by
    simpa [prefixWord, tailWord_7691537, baseEnd_7691537] using wordTrace_append hprefix tailTrace_7691537
  have hstable : (prefixWord ++ tailWord_7691537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691537).length < 2 ^ (prefixWord ++ tailWord_7691537).sum := by decide
  have hdescent : baseEnd_7691537 < baseStart_7691537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691544 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_7691544 : Nat := 118140960795 + 7691544 * 2 ^ 59
def prefixEnd_7691544 : Nat := 4983230072969 + 3 ^ 40 * 7691544 * 2
def baseEnd_7691544 : Nat := 3949459047205560032427239

theorem tailTrace_7691544 : CollatzResearch.WordTrace tailWord_7691544 prefixEnd_7691544 3949459047205560032427239 := by
  unfold tailWord_7691544
  simp only [CollatzResearch.WordTrace]
  refine ⟨140266828223428586989192843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187022437631238115985590457 140266828223428586989192843)
  ·
    refine ⟨210400242335142880483789265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140266828223428586989192843 210400242335142880483789265)
    ·
      refine ⟨157800181751357160362841949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210400242335142880483789265 157800181751357160362841949)
      ·
        refine ⟨59175068156758935136065731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157800181751357160362841949 59175068156758935136065731)
        ·
          refine ⟨88762602235138402704098597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59175068156758935136065731 88762602235138402704098597)
          ·
            refine ⟨16642987919088450507018487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88762602235138402704098597 16642987919088450507018487)
            ·
              refine ⟨24964481878632675760527731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16642987919088450507018487 24964481878632675760527731)
              ·
                refine ⟨37446722817949013640791597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24964481878632675760527731 37446722817949013640791597)
                ·
                  refine ⟨14042521056730880115296849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37446722817949013640791597 14042521056730880115296849)
                  ·
                    refine ⟨10531890792548160086472637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14042521056730880115296849 10531890792548160086472637)
                    ·
                      refine ⟨3949459047205560032427239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10531890792548160086472637 3949459047205560032427239)
                      ·
                        rfl

theorem cell23_7691544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_7691544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691544 prefixEnd_7691544 := by exact prefixLift 7691544
  have htrace : WordTrace (prefixWord ++ tailWord_7691544) baseStart_7691544 baseEnd_7691544 := by
    simpa [prefixWord, tailWord_7691544, baseEnd_7691544] using wordTrace_append hprefix tailTrace_7691544
  have hstable : (prefixWord ++ tailWord_7691544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691544).length < 2 ^ (prefixWord ++ tailWord_7691544).sum := by decide
  have hdescent : baseEnd_7691544 < baseStart_7691544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691581 : List Nat := [1, 4, 1, 5, 1, 2, 1, 8]
def baseStart_7691581 : Nat := 118140960795 + 7691581 * 2 ^ 59
def prefixEnd_7691581 : Nat := 4983230072969 + 3 ^ 40 * 7691581 * 2
def baseEnd_7691581 : Nat := 146276964666288014357947

theorem tailTrace_7691581 : CollatzResearch.WordTrace tailWord_7691581 prefixEnd_7691581 146276964666288014357947 := by
  unfold tailWord_7691581
  simp only [CollatzResearch.WordTrace]
  refine ⟨280535005947723129297482597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187023337298482086198321731 280535005947723129297482597)
  ·
    refine ⟨52600313615198086743277987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280535005947723129297482597 52600313615198086743277987)
    ·
      refine ⟨78900470422797130114916981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52600313615198086743277987 78900470422797130114916981)
      ·
        refine ⟨7396919102137230948273467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78900470422797130114916981 7396919102137230948273467)
        ·
          refine ⟨11095378653205846422410201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7396919102137230948273467 11095378653205846422410201)
          ·
            refine ⟨8321533989904384816807651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11095378653205846422410201 8321533989904384816807651)
            ·
              refine ⟨12482300984856577225211477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8321533989904384816807651 12482300984856577225211477)
              ·
                refine ⟨146276964666288014357947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12482300984856577225211477 146276964666288014357947)
                ·
                  rfl

theorem cell23_7691581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 8].length) (baseStart_7691581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691581 prefixEnd_7691581 := by exact prefixLift 7691581
  have htrace : WordTrace (prefixWord ++ tailWord_7691581) baseStart_7691581 baseEnd_7691581 := by
    simpa [prefixWord, tailWord_7691581, baseEnd_7691581] using wordTrace_append hprefix tailTrace_7691581
  have hstable : (prefixWord ++ tailWord_7691581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691581).length < 2 ^ (prefixWord ++ tailWord_7691581).sum := by decide
  have hdescent : baseEnd_7691581 < baseStart_7691581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691584 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 5, 3, 2]
def baseStart_7691584 : Nat := 118140960795 + 7691584 * 2 ^ 59
def prefixEnd_7691584 : Nat := 4983230072969 + 3 ^ 40 * 7691584 * 2
def baseEnd_7691584 : Nat := 3949479586431739875927055

theorem tailTrace_7691584 : CollatzResearch.WordTrace tailWord_7691584 prefixEnd_7691584 3949479586431739875927055 := by
  unfold tailWord_7691584
  simp only [CollatzResearch.WordTrace]
  refine ⟨140267557683356130404920903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187023410244474840539894537 140267557683356130404920903)
  ·
    refine ⟨210401336525034195607381355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140267557683356130404920903 210401336525034195607381355)
    ·
      refine ⟨315602004787551293411072033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210401336525034195607381355 315602004787551293411072033)
      ·
        refine ⟨236701503590663470058304025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315602004787551293411072033 236701503590663470058304025)
        ·
          refine ⟨177526127692997602543728019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236701503590663470058304025 177526127692997602543728019)
          ·
            refine ⟨266289191539496403815592029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177526127692997602543728019 266289191539496403815592029)
            ·
              refine ⟨99858446827311151430847011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266289191539496403815592029 99858446827311151430847011)
              ·
                refine ⟨149787670240966727146270517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99858446827311151430847011 149787670240966727146270517)
                ·
                  refine ⟨14042594085090630669962861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149787670240966727146270517 14042594085090630669962861)
                  ·
                    refine ⟨5265972781908986501236073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14042594085090630669962861 5265972781908986501236073)
                    ·
                      refine ⟨3949479586431739875927055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265972781908986501236073 3949479586431739875927055)
                      ·
                        rfl

theorem cell23_7691584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_7691584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691584 prefixEnd_7691584 := by exact prefixLift 7691584
  have htrace : WordTrace (prefixWord ++ tailWord_7691584) baseStart_7691584 baseEnd_7691584 := by
    simpa [prefixWord, tailWord_7691584, baseEnd_7691584] using wordTrace_append hprefix tailTrace_7691584
  have hstable : (prefixWord ++ tailWord_7691584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691584).length < 2 ^ (prefixWord ++ tailWord_7691584).sum := by decide
  have hdescent : baseEnd_7691584 < baseStart_7691584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691591 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_7691591 : Nat := 118140960795 + 7691591 * 2 ^ 59
def prefixEnd_7691591 : Nat := 4983230072969 + 3 ^ 40 * 7691591 * 2
def baseEnd_7691591 : Nat := 3949483180796321348539523

theorem tailTrace_7691591 : CollatzResearch.WordTrace tailWord_7691591 prefixEnd_7691591 3949483180796321348539523 := by
  unfold tailWord_7691591
  simp only [CollatzResearch.WordTrace]
  refine ⟨280535370677686901005346627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187023580451791267336897751 280535370677686901005346627)
  ·
    refine ⟨420803056016530351508019941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280535370677686901005346627 420803056016530351508019941)
    ·
      refine ⟨78900573003099440907753739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420803056016530351508019941 78900573003099440907753739)
      ·
        refine ⟨118350859504649161361630609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78900573003099440907753739 118350859504649161361630609)
        ·
          refine ⟨88763144628486871021222957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118350859504649161361630609 88763144628486871021222957)
          ·
            refine ⟨33286179235682576632958609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88763144628486871021222957 33286179235682576632958609)
            ·
              refine ⟨24964634426761932474718957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33286179235682576632958609 24964634426761932474718957)
              ·
                refine ⟨9361737910035724678019609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24964634426761932474718957 9361737910035724678019609)
                ·
                  refine ⟨7021303432526793508514707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9361737910035724678019609 7021303432526793508514707)
                  ·
                    refine ⟨10531955148790190262772061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7021303432526793508514707 10531955148790190262772061)
                    ·
                      refine ⟨3949483180796321348539523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10531955148790190262772061 3949483180796321348539523)
                      ·
                        rfl

theorem cell23_7691591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_7691591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691591 prefixEnd_7691591 := by exact prefixLift 7691591
  have htrace : WordTrace (prefixWord ++ tailWord_7691591) baseStart_7691591 baseEnd_7691591 := by
    simpa [prefixWord, tailWord_7691591, baseEnd_7691591] using wordTrace_append hprefix tailTrace_7691591
  have hstable : (prefixWord ++ tailWord_7691591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691591).length < 2 ^ (prefixWord ++ tailWord_7691591).sum := by decide
  have hdescent : baseEnd_7691591 < baseStart_7691591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691601 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 1, 3, 2]
def baseStart_7691601 : Nat := 118140960795 + 7691601 * 2 ^ 59
def prefixEnd_7691601 : Nat := 4983230072969 + 3 ^ 40 * 7691601 * 2
def baseEnd_7691601 : Nat := 3949488315602866309414477

theorem tailTrace_7691601 : CollatzResearch.WordTrace tailWord_7691601 prefixEnd_7691601 3949488315602866309414477 := by
  unfold tailWord_7691601
  simp only [CollatzResearch.WordTrace]
  refine ⟨280535735407650672713210657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187023823605100448475473771 280535735407650672713210657)
  ·
    refine ⟨210401801555738004534907993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280535735407650672713210657 210401801555738004534907993)
    ·
      refine ⟨157801351166803503401180995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210401801555738004534907993 157801351166803503401180995)
      ·
        refine ⟨236702026750205255101771493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157801351166803503401180995 236702026750205255101771493)
        ·
          refine ⟨44381630015663485331582155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236702026750205255101771493 44381630015663485331582155)
          ·
            refine ⟨66572445023495227997373233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44381630015663485331582155 66572445023495227997373233)
            ·
              refine ⟨49929333767621420998029925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66572445023495227997373233 49929333767621420998029925)
              ·
                refine ⟨9361750081429016437130611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49929333767621420998029925 9361750081429016437130611)
                ·
                  refine ⟨14042625122143524655695917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9361750081429016437130611 14042625122143524655695917)
                  ·
                    refine ⟨5265984420803821745885969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14042625122143524655695917 5265984420803821745885969)
                    ·
                      refine ⟨3949488315602866309414477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265984420803821745885969 3949488315602866309414477)
                      ·
                        rfl

theorem cell23_7691601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_7691601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691601 prefixEnd_7691601 := by exact prefixLift 7691601
  have htrace : WordTrace (prefixWord ++ tailWord_7691601) baseStart_7691601 baseEnd_7691601 := by
    simpa [prefixWord, tailWord_7691601, baseEnd_7691601] using wordTrace_append hprefix tailTrace_7691601
  have hstable : (prefixWord ++ tailWord_7691601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691601).length < 2 ^ (prefixWord ++ tailWord_7691601).sum := by decide
  have hdescent : baseEnd_7691601 < baseStart_7691601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691617 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_7691617 : Nat := 118140960795 + 7691617 * 2 ^ 59
def prefixEnd_7691617 : Nat := 4983230072969 + 3 ^ 40 * 7691617 * 2
def baseEnd_7691617 : Nat := 3949496531293338246814403

theorem tailTrace_7691617 : CollatzResearch.WordTrace tailWord_7691617 prefixEnd_7691617 3949496531293338246814403 := by
  unfold tailWord_7691617
  simp only [CollatzResearch.WordTrace]
  refine ⟨280536318975592707445793105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187024212650395138297195403 280536318975592707445793105)
  ·
    refine ⟨210402239231694530584344829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280536318975592707445793105 210402239231694530584344829)
    ·
      refine ⟨78900839711885448969129311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210402239231694530584344829 78900839711885448969129311)
      ·
        refine ⟨118351259567828173453693967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78900839711885448969129311 118351259567828173453693967)
        ·
          refine ⟨177526889351742260180540951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118351259567828173453693967 177526889351742260180540951)
          ·
            refine ⟨266290334027613390270811427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177526889351742260180540951 266290334027613390270811427)
            ·
              refine ⟨399435501041420085406217141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266290334027613390270811427 399435501041420085406217141)
              ·
                refine ⟨37447078222633133006832857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399435501041420085406217141 37447078222633133006832857)
                ·
                  refine ⟨28085308666974849755124643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37447078222633133006832857 28085308666974849755124643)
                  ·
                    refine ⟨42127963000462274632686965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28085308666974849755124643 42127963000462274632686965)
                    ·
                      refine ⟨3949496531293338246814403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42127963000462274632686965 3949496531293338246814403)
                      ·
                        rfl

theorem cell23_7691617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_7691617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691617 prefixEnd_7691617 := by exact prefixLift 7691617
  have htrace : WordTrace (prefixWord ++ tailWord_7691617) baseStart_7691617 baseEnd_7691617 := by
    simpa [prefixWord, tailWord_7691617, baseEnd_7691617] using wordTrace_append hprefix tailTrace_7691617
  have hstable : (prefixWord ++ tailWord_7691617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691617).length < 2 ^ (prefixWord ++ tailWord_7691617).sum := by decide
  have hdescent : baseEnd_7691617 < baseStart_7691617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691618 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_7691618 : Nat := 118140960795 + 7691618 * 2 ^ 59
def prefixEnd_7691618 : Nat := 4983230072969 + 3 ^ 40 * 7691618 * 2
def baseEnd_7691618 : Nat := 3949497044773992742901899

theorem tailTrace_7691618 : CollatzResearch.WordTrace tailWord_7691618 prefixEnd_7691618 3949497044773992742901899 := by
  unfold tailWord_7691618
  simp only [CollatzResearch.WordTrace]
  refine ⟨70134088862147271154144877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187024236965726056411053005 70134088862147271154144877)
  ·
    refine ⟨26300283323305226682804329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70134088862147271154144877 26300283323305226682804329)
    ·
      refine ⟨19725212492478920012103247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26300283323305226682804329 19725212492478920012103247)
      ·
        refine ⟨29587818738718380018154871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19725212492478920012103247 29587818738718380018154871)
        ·
          refine ⟨44381728108077570027232307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29587818738718380018154871 44381728108077570027232307)
          ·
            refine ⟨66572592162116355040848461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44381728108077570027232307 66572592162116355040848461)
            ·
              refine ⟨24964722060793633140318173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66572592162116355040848461 24964722060793633140318173)
              ·
                refine ⟨9361770772797612427619315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24964722060793633140318173 9361770772797612427619315)
                ·
                  refine ⟨14042656159196418641428973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9361770772797612427619315 14042656159196418641428973)
                  ·
                    refine ⟨5265996059698656990535865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14042656159196418641428973 5265996059698656990535865)
                    ·
                      refine ⟨3949497044773992742901899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5265996059698656990535865 3949497044773992742901899)
                      ·
                        rfl

theorem cell23_7691618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_7691618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691618 prefixEnd_7691618 := by exact prefixLift 7691618
  have htrace : WordTrace (prefixWord ++ tailWord_7691618) baseStart_7691618 baseEnd_7691618 := by
    simpa [prefixWord, tailWord_7691618, baseEnd_7691618] using wordTrace_append hprefix tailTrace_7691618
  have hstable : (prefixWord ++ tailWord_7691618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691618).length < 2 ^ (prefixWord ++ tailWord_7691618).sum := by decide
  have hdescent : baseEnd_7691618 < baseStart_7691618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691631 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 4, 2, 2]
def baseStart_7691631 : Nat := 118140960795 + 7691631 * 2 ^ 59
def prefixEnd_7691631 : Nat := 4983230072969 + 3 ^ 40 * 7691631 * 2
def baseEnd_7691631 : Nat := 3949503720022501192039339

theorem tailTrace_7691631 : CollatzResearch.WordTrace tailWord_7691631 prefixEnd_7691631 3949503720022501192039339 := by
  unfold tailWord_7691631
  simp only [CollatzResearch.WordTrace]
  refine ⟨280536829597541987836802747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187024553065027991891201831 280536829597541987836802747)
  ·
    refine ⟨420805244396312981755204121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280536829597541987836802747 420805244396312981755204121)
    ·
      refine ⟨315603933297234736316403091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420805244396312981755204121 315603933297234736316403091)
      ·
        refine ⟨473405899945852104474604637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315603933297234736316403091 473405899945852104474604637)
        ·
          refine ⟨177527212479694539177976739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473405899945852104474604637 177527212479694539177976739)
          ·
            refine ⟨266290818719541808766965109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177527212479694539177976739 266290818719541808766965109)
            ·
              refine ⟨24964764254957044571902979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266290818719541808766965109 24964764254957044571902979)
              ·
                refine ⟨37447146382435566857854469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24964764254957044571902979 37447146382435566857854469)
                ·
                  refine ⟨7021339946706668785847713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37447146382435566857854469 7021339946706668785847713)
                  ·
                    refine ⟨5266004960030001589385785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7021339946706668785847713 5266004960030001589385785)
                    ·
                      refine ⟨3949503720022501192039339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266004960030001589385785 3949503720022501192039339)
                      ·
                        rfl

theorem cell23_7691631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 2, 2].length) (baseStart_7691631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691631 prefixEnd_7691631 := by exact prefixLift 7691631
  have htrace : WordTrace (prefixWord ++ tailWord_7691631) baseStart_7691631 baseEnd_7691631 := by
    simpa [prefixWord, tailWord_7691631, baseEnd_7691631] using wordTrace_append hprefix tailTrace_7691631
  have hstable : (prefixWord ++ tailWord_7691631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691631).length < 2 ^ (prefixWord ++ tailWord_7691631).sum := by decide
  have hdescent : baseEnd_7691631 < baseStart_7691631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691667 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 8, 5]
def baseStart_7691667 : Nat := 118140960795 + 7691667 * 2 ^ 59
def prefixEnd_7691667 : Nat := 4983230072969 + 3 ^ 40 * 7691667 * 2
def baseEnd_7691667 : Nat := 1316507401775354350396391

theorem tailTrace_7691667 : CollatzResearch.WordTrace tailWord_7691667 prefixEnd_7691667 1316507401775354350396391 := by
  unfold tailWord_7691667
  simp only [CollatzResearch.WordTrace]
  refine ⟨280538142625411565985113255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187025428416941043990075503 280538142625411565985113255)
  ·
    refine ⟨420807213938117348977669883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280538142625411565985113255 420807213938117348977669883)
    ·
      refine ⟨631210820907176023466504825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420807213938117348977669883 631210820907176023466504825)
      ·
        refine ⟨473408115680382017599878619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631210820907176023466504825 473408115680382017599878619)
        ·
          refine ⟨710112173520573026399817929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473408115680382017599878619 710112173520573026399817929)
          ·
            refine ⟨532584130140429769799863447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710112173520573026399817929 532584130140429769799863447)
            ·
              refine ⟨798876195210644654699795171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532584130140429769799863447 798876195210644654699795171)
              ·
                refine ⟨1198314292815966982049692757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 798876195210644654699795171 1198314292815966982049692757)
                ·
                  refine ⟨14042745618937113070894837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1198314292815966982049692757 14042745618937113070894837)
                  ·
                    refine ⟨1316507401775354350396391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14042745618937113070894837 1316507401775354350396391)
                    ·
                      rfl

theorem cell23_7691667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 5].length) (baseStart_7691667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691667 prefixEnd_7691667 := by exact prefixLift 7691667
  have htrace : WordTrace (prefixWord ++ tailWord_7691667) baseStart_7691667 baseEnd_7691667 := by
    simpa [prefixWord, tailWord_7691667, baseEnd_7691667] using wordTrace_append hprefix tailTrace_7691667
  have hstable : (prefixWord ++ tailWord_7691667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691667).length < 2 ^ (prefixWord ++ tailWord_7691667).sum := by decide
  have hdescent : baseEnd_7691667 < baseStart_7691667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691688 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 7]
def baseStart_7691688 : Nat := 118140960795 + 7691688 * 2 ^ 59
def prefixEnd_7691688 : Nat := 4983230072969 + 3 ^ 40 * 7691688 * 2
def baseEnd_7691688 : Nat := 438836998713311941002953

theorem tailTrace_7691688 : CollatzResearch.WordTrace tailWord_7691688 prefixEnd_7691688 438836998713311941002953 := by
  unfold tailWord_7691688
  simp only [CollatzResearch.WordTrace]
  refine ⟨140269454279167743285813859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187025939038890324381085145 140269454279167743285813859)
  ·
    refine ⟨210404181418751614928720789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140269454279167743285813859 210404181418751614928720789)
    ·
      refine ⟨9862696004003981949783787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210404181418751614928720789 9862696004003981949783787)
      ·
        refine ⟨14794044006005972924675681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9862696004003981949783787 14794044006005972924675681)
        ·
          refine ⟨11095533004504479693506761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14794044006005972924675681 11095533004504479693506761)
          ·
            refine ⟨8321649753378359770130071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11095533004504479693506761 8321649753378359770130071)
            ·
              refine ⟨12482474630067539655195107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8321649753378359770130071 12482474630067539655195107)
              ·
                refine ⟨18723711945101309482792661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12482474630067539655195107 18723711945101309482792661)
                ·
                  refine ⟨438836998713311941002953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18723711945101309482792661 438836998713311941002953)
                  ·
                    rfl

theorem cell23_7691688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 7].length) (baseStart_7691688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691688 prefixEnd_7691688 := by exact prefixLift 7691688
  have htrace : WordTrace (prefixWord ++ tailWord_7691688) baseStart_7691688 baseEnd_7691688 := by
    simpa [prefixWord, tailWord_7691688, baseEnd_7691688] using wordTrace_append hprefix tailTrace_7691688
  have hstable : (prefixWord ++ tailWord_7691688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691688).length < 2 ^ (prefixWord ++ tailWord_7691688).sum := by decide
  have hdescent : baseEnd_7691688 < baseStart_7691688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691727 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 10]
def baseStart_7691727 : Nat := 118140960795 + 7691727 * 2 ^ 59
def prefixEnd_7691727 : Nat := 4983230072969 + 3 ^ 40 * 7691727 * 2
def baseEnd_7691727 : Nat := 438839223796148090715433

theorem tailTrace_7691727 : CollatzResearch.WordTrace tailWord_7691727 prefixEnd_7691727 438839223796148090715433 := by
  unfold tailWord_7691727
  simp only [CollatzResearch.WordTrace]
  refine ⟨280540331005194196232297435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187026887336796130821531623 280540331005194196232297435)
  ·
    refine ⟨420810496507791294348446153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280540331005194196232297435 420810496507791294348446153)
    ·
      refine ⟨315607872380843470761334615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420810496507791294348446153 315607872380843470761334615)
      ·
        refine ⟨473411808571265206142001923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315607872380843470761334615 473411808571265206142001923)
        ·
          refine ⟨710117712856897809213002885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473411808571265206142001923 710117712856897809213002885)
          ·
            refine ⟨133147071160668339227438041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 710117712856897809213002885 133147071160668339227438041)
            ·
              refine ⟨99860303370501254420578531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133147071160668339227438041 99860303370501254420578531)
              ·
                refine ⟨149790455055751881630867797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99860303370501254420578531 149790455055751881630867797)
                ·
                  refine ⟨438839223796148090715433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149790455055751881630867797 438839223796148090715433)
                  ·
                    rfl

theorem cell23_7691727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 10].length) (baseStart_7691727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691727 prefixEnd_7691727 := by exact prefixLift 7691727
  have htrace : WordTrace (prefixWord ++ tailWord_7691727) baseStart_7691727 baseEnd_7691727 := by
    simpa [prefixWord, tailWord_7691727, baseEnd_7691727] using wordTrace_append hprefix tailTrace_7691727
  have hstable : (prefixWord ++ tailWord_7691727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691727).length < 2 ^ (prefixWord ++ tailWord_7691727).sum := by decide
  have hdescent : baseEnd_7691727 < baseStart_7691727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691771 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 3]
def baseStart_7691771 : Nat := 118140960795 + 7691771 * 2 ^ 59
def prefixEnd_7691771 : Nat := 4983230072969 + 3 ^ 40 * 7691771 * 2
def baseEnd_7691771 : Nat := 3949575607314130644288695

theorem tailTrace_7691771 : CollatzResearch.WordTrace tailWord_7691771 prefixEnd_7691771 3949575607314130644288695 := by
  unfold tailWord_7691771
  simp only [CollatzResearch.WordTrace]
  refine ⟨280541935817034791746899167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187027957211356527831266111 280541935817034791746899167)
  ·
    refine ⟨420812903725552187620348751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280541935817034791746899167 420812903725552187620348751)
    ·
      refine ⟨631219355588328281430523127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420812903725552187620348751 631219355588328281430523127)
      ·
        refine ⟨946829033382492422145784691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631219355588328281430523127 946829033382492422145784691)
        ·
          refine ⟨1420243550073738633218677037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 946829033382492422145784691 1420243550073738633218677037)
          ·
            refine ⟨532591331277651987457003889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1420243550073738633218677037 532591331277651987457003889)
            ·
              refine ⟨399443498458238990592752917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532591331277651987457003889 399443498458238990592752917)
              ·
                refine ⟨18723913990229952684035293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 399443498458238990592752917 18723913990229952684035293)
                ·
                  refine ⟨7021467746336232256513235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18723913990229952684035293 7021467746336232256513235)
                  ·
                    refine ⟨10532201619504348384769853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7021467746336232256513235 10532201619504348384769853)
                    ·
                      refine ⟨3949575607314130644288695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10532201619504348384769853 3949575607314130644288695)
                      ·
                        rfl

theorem cell23_7691771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 3].length) (baseStart_7691771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691771 prefixEnd_7691771 := by exact prefixLift 7691771
  have htrace : WordTrace (prefixWord ++ tailWord_7691771) baseStart_7691771 baseEnd_7691771 := by
    simpa [prefixWord, tailWord_7691771, baseEnd_7691771] using wordTrace_append hprefix tailTrace_7691771
  have hstable : (prefixWord ++ tailWord_7691771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691771).length < 2 ^ (prefixWord ++ tailWord_7691771).sum := by decide
  have hdescent : baseEnd_7691771 < baseStart_7691771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691805 : List Nat := [1, 4, 2, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_7691805 : Nat := 118140960795 + 7691805 * 2 ^ 59
def prefixEnd_7691805 : Nat := 4983230072969 + 3 ^ 40 * 7691805 * 2
def baseEnd_7691805 : Nat := 3949593065656383511263539

theorem tailTrace_7691805 : CollatzResearch.WordTrace tailWord_7691805 prefixEnd_7691805 3949593065656383511263539 := by
  unfold tailWord_7691805
  simp only [CollatzResearch.WordTrace]
  refine ⟨280543175898911615553636869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187028783932607743702424579 280543175898911615553636869)
  ·
    refine ⟨52601845481045927916306913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280543175898911615553636869 52601845481045927916306913)
    ·
      refine ⟨39451384110784445937230185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52601845481045927916306913 39451384110784445937230185)
      ·
        refine ⟨29588538083088334452922639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39451384110784445937230185 29588538083088334452922639)
        ·
          refine ⟨44382807124632501679383959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29588538083088334452922639 44382807124632501679383959)
          ·
            refine ⟨66574210686948752519075939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44382807124632501679383959 66574210686948752519075939)
            ·
              refine ⟨99861316030423128778613909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66574210686948752519075939 99861316030423128778613909)
              ·
                refine ⟨4680999188926084161497527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99861316030423128778613909 4680999188926084161497527)
                ·
                  refine ⟨7021498783389126242246291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4680999188926084161497527 7021498783389126242246291)
                  ·
                    refine ⟨10532248175083689363369437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7021498783389126242246291 10532248175083689363369437)
                    ·
                      refine ⟨3949593065656383511263539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10532248175083689363369437 3949593065656383511263539)
                      ·
                        rfl

theorem cell23_7691805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_7691805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691805 prefixEnd_7691805 := by exact prefixLift 7691805
  have htrace : WordTrace (prefixWord ++ tailWord_7691805) baseStart_7691805 baseEnd_7691805 := by
    simpa [prefixWord, tailWord_7691805, baseEnd_7691805] using wordTrace_append hprefix tailTrace_7691805
  have hstable : (prefixWord ++ tailWord_7691805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691805).length < 2 ^ (prefixWord ++ tailWord_7691805).sum := by decide
  have hdescent : baseEnd_7691805 < baseStart_7691805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691834 : List Nat := [3, 1, 1, 1, 3, 2, 3, 9]
def baseStart_7691834 : Nat := 118140960795 + 7691834 * 2 ^ 59
def prefixEnd_7691834 : Nat := 4983230072969 + 3 ^ 40 * 7691834 * 2
def baseEnd_7691834 : Nat := 146281776170198662881515

theorem tailTrace_7691834 : CollatzResearch.WordTrace tailWord_7691834 prefixEnd_7691834 146281776170198662881515 := by
  unfold tailWord_7691834
  simp only [CollatzResearch.WordTrace]
  refine ⟨70136058403951638376610639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187029489077204369004295037 70136058403951638376610639)
  ·
    refine ⟨105204087605927457564915959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70136058403951638376610639 105204087605927457564915959)
    ·
      refine ⟨157806131408891186347373939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105204087605927457564915959 157806131408891186347373939)
      ·
        refine ⟨236709197113336779521060909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157806131408891186347373939 236709197113336779521060909)
        ·
          refine ⟨88765948917501292320397841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236709197113336779521060909 88765948917501292320397841)
          ·
            refine ⟨66574461688125969240298381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88765948917501292320397841 66574461688125969240298381)
            ·
              refine ⟨24965423133047238465111893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66574461688125969240298381 24965423133047238465111893)
              ·
                refine ⟨146281776170198662881515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24965423133047238465111893 146281776170198662881515)
                ·
                  rfl

theorem cell23_7691834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 9].length) (baseStart_7691834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691834 prefixEnd_7691834 := by exact prefixLift 7691834
  have htrace : WordTrace (prefixWord ++ tailWord_7691834) baseStart_7691834 baseEnd_7691834 := by
    simpa [prefixWord, tailWord_7691834, baseEnd_7691834] using wordTrace_append hprefix tailTrace_7691834
  have hstable : (prefixWord ++ tailWord_7691834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691834).length < 2 ^ (prefixWord ++ tailWord_7691834).sum := by decide
  have hdescent : baseEnd_7691834 < baseStart_7691834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691841 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_7691841 : Nat := 118140960795 + 7691841 * 2 ^ 59
def prefixEnd_7691841 : Nat := 4983230072969 + 3 ^ 40 * 7691841 * 2
def baseEnd_7691841 : Nat := 3949611550959945370413373

theorem tailTrace_7691841 : CollatzResearch.WordTrace tailWord_7691841 prefixEnd_7691841 3949611550959945370413373 := by
  unfold tailWord_7691841
  simp only [CollatzResearch.WordTrace]
  refine ⟨280544488926781193701947377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187029659284520795801298251 280544488926781193701947377)
  ·
    refine ⟨210408366695085895276460533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280544488926781193701947377 210408366695085895276460533)
    ·
      refine ⟨19725784377664302682168175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210408366695085895276460533 19725784377664302682168175)
      ·
        refine ⟨29588676566496454023252263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19725784377664302682168175 29588676566496454023252263)
        ·
          refine ⟨44383014849744681034878395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29588676566496454023252263 44383014849744681034878395)
          ·
            refine ⟨66574522274617021552317593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44383014849744681034878395 66574522274617021552317593)
            ·
              refine ⟨49930891705962766164238195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66574522274617021552317593 49930891705962766164238195)
              ·
                refine ⟨74896337558944149246357293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49930891705962766164238195 74896337558944149246357293)
                ·
                  refine ⟨28086126584604055967383985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74896337558944149246357293 28086126584604055967383985)
                  ·
                    refine ⟨21064594938453041975537989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28086126584604055967383985 21064594938453041975537989)
                    ·
                      refine ⟨3949611550959945370413373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21064594938453041975537989 3949611550959945370413373)
                      ·
                        rfl

theorem cell23_7691841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_7691841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691841 prefixEnd_7691841 := by exact prefixLift 7691841
  have htrace : WordTrace (prefixWord ++ tailWord_7691841) baseStart_7691841 baseEnd_7691841 := by
    simpa [prefixWord, tailWord_7691841, baseEnd_7691841] using wordTrace_append hprefix tailTrace_7691841
  have hstable : (prefixWord ++ tailWord_7691841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691841).length < 2 ^ (prefixWord ++ tailWord_7691841).sum := by decide
  have hdescent : baseEnd_7691841 < baseStart_7691841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691864 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 2, 7]
def baseStart_7691864 : Nat := 118140960795 + 7691864 * 2 ^ 59
def prefixEnd_7691864 : Nat := 4983230072969 + 3 ^ 40 * 7691864 * 2
def baseEnd_7691864 : Nat := 1316541120338332926808589

theorem tailTrace_7691864 : CollatzResearch.WordTrace tailWord_7691864 prefixEnd_7691864 1316541120338332926808589 := by
  unfold tailWord_7691864
  simp only [CollatzResearch.WordTrace]
  refine ⟨140272663902848934315017323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187030218537131912420023097 140272663902848934315017323)
  ·
    refine ⟨210408995854273401472525985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140272663902848934315017323 210408995854273401472525985)
    ·
      refine ⟨157806746890705051104394489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210408995854273401472525985 157806746890705051104394489)
      ·
        refine ⟨118355060168028788328295867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157806746890705051104394489 118355060168028788328295867)
        ·
          refine ⟨177532590252043182492443801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118355060168028788328295867 177532590252043182492443801)
          ·
            refine ⟨133149442689032386869332851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177532590252043182492443801 133149442689032386869332851)
            ·
              refine ⟨199724164033548580303999277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133149442689032386869332851 199724164033548580303999277)
              ·
                refine ⟨74896561512580717613999729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199724164033548580303999277 74896561512580717613999729)
                ·
                  refine ⟨56172421134435538210499797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74896561512580717613999729 56172421134435538210499797)
                  ·
                    refine ⟨1316541120338332926808589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56172421134435538210499797 1316541120338332926808589)
                    ·
                      rfl

theorem cell23_7691864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_7691864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691864 prefixEnd_7691864 := by exact prefixLift 7691864
  have htrace : WordTrace (prefixWord ++ tailWord_7691864) baseStart_7691864 baseEnd_7691864 := by
    simpa [prefixWord, tailWord_7691864, baseEnd_7691864] using wordTrace_append hprefix tailTrace_7691864
  have hstable : (prefixWord ++ tailWord_7691864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691864).length < 2 ^ (prefixWord ++ tailWord_7691864).sum := by decide
  have hdescent : baseEnd_7691864 < baseStart_7691864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691871 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 9, 2]
def baseStart_7691871 : Nat := 118140960795 + 7691871 * 2 ^ 59
def prefixEnd_7691871 : Nat := 4983230072969 + 3 ^ 40 * 7691871 * 2
def baseEnd_7691871 : Nat := 3949626955379580253038235

theorem tailTrace_7691871 : CollatzResearch.WordTrace tailWord_7691871 prefixEnd_7691871 3949626955379580253038235 := by
  unfold tailWord_7691871
  simp only [CollatzResearch.WordTrace]
  refine ⟨280545583116672508825539467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187030388744448339217026311 280545583116672508825539467)
  ·
    refine ⟨420818374675008763238309201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280545583116672508825539467 420818374675008763238309201)
    ·
      refine ⟨315613781006256572428731901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420818374675008763238309201 315613781006256572428731901)
      ·
        refine ⟨118355167877346214660774463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315613781006256572428731901 118355167877346214660774463)
        ·
          refine ⟨177532751816019321991161695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118355167877346214660774463 177532751816019321991161695)
          ·
            refine ⟨266299127724028982986742543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177532751816019321991161695 266299127724028982986742543)
            ·
              refine ⟨399448691586043474480113815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266299127724028982986742543 399448691586043474480113815)
              ·
                refine ⟨599173037379065211720170723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399448691586043474480113815 599173037379065211720170723)
                ·
                  refine ⟨898759556068597817580256085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599173037379065211720170723 898759556068597817580256085)
                  ·
                    refine ⟨5266169273839440337384313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 898759556068597817580256085 5266169273839440337384313)
                    ·
                      refine ⟨3949626955379580253038235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266169273839440337384313 3949626955379580253038235)
                      ·
                        rfl

theorem cell23_7691871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_7691871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691871 prefixEnd_7691871 := by exact prefixLift 7691871
  have htrace : WordTrace (prefixWord ++ tailWord_7691871) baseStart_7691871 baseEnd_7691871 := by
    simpa [prefixWord, tailWord_7691871, baseEnd_7691871] using wordTrace_append hprefix tailTrace_7691871
  have hstable : (prefixWord ++ tailWord_7691871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691871).length < 2 ^ (prefixWord ++ tailWord_7691871).sum := by decide
  have hdescent : baseEnd_7691871 < baseStart_7691871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691884 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_7691884 : Nat := 118140960795 + 7691884 * 2 ^ 59
def prefixEnd_7691884 : Nat := 4983230072969 + 3 ^ 40 * 7691884 * 2
def baseEnd_7691884 : Nat := 3949633630628088702175675

theorem tailTrace_7691884 : CollatzResearch.WordTrace tailWord_7691884 prefixEnd_7691884 3949633630628088702175675 := by
  unfold tailWord_7691884
  simp only [CollatzResearch.WordTrace]
  refine ⟨140273028632812706022881353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187030704843750274697175137 140273028632812706022881353)
  ·
    refine ⟨105204771474609529517161015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140273028632812706022881353 105204771474609529517161015)
    ·
      refine ⟨157807157211914294275741523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105204771474609529517161015 157807157211914294275741523)
      ·
        refine ⟨236710735817871441413612285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157807157211914294275741523 236710735817871441413612285)
        ·
          refine ⟨88766525931701790530104607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236710735817871441413612285 88766525931701790530104607)
          ·
            refine ⟨133149788897552685795156911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88766525931701790530104607 133149788897552685795156911)
            ·
              refine ⟨199724683346329028692735367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133149788897552685795156911 199724683346329028692735367)
              ·
                refine ⟨299587025019493543039103051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199724683346329028692735367 299587025019493543039103051)
                ·
                  refine ⟨449380537529240314558654577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299587025019493543039103051 449380537529240314558654577)
                  ·
                    refine ⟨337035403146930235918990933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 449380537529240314558654577 337035403146930235918990933)
                    ·
                      refine ⟨3949633630628088702175675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 337035403146930235918990933 3949633630628088702175675)
                      ·
                        rfl

theorem cell23_7691884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_7691884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691884 prefixEnd_7691884 := by exact prefixLift 7691884
  have htrace : WordTrace (prefixWord ++ tailWord_7691884) baseStart_7691884 baseEnd_7691884 := by
    simpa [prefixWord, tailWord_7691884, baseEnd_7691884] using wordTrace_append hprefix tailTrace_7691884
  have hstable : (prefixWord ++ tailWord_7691884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691884).length < 2 ^ (prefixWord ++ tailWord_7691884).sum := by decide
  have hdescent : baseEnd_7691884 < baseStart_7691884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691951 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 3]
def baseStart_7691951 : Nat := 118140960795 + 7691951 * 2 ^ 59
def prefixEnd_7691951 : Nat := 4983230072969 + 3 ^ 40 * 7691951 * 2
def baseEnd_7691951 : Nat := 3949668033831939940037867

theorem tailTrace_7691951 : CollatzResearch.WordTrace tailWord_7691951 prefixEnd_7691951 3949668033831939940037867 := by
  unfold tailWord_7691951
  simp only [CollatzResearch.WordTrace]
  refine ⟨280548500956382682488451707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187032333970921788325634471 280548500956382682488451707)
  ·
    refine ⟨420822751434574023732677561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280548500956382682488451707 420822751434574023732677561)
    ·
      refine ⟨315617063575930517799508171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420822751434574023732677561 315617063575930517799508171)
      ·
        refine ⟨473425595363895776699262257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315617063575930517799508171 473425595363895776699262257)
        ·
          refine ⟨355069196522921832524446693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473425595363895776699262257 355069196522921832524446693)
          ·
            refine ⟨66575474348047843598333755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355069196522921832524446693 66575474348047843598333755)
            ·
              refine ⟨99863211522071765397500633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66575474348047843598333755 99863211522071765397500633)
              ·
                refine ⟨74897408641553824048125475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99863211522071765397500633 74897408641553824048125475)
                ·
                  refine ⟨112346112962330736072188213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74897408641553824048125475 112346112962330736072188213)
                  ·
                    refine ⟨10532448090218506506767645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112346112962330736072188213 10532448090218506506767645)
                    ·
                      refine ⟨3949668033831939940037867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10532448090218506506767645 3949668033831939940037867)
                      ·
                        rfl

theorem cell23_7691951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_7691951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691951 prefixEnd_7691951 := by exact prefixLift 7691951
  have htrace : WordTrace (prefixWord ++ tailWord_7691951) baseStart_7691951 baseEnd_7691951 := by
    simpa [prefixWord, tailWord_7691951, baseEnd_7691951] using wordTrace_append hprefix tailTrace_7691951
  have hstable : (prefixWord ++ tailWord_7691951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691951).length < 2 ^ (prefixWord ++ tailWord_7691951).sum := by decide
  have hdescent : baseEnd_7691951 < baseStart_7691951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691988 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_7691988 : Nat := 118140960795 + 7691988 * 2 ^ 59
def prefixEnd_7691988 : Nat := 4983230072969 + 3 ^ 40 * 7691988 * 2
def baseEnd_7691988 : Nat := 1316562344205385431758399

theorem tailTrace_7691988 : CollatzResearch.WordTrace tailWord_7691988 prefixEnd_7691988 1316562344205385431758399 := by
  unfold tailWord_7691988
  simp only [CollatzResearch.WordTrace]
  refine ⟨140274925228624318903774309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187033233638165758538365745 140274925228624318903774309)
  ·
    refine ⟨26301548480367059794457683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140274925228624318903774309 26301548480367059794457683)
    ·
      refine ⟨39452322720550589691686525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26301548480367059794457683 39452322720550589691686525)
      ·
        refine ⟨14794621020206471134382447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39452322720550589691686525 14794621020206471134382447)
        ·
          refine ⟨22191931530309706701573671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14794621020206471134382447 22191931530309706701573671)
          ·
            refine ⟨33287897295464560052360507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22191931530309706701573671 33287897295464560052360507)
            ·
              refine ⟨49931845943196840078540761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33287897295464560052360507 49931845943196840078540761)
              ·
                refine ⟨37448884457397630058905571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49931845943196840078540761 37448884457397630058905571)
                ·
                  refine ⟨56173326686096445088358357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37448884457397630058905571 56173326686096445088358357)
                  ·
                    refine ⟨1316562344205385431758399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56173326686096445088358357 1316562344205385431758399)
                    ·
                      rfl

theorem cell23_7691988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_7691988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691988 prefixEnd_7691988 := by exact prefixLift 7691988
  have htrace : WordTrace (prefixWord ++ tailWord_7691988) baseStart_7691988 baseEnd_7691988 := by
    simpa [prefixWord, tailWord_7691988, baseEnd_7691988] using wordTrace_append hprefix tailTrace_7691988
  have hstable : (prefixWord ++ tailWord_7691988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691988).length < 2 ^ (prefixWord ++ tailWord_7691988).sum := by decide
  have hdescent : baseEnd_7691988 < baseStart_7691988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7691991 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_7691991 : Nat := 118140960795 + 7691991 * 2 ^ 59
def prefixEnd_7691991 : Nat := 4983230072969 + 3 ^ 40 * 7691991 * 2
def baseEnd_7691991 : Nat := 3949688573058119783537683

theorem tailTrace_7691991 : CollatzResearch.WordTrace tailWord_7691991 prefixEnd_7691991 3949688573058119783537683 := by
  unfold tailWord_7691991
  simp only [CollatzResearch.WordTrace]
  refine ⟨280549959876237769319907827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187033306584158512879938551 280549959876237769319907827)
  ·
    refine ⟨420824939814356653979861741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280549959876237769319907827 420824939814356653979861741)
    ·
      refine ⟨157809352430383745242448153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420824939814356653979861741 157809352430383745242448153)
      ·
        refine ⟨118357014322787808931836115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157809352430383745242448153 118357014322787808931836115)
        ·
          refine ⟨177535521484181713397754173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118357014322787808931836115 177535521484181713397754173)
          ·
            refine ⟨66575820556568142524157815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177535521484181713397754173 66575820556568142524157815)
            ·
              refine ⟨99863730834852213786236723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66575820556568142524157815 99863730834852213786236723)
              ·
                refine ⟨149795596252278320679355085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99863730834852213786236723 149795596252278320679355085)
                ·
                  refine ⟨56173348594604370254758157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149795596252278320679355085 56173348594604370254758157)
                  ·
                    refine ⟨21065005722976638845534309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56173348594604370254758157 21065005722976638845534309)
                    ·
                      refine ⟨3949688573058119783537683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21065005722976638845534309 3949688573058119783537683)
                      ·
                        rfl

theorem cell23_7691991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_7691991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7691991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7691991 prefixEnd_7691991 := by exact prefixLift 7691991
  have htrace : WordTrace (prefixWord ++ tailWord_7691991) baseStart_7691991 baseEnd_7691991 := by
    simpa [prefixWord, tailWord_7691991, baseEnd_7691991] using wordTrace_append hprefix tailTrace_7691991
  have hstable : (prefixWord ++ tailWord_7691991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7691991).length < 2 ^ (prefixWord ++ tailWord_7691991).sum := by decide
  have hdescent : baseEnd_7691991 < baseStart_7691991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7691991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692008 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7692008 : Nat := 118140960795 + 7692008 * 2 ^ 59
def prefixEnd_7692008 : Nat := 4983230072969 + 3 ^ 40 * 7692008 * 2
def baseEnd_7692008 : Nat := 3949697302229246217025105

theorem tailTrace_7692008 : CollatzResearch.WordTrace tailWord_7692008 prefixEnd_7692008 3949697302229246217025105 := by
  unfold tailWord_7692008
  simp only [CollatzResearch.WordTrace]
  refine ⟨140275289958588090611638339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187033719944784120815517785 140275289958588090611638339)
  ·
    refine ⟨210412934937882135917457509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140275289958588090611638339 210412934937882135917457509)
    ·
      refine ⟨39452425300852900484523283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210412934937882135917457509 39452425300852900484523283)
      ·
        refine ⟨59178637951279350726784925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39452425300852900484523283 59178637951279350726784925)
        ·
          refine ⟨22191989231729756522544347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59178637951279350726784925 22191989231729756522544347)
          ·
            refine ⟨33287983847594634783816521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22191989231729756522544347 33287983847594634783816521)
            ·
              refine ⟨24965987885695976087862391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33287983847594634783816521 24965987885695976087862391)
              ·
                refine ⟨37448981828543964131793587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24965987885695976087862391 37448981828543964131793587)
                ·
                  refine ⟨56173472742815946197690381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37448981828543964131793587 56173472742815946197690381)
                  ·
                    refine ⟨21065052278555979824133893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56173472742815946197690381 21065052278555979824133893)
                    ·
                      refine ⟨3949697302229246217025105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21065052278555979824133893 3949697302229246217025105)
                      ·
                        rfl

theorem cell23_7692008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7692008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692008 prefixEnd_7692008 := by exact prefixLift 7692008
  have htrace : WordTrace (prefixWord ++ tailWord_7692008) baseStart_7692008 baseEnd_7692008 := by
    simpa [prefixWord, tailWord_7692008, baseEnd_7692008] using wordTrace_append hprefix tailTrace_7692008
  have hstable : (prefixWord ++ tailWord_7692008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692008).length < 2 ^ (prefixWord ++ tailWord_7692008).sum := by decide
  have hdescent : baseEnd_7692008 < baseStart_7692008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692031 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 8]
def baseStart_7692031 : Nat := 118140960795 + 7692031 * 2 ^ 59
def prefixEnd_7692031 : Nat := 4983230072969 + 3 ^ 40 * 7692031 * 2
def baseEnd_7692031 : Nat := 438856568031588847448611

theorem tailTrace_7692031 : CollatzResearch.WordTrace tailWord_7692031 prefixEnd_7692031 438856568031588847448611 := by
  unfold tailWord_7692031
  simp only [CollatzResearch.WordTrace]
  refine ⟨280551418796092856151363947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187034279197395237434242631 280551418796092856151363947)
  ·
    refine ⟨420827128194139284227045921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280551418796092856151363947 420827128194139284227045921)
    ·
      refine ⟨315620346145604463170284441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420827128194139284227045921 315620346145604463170284441)
      ·
        refine ⟨236715259609203347377713331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315620346145604463170284441 236715259609203347377713331)
        ·
          refine ⟨355072889413805021066569997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236715259609203347377713331 355072889413805021066569997)
          ·
            refine ⟨133152333530176882899963749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355072889413805021066569997 133152333530176882899963749)
            ·
              refine ⟨24966062536908165543743203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133152333530176882899963749 24966062536908165543743203)
              ·
                refine ⟨37449093805362248315614805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24966062536908165543743203 37449093805362248315614805)
                ·
                  refine ⟨438856568031588847448611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37449093805362248315614805 438856568031588847448611)
                  ·
                    rfl

theorem cell23_7692031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 8].length) (baseStart_7692031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692031 prefixEnd_7692031 := by exact prefixLift 7692031
  have htrace : WordTrace (prefixWord ++ tailWord_7692031) baseStart_7692031 baseEnd_7692031 := by
    simpa [prefixWord, tailWord_7692031, baseEnd_7692031] using wordTrace_append hprefix tailTrace_7692031
  have hstable : (prefixWord ++ tailWord_7692031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692031).length < 2 ^ (prefixWord ++ tailWord_7692031).sum := by decide
  have hdescent : baseEnd_7692031 < baseStart_7692031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692035 : List Nat := [1, 1, 1, 3, 2, 2, 2, 6, 1, 4]
def baseStart_7692035 : Nat := 118140960795 + 7692035 * 2 ^ 59
def prefixEnd_7692035 : Nat := 4983230072969 + 3 ^ 40 * 7692035 * 2
def baseEnd_7692035 : Nat := 1316570388735639203795827

theorem tailTrace_7692035 : CollatzResearch.WordTrace tailWord_7692035 prefixEnd_7692035 1316570388735639203795827 := by
  unfold tailWord_7692035
  simp only [CollatzResearch.WordTrace]
  refine ⟨280551564688078364834509559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187034376458718909889673039 280551564688078364834509559)
  ·
    refine ⟨420827347032117547251764339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280551564688078364834509559 420827347032117547251764339)
    ·
      refine ⟨631241020548176320877646509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420827347032117547251764339 631241020548176320877646509)
      ·
        refine ⟨236715382705566120329117441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631241020548176320877646509 236715382705566120329117441)
        ·
          refine ⟨177536537029174590246838081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236715382705566120329117441 177536537029174590246838081)
          ·
            refine ⟨133152402771880942685128561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177536537029174590246838081 133152402771880942685128561)
            ·
              refine ⟨99864302078910707013846421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133152402771880942685128561 99864302078910707013846421)
              ·
                refine ⟨4681139159948939391274051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99864302078910707013846421 4681139159948939391274051)
                ·
                  refine ⟨7021708739923409086911077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681139159948939391274051 7021708739923409086911077)
                  ·
                    refine ⟨1316570388735639203795827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7021708739923409086911077 1316570388735639203795827)
                    ·
                      rfl

theorem cell23_7692035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 4].length) (baseStart_7692035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692035 prefixEnd_7692035 := by exact prefixLift 7692035
  have htrace : WordTrace (prefixWord ++ tailWord_7692035) baseStart_7692035 baseEnd_7692035 := by
    simpa [prefixWord, tailWord_7692035, baseEnd_7692035] using wordTrace_append hprefix tailTrace_7692035
  have hstable : (prefixWord ++ tailWord_7692035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692035).length < 2 ^ (prefixWord ++ tailWord_7692035).sum := by decide
  have hdescent : baseEnd_7692035 < baseStart_7692035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692086 : List Nat := [5, 1, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_7692086 : Nat := 118140960795 + 7692086 * 2 ^ 59
def prefixEnd_7692086 : Nat := 4983230072969 + 3 ^ 40 * 7692086 * 2
def baseEnd_7692086 : Nat := 1316579117906765637283249

theorem tailTrace_7692086 : CollatzResearch.WordTrace tailWord_7692086 prefixEnd_7692086 1316579117906765637283249 := by
  unfold tailWord_7692086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17534589050680850034038507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187035616540595733696410741 17534589050680850034038507)
  ·
    refine ⟨26301883576021275051057761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17534589050680850034038507 26301883576021275051057761)
    ·
      refine ⟨19726412682015956288293321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26301883576021275051057761 19726412682015956288293321)
      ·
        refine ⟨14794809511511967216219991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19726412682015956288293321 14794809511511967216219991)
        ·
          refine ⟨22192214267267950824329987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14794809511511967216219991 22192214267267950824329987)
          ·
            refine ⟨33288321400901926236494981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22192214267267950824329987 33288321400901926236494981)
            ·
              refine ⟨6241560262669111169342809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33288321400901926236494981 6241560262669111169342809)
              ·
                refine ⟨4681170197001833377007107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6241560262669111169342809 4681170197001833377007107)
                ·
                  refine ⟨7021755295502750065510661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681170197001833377007107 7021755295502750065510661)
                  ·
                    refine ⟨1316579117906765637283249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7021755295502750065510661 1316579117906765637283249)
                    ·
                      rfl

theorem cell23_7692086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_7692086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692086 prefixEnd_7692086 := by exact prefixLift 7692086
  have htrace : WordTrace (prefixWord ++ tailWord_7692086) baseStart_7692086 baseEnd_7692086 := by
    simpa [prefixWord, tailWord_7692086, baseEnd_7692086] using wordTrace_append hprefix tailTrace_7692086
  have hstable : (prefixWord ++ tailWord_7692086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692086).length < 2 ^ (prefixWord ++ tailWord_7692086).sum := by decide
  have hdescent : baseEnd_7692086 < baseStart_7692086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692109 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_7692109 : Nat := 118140960795 + 7692109 * 2 ^ 59
def prefixEnd_7692109 : Nat := 4983230072969 + 3 ^ 40 * 7692109 * 2
def baseEnd_7692109 : Nat := 3949749163775350321862141

theorem tailTrace_7692109 : CollatzResearch.WordTrace tailWord_7692109 prefixEnd_7692109 3949749163775350321862141 := by
  unfold tailWord_7692109
  simp only [CollatzResearch.WordTrace]
  refine ⟨280554263689810275472703381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187036175793206850315135587 280554263689810275472703381)
  ·
    refine ⟨13150981110459856662782971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 280554263689810275472703381 13150981110459856662782971)
    ·
      refine ⟨19726471665689784994174457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13150981110459856662782971 19726471665689784994174457)
      ·
        refine ⟨14794853749267338745630843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19726471665689784994174457 14794853749267338745630843)
        ·
          refine ⟨22192280623901008118446265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14794853749267338745630843 22192280623901008118446265)
          ·
            refine ⟨16644210467925756088834699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22192280623901008118446265 16644210467925756088834699)
            ·
              refine ⟨24966315701888634133252049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16644210467925756088834699 24966315701888634133252049)
              ·
                refine ⟨18724736776416475599939037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24966315701888634133252049 18724736776416475599939037)
                ·
                  refine ⟨7021776291156178349977139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18724736776416475599939037 7021776291156178349977139)
                  ·
                    refine ⟨10532664436734267524965709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7021776291156178349977139 10532664436734267524965709)
                    ·
                      refine ⟨3949749163775350321862141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10532664436734267524965709 3949749163775350321862141)
                      ·
                        rfl

theorem cell23_7692109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_7692109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692109 prefixEnd_7692109 := by exact prefixLift 7692109
  have htrace : WordTrace (prefixWord ++ tailWord_7692109) baseStart_7692109 baseEnd_7692109 := by
    simpa [prefixWord, tailWord_7692109, baseEnd_7692109] using wordTrace_append hprefix tailTrace_7692109
  have hstable : (prefixWord ++ tailWord_7692109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692109).length < 2 ^ (prefixWord ++ tailWord_7692109).sum := by decide
  have hdescent : baseEnd_7692109 < baseStart_7692109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692119 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 2, 3, 2]
def baseStart_7692119 : Nat := 118140960795 + 7692119 * 2 ^ 59
def prefixEnd_7692119 : Nat := 4983230072969 + 3 ^ 40 * 7692119 * 2
def baseEnd_7692119 : Nat := 3949754298581895282737095

theorem tailTrace_7692119 : CollatzResearch.WordTrace tailWord_7692119 prefixEnd_7692119 3949754298581895282737095 := by
  unfold tailWord_7692119
  simp only [CollatzResearch.WordTrace]
  refine ⟨280554628419774047180567411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187036418946516031453711607 280554628419774047180567411)
  ·
    refine ⟨420831942629661070770851117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280554628419774047180567411 420831942629661070770851117)
    ·
      refine ⟨157811978486122901539069169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420831942629661070770851117 157811978486122901539069169)
      ·
        refine ⟨118358983864592176154301877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157811978486122901539069169 118358983864592176154301877)
        ·
          refine ⟨11096154737305516514465801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118358983864592176154301877 11096154737305516514465801)
          ·
            refine ⟨8322116052979137385849351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11096154737305516514465801 8322116052979137385849351)
            ·
              refine ⟨12483174079468706078774027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322116052979137385849351 12483174079468706078774027)
              ·
                refine ⟨18724761119203059118161041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483174079468706078774027 18724761119203059118161041)
                ·
                  refine ⟨14043570839402294338620781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18724761119203059118161041 14043570839402294338620781)
                  ·
                    refine ⟨5266339064775860376982793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14043570839402294338620781 5266339064775860376982793)
                    ·
                      refine ⟨3949754298581895282737095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266339064775860376982793 3949754298581895282737095)
                      ·
                        rfl

theorem cell23_7692119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_7692119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692119 prefixEnd_7692119 := by exact prefixLift 7692119
  have htrace : WordTrace (prefixWord ++ tailWord_7692119) baseStart_7692119 baseEnd_7692119 := by
    simpa [prefixWord, tailWord_7692119, baseEnd_7692119] using wordTrace_append hprefix tailTrace_7692119
  have hstable : (prefixWord ++ tailWord_7692119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692119).length < 2 ^ (prefixWord ++ tailWord_7692119).sum := by decide
  have hdescent : baseEnd_7692119 < baseStart_7692119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692132 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_7692132 : Nat := 118140960795 + 7692132 * 2 ^ 59
def prefixEnd_7692132 : Nat := 4983230072969 + 3 ^ 40 * 7692132 * 2
def baseEnd_7692132 : Nat := 3949760973830403731874535

theorem tailTrace_7692132 : CollatzResearch.WordTrace tailWord_7692132 prefixEnd_7692132 3949760973830403731874535 := by
  unfold tailWord_7692132
  simp only [CollatzResearch.WordTrace]
  refine ⟨140277551284363475200395325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187036735045817966933860433 140277551284363475200395325)
  ·
    refine ⟨52604081731636303200148247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140277551284363475200395325 52604081731636303200148247)
    ·
      refine ⟨78906122597454454800222371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52604081731636303200148247 78906122597454454800222371)
      ·
        refine ⟨118359183896181682200333557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78906122597454454800222371 118359183896181682200333557)
        ·
          refine ⟨11096173490267032706281271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118359183896181682200333557 11096173490267032706281271)
          ·
            refine ⟨16644260235400549059421907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11096173490267032706281271 16644260235400549059421907)
            ·
              refine ⟨24966390353100823589132861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16644260235400549059421907 24966390353100823589132861)
              ·
                refine ⟨9362396382412808845924823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24966390353100823589132861 9362396382412808845924823)
                ·
                  refine ⟨14043594573619213268887235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9362396382412808845924823 14043594573619213268887235)
                  ·
                    refine ⟨21065391860428819903330853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14043594573619213268887235 21065391860428819903330853)
                    ·
                      refine ⟨3949760973830403731874535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21065391860428819903330853 3949760973830403731874535)
                      ·
                        rfl

theorem cell23_7692132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_7692132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692132 prefixEnd_7692132 := by exact prefixLift 7692132
  have htrace : WordTrace (prefixWord ++ tailWord_7692132) baseStart_7692132 baseEnd_7692132 := by
    simpa [prefixWord, tailWord_7692132, baseEnd_7692132] using wordTrace_append hprefix tailTrace_7692132
  have hstable : (prefixWord ++ tailWord_7692132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692132).length < 2 ^ (prefixWord ++ tailWord_7692132).sum := by decide
  have hdescent : baseEnd_7692132 < baseStart_7692132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692142 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_7692142 : Nat := 118140960795 + 7692142 * 2 ^ 59
def prefixEnd_7692142 : Nat := 4983230072969 + 3 ^ 40 * 7692142 * 2
def baseEnd_7692142 : Nat := 1316588702878982897583163

theorem tailTrace_7692142 : CollatzResearch.WordTrace tailWord_7692142 prefixEnd_7692142 1316588702878982897583163 := by
  unfold tailWord_7692142
  simp only [CollatzResearch.WordTrace]
  refine ⟨35069433412336340263581835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187036978199127148072436453 35069433412336340263581835)
  ·
    refine ⟨52604150118504510395372753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35069433412336340263581835 52604150118504510395372753)
    ·
      refine ⟨39453112588878382796529565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52604150118504510395372753 39453112588878382796529565)
      ·
        refine ⟨14794917220829393548698587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39453112588878382796529565 14794917220829393548698587)
        ·
          refine ⟨22192375831244090323047881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14794917220829393548698587 22192375831244090323047881)
          ·
            refine ⟨16644281873433067742285911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22192375831244090323047881 16644281873433067742285911)
            ·
              refine ⟨24966422810149601613428867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16644281873433067742285911 24966422810149601613428867)
              ·
                refine ⟨37449634215224402420143301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24966422810149601613428867 37449634215224402420143301)
                ·
                  refine ⟨7021806415354575453776869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37449634215224402420143301 7021806415354575453776869)
                  ·
                    refine ⟨1316588702878982897583163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7021806415354575453776869 1316588702878982897583163)
                    ·
                      rfl

theorem cell23_7692142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_7692142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692142 prefixEnd_7692142 := by exact prefixLift 7692142
  have htrace : WordTrace (prefixWord ++ tailWord_7692142) baseStart_7692142 baseEnd_7692142 := by
    simpa [prefixWord, tailWord_7692142, baseEnd_7692142] using wordTrace_append hprefix tailTrace_7692142
  have hstable : (prefixWord ++ tailWord_7692142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692142).length < 2 ^ (prefixWord ++ tailWord_7692142).sum := by decide
  have hdescent : baseEnd_7692142 < baseStart_7692142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692149 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_7692149 : Nat := 118140960795 + 7692149 * 2 ^ 59
def prefixEnd_7692149 : Nat := 4983230072969 + 3 ^ 40 * 7692149 * 2
def baseEnd_7692149 : Nat := 3949769703001530165361957

theorem tailTrace_7692149 : CollatzResearch.WordTrace tailWord_7692149 prefixEnd_7692149 3949769703001530165361957 := by
  unfold tailWord_7692149
  simp only [CollatzResearch.WordTrace]
  refine ⟨280555722609665362304159501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187037148406443574869439667 280555722609665362304159501)
  ·
    refine ⟨105208395978624510864059813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280555722609665362304159501 105208395978624510864059813)
    ·
      refine ⟨19726574245992095787011215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105208395978624510864059813 19726574245992095787011215)
      ·
        refine ⟨29589861368988143680516823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19726574245992095787011215 29589861368988143680516823)
        ·
          refine ⟨44384792053482215520775235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29589861368988143680516823 44384792053482215520775235)
          ·
            refine ⟨66577188080223323281162853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44384792053482215520775235 66577188080223323281162853)
            ·
              refine ⟨12483222765041873115218035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66577188080223323281162853 12483222765041873115218035)
              ·
                refine ⟨18724834147562809672827053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483222765041873115218035 18724834147562809672827053)
                ·
                  refine ⟨7021812805336053627310145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18724834147562809672827053 7021812805336053627310145)
                  ·
                    refine ⟨5266359604002040220482609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7021812805336053627310145 5266359604002040220482609)
                    ·
                      refine ⟨3949769703001530165361957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266359604002040220482609 3949769703001530165361957)
                      ·
                        rfl

theorem cell23_7692149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_7692149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692149 prefixEnd_7692149 := by exact prefixLift 7692149
  have htrace : WordTrace (prefixWord ++ tailWord_7692149) baseStart_7692149 baseEnd_7692149 := by
    simpa [prefixWord, tailWord_7692149, baseEnd_7692149] using wordTrace_append hprefix tailTrace_7692149
  have hstable : (prefixWord ++ tailWord_7692149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692149).length < 2 ^ (prefixWord ++ tailWord_7692149).sum := by decide
  have hdescent : baseEnd_7692149 < baseStart_7692149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692175 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 9, 3, 2]
def baseStart_7692175 : Nat := 118140960795 + 7692175 * 2 ^ 59
def prefixEnd_7692175 : Nat := 4983230072969 + 3 ^ 40 * 7692175 * 2
def baseEnd_7692175 : Nat := 3949783053498547063636837

theorem tailTrace_7692175 : CollatzResearch.WordTrace tailWord_7692175 prefixEnd_7692175 3949783053498547063636837 := by
  unfold tailWord_7692175
  simp only [CollatzResearch.WordTrace]
  refine ⟨280556670907571168744605979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187037780605047445829737319 280556670907571168744605979)
  ·
    refine ⟨420835006361356753116908969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280556670907571168744605979 420835006361356753116908969)
    ·
      refine ⟨315626254771017564837681727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420835006361356753116908969 315626254771017564837681727)
      ·
        refine ⟨473439382156526347256522591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315626254771017564837681727 473439382156526347256522591)
        ·
          refine ⟨710159073234789520884783887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473439382156526347256522591 710159073234789520884783887)
          ·
            refine ⟨1065238609852184281327175831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710159073234789520884783887 1065238609852184281327175831)
            ·
              refine ⟨1597857914778276421990763747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065238609852184281327175831 1597857914778276421990763747)
              ·
                refine ⟨2396786872167414632986145621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597857914778276421990763747 2396786872167414632986145621)
                ·
                  refine ⟨14043673079105945115153197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2396786872167414632986145621 14043673079105945115153197)
                  ·
                    refine ⟨5266377404664729418182449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14043673079105945115153197 5266377404664729418182449)
                    ·
                      refine ⟨3949783053498547063636837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266377404664729418182449 3949783053498547063636837)
                      ·
                        rfl

theorem cell23_7692175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 3, 2].length) (baseStart_7692175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692175 prefixEnd_7692175 := by exact prefixLift 7692175
  have htrace : WordTrace (prefixWord ++ tailWord_7692175) baseStart_7692175 baseEnd_7692175 := by
    simpa [prefixWord, tailWord_7692175, baseEnd_7692175] using wordTrace_append hprefix tailTrace_7692175
  have hstable : (prefixWord ++ tailWord_7692175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692175).length < 2 ^ (prefixWord ++ tailWord_7692175).sum := by decide
  have hdescent : baseEnd_7692175 < baseStart_7692175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692200 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7692200 : Nat := 118140960795 + 7692200 * 2 ^ 59
def prefixEnd_7692200 : Nat := 4983230072969 + 3 ^ 40 * 7692200 * 2
def baseEnd_7692200 : Nat := 3949795890514909465824223

theorem tailTrace_7692200 : CollatzResearch.WordTrace tailWord_7692200 prefixEnd_7692200 3949795890514909465824223 := by
  unfold tailWord_7692200
  simp only [CollatzResearch.WordTrace]
  refine ⟨140278791366240299007133027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187038388488320398676177369 140278791366240299007133027)
  ·
    refine ⟨210418187049360448510699541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140278791366240299007133027 210418187049360448510699541)
    ·
      refine ⟨9863352517938771023939041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210418187049360448510699541 9863352517938771023939041)
      ·
        refine ⟨7397514388454078267954281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9863352517938771023939041 7397514388454078267954281)
        ·
          refine ⟨5548135791340558700965711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7397514388454078267954281 5548135791340558700965711)
          ·
            refine ⟨8322203687010838051448567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5548135791340558700965711 8322203687010838051448567)
            ·
              refine ⟨12483305530516257077172851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322203687010838051448567 12483305530516257077172851)
              ·
                refine ⟨18724958295774385615759277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483305530516257077172851 18724958295774385615759277)
                ·
                  refine ⟨7021859360915394605909729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18724958295774385615759277 7021859360915394605909729)
                  ·
                    refine ⟨5266394520686545954432297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7021859360915394605909729 5266394520686545954432297)
                    ·
                      refine ⟨3949795890514909465824223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266394520686545954432297 3949795890514909465824223)
                      ·
                        rfl

theorem cell23_7692200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7692200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692200 prefixEnd_7692200 := by exact prefixLift 7692200
  have htrace : WordTrace (prefixWord ++ tailWord_7692200) baseStart_7692200 baseEnd_7692200 := by
    simpa [prefixWord, tailWord_7692200, baseEnd_7692200] using wordTrace_append hprefix tailTrace_7692200
  have hstable : (prefixWord ++ tailWord_7692200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692200).length < 2 ^ (prefixWord ++ tailWord_7692200).sum := by decide
  have hdescent : baseEnd_7692200 < baseStart_7692200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692269 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7692269 : Nat := 118140960795 + 7692269 * 2 ^ 59
def prefixEnd_7692269 : Nat := 4983230072969 + 3 ^ 40 * 7692269 * 2
def baseEnd_7692269 : Nat := 3949831320680069695861405

theorem tailTrace_7692269 : CollatzResearch.WordTrace tailWord_7692269 prefixEnd_7692269 3949831320680069695861405 := by
  unfold tailWord_7692269
  simp only [CollatzResearch.WordTrace]
  refine ⟨280560099369230622798527861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187040066246153748532351907 280560099369230622798527861)
  ·
    refine ⟨26302509315865370887361987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280560099369230622798527861 26302509315865370887361987)
    ·
      refine ⟨39453763973798056331042981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26302509315865370887361987 39453763973798056331042981)
      ·
        refine ⟨7397580745087135562070559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39453763973798056331042981 7397580745087135562070559)
        ·
          refine ⟨11096371117630703343105839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7397580745087135562070559 11096371117630703343105839)
          ·
            refine ⟨16644556676446055014658759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11096371117630703343105839 16644556676446055014658759)
            ·
              refine ⟨24966835014669082521988139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16644556676446055014658759 24966835014669082521988139)
              ·
                refine ⟨37450252522003623782982209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24966835014669082521988139 37450252522003623782982209)
                ·
                  refine ⟨28087689391502717837236657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37450252522003623782982209 28087689391502717837236657)
                  ·
                    refine ⟨21065767043627038377927493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28087689391502717837236657 21065767043627038377927493)
                    ·
                      refine ⟨3949831320680069695861405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21065767043627038377927493 3949831320680069695861405)
                      ·
                        rfl

theorem cell23_7692269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7692269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692269 prefixEnd_7692269 := by exact prefixLift 7692269
  have htrace : WordTrace (prefixWord ++ tailWord_7692269) baseStart_7692269 baseEnd_7692269 := by
    simpa [prefixWord, tailWord_7692269, baseEnd_7692269] using wordTrace_append hprefix tailTrace_7692269
  have hstable : (prefixWord ++ tailWord_7692269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692269).length < 2 ^ (prefixWord ++ tailWord_7692269).sum := by decide
  have hdescent : baseEnd_7692269 < baseStart_7692269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692288 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 1, 10]
def baseStart_7692288 : Nat := 118140960795 + 7692288 * 2 ^ 59
def prefixEnd_7692288 : Nat := 4983230072969 + 3 ^ 40 * 7692288 * 2
def baseEnd_7692288 : Nat := 1316613692270835040507939

theorem tailTrace_7692288 : CollatzResearch.WordTrace tailWord_7692288 prefixEnd_7692288 1316613692270835040507939 := by
  unfold tailWord_7692288
  simp only [CollatzResearch.WordTrace]
  refine ⟨140280396178080894521734759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187040528237441192695646345 140280396178080894521734759)
  ·
    refine ⟨210420594267121341782602139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140280396178080894521734759 210420594267121341782602139)
    ·
      refine ⟨315630891400682012673903209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210420594267121341782602139 315630891400682012673903209)
      ·
        refine ⟨236723168550511509505427407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315630891400682012673903209 236723168550511509505427407)
        ·
          refine ⟨355084752825767264258141111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236723168550511509505427407 355084752825767264258141111)
          ·
            refine ⟨532627129238650896387211667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355084752825767264258141111 532627129238650896387211667)
            ·
              refine ⟨798940693857976344580817501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532627129238650896387211667 798940693857976344580817501)
              ·
                refine ⟨299602760196741129217806563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 798940693857976344580817501 299602760196741129217806563)
                ·
                  refine ⟨449404140295111693826709845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299602760196741129217806563 449404140295111693826709845)
                  ·
                    refine ⟨1316613692270835040507939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 449404140295111693826709845 1316613692270835040507939)
                    ·
                      rfl

theorem cell23_7692288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_7692288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692288 prefixEnd_7692288 := by exact prefixLift 7692288
  have htrace : WordTrace (prefixWord ++ tailWord_7692288) baseStart_7692288 baseEnd_7692288 := by
    simpa [prefixWord, tailWord_7692288, baseEnd_7692288] using wordTrace_append hprefix tailTrace_7692288
  have hstable : (prefixWord ++ tailWord_7692288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692288).length < 2 ^ (prefixWord ++ tailWord_7692288).sum := by decide
  have hdescent : baseEnd_7692288 < baseStart_7692288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692294 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7692294 : Nat := 118140960795 + 7692294 * 2 ^ 59
def prefixEnd_7692294 : Nat := 4983230072969 + 3 ^ 40 * 7692294 * 2
def baseEnd_7692294 : Nat := 3949844157696432098048791

theorem tailTrace_7692294 : CollatzResearch.WordTrace tailWord_7692294 prefixEnd_7692294 3949844157696432098048791 := by
  unfold tailWord_7692294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8767531599816876627130873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187040674129426701378791957 8767531599816876627130873)
  ·
    refine ⟨6575648699862657470348155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8767531599816876627130873 6575648699862657470348155)
    ·
      refine ⟨9863473049793986205522233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575648699862657470348155 9863473049793986205522233)
      ·
        refine ⟨7397604787345489654141675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9863473049793986205522233 7397604787345489654141675)
        ·
          refine ⟨11096407181018234481212513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7397604787345489654141675 11096407181018234481212513)
          ·
            refine ⟨8322305385763675860909385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11096407181018234481212513 8322305385763675860909385)
            ·
              refine ⟨6241729039322756895682039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8322305385763675860909385 6241729039322756895682039)
              ·
                refine ⟨9362593558984135343523059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6241729039322756895682039 9362593558984135343523059)
                ·
                  refine ⟨14043890338476203015284589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9362593558984135343523059 14043890338476203015284589)
                  ·
                    refine ⟨5266458876928576130731721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14043890338476203015284589 5266458876928576130731721)
                    ·
                      refine ⟨3949844157696432098048791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266458876928576130731721 3949844157696432098048791)
                      ·
                        rfl

theorem cell23_7692294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7692294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692294 prefixEnd_7692294 := by exact prefixLift 7692294
  have htrace : WordTrace (prefixWord ++ tailWord_7692294) baseStart_7692294 baseEnd_7692294 := by
    simpa [prefixWord, tailWord_7692294, baseEnd_7692294] using wordTrace_append hprefix tailTrace_7692294
  have hstable : (prefixWord ++ tailWord_7692294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692294).length < 2 ^ (prefixWord ++ tailWord_7692294).sum := by decide
  have hdescent : baseEnd_7692294 < baseStart_7692294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692312 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 4, 4, 2]
def baseStart_7692312 : Nat := 118140960795 + 7692312 * 2 ^ 59
def prefixEnd_7692312 : Nat := 4983230072969 + 3 ^ 40 * 7692312 * 2
def baseEnd_7692312 : Nat := 3949853400348213027623707

theorem tailTrace_7692312 : CollatzResearch.WordTrace tailWord_7692312 prefixEnd_7692312 3949853400348213027623707 := by
  unfold tailWord_7692312
  simp only [CollatzResearch.WordTrace]
  refine ⟨140280833854037420571171595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187041111805383227428228793 140280833854037420571171595)
  ·
    refine ⟨210421250781056130856757393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140280833854037420571171595 210421250781056130856757393)
    ·
      refine ⟨157815938085792098142568045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210421250781056130856757393 157815938085792098142568045)
      ·
        refine ⟨59180976782172036803463017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157815938085792098142568045 59180976782172036803463017)
        ·
          refine ⟨44385732586629027602597263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59180976782172036803463017 44385732586629027602597263)
          ·
            refine ⟨66578598879943541403895895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44385732586629027602597263 66578598879943541403895895)
            ·
              refine ⟨99867898319915312105843843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66578598879943541403895895 99867898319915312105843843)
              ·
                refine ⟨149801847479872968158765765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99867898319915312105843843 149801847479872968158765765)
                ·
                  refine ⟨28087846402476181529768581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149801847479872968158765765 28087846402476181529768581)
                  ·
                    refine ⟨5266471200464284036831609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28087846402476181529768581 5266471200464284036831609)
                    ·
                      refine ⟨3949853400348213027623707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266471200464284036831609 3949853400348213027623707)
                      ·
                        rfl

theorem cell23_7692312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_7692312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692312 prefixEnd_7692312 := by exact prefixLift 7692312
  have htrace : WordTrace (prefixWord ++ tailWord_7692312) baseStart_7692312 baseEnd_7692312 := by
    simpa [prefixWord, tailWord_7692312, baseEnd_7692312] using wordTrace_append hprefix tailTrace_7692312
  have hstable : (prefixWord ++ tailWord_7692312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692312).length < 2 ^ (prefixWord ++ tailWord_7692312).sum := by decide
  have hdescent : baseEnd_7692312 < baseStart_7692312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692342 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_7692342 : Nat := 118140960795 + 7692342 * 2 ^ 59
def prefixEnd_7692342 : Nat := 4983230072969 + 3 ^ 40 * 7692342 * 2
def baseEnd_7692342 : Nat := 3949868804767847910248569

theorem tailTrace_7692342 : CollatzResearch.WordTrace tailWord_7692342 prefixEnd_7692342 3949868804767847910248569 := by
  unfold tailWord_7692342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17535172618622884766620955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187041841265310770843956853 17535172618622884766620955)
  ·
    refine ⟨26302758927934327149931433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17535172618622884766620955 26302758927934327149931433)
    ·
      refine ⟨19727069195950745362448575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26302758927934327149931433 19727069195950745362448575)
      ·
        refine ⟨29590603793926118043672863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19727069195950745362448575 29590603793926118043672863)
        ·
          refine ⟨44385905690889177065509295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29590603793926118043672863 44385905690889177065509295)
          ·
            refine ⟨66578858536333765598263943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44385905690889177065509295 66578858536333765598263943)
            ·
              refine ⟨99868287804500648397395915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66578858536333765598263943 99868287804500648397395915)
              ·
                refine ⟨149802431706750972596093873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99868287804500648397395915 149802431706750972596093873)
                ·
                  refine ⟨112351823780063229447070405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149802431706750972596093873 112351823780063229447070405)
                  ·
                    refine ⟨21065966958761855521325701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112351823780063229447070405 21065966958761855521325701)
                    ·
                      refine ⟨3949868804767847910248569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21065966958761855521325701 3949868804767847910248569)
                      ·
                        rfl

theorem cell23_7692342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_7692342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692342 prefixEnd_7692342 := by exact prefixLift 7692342
  have htrace : WordTrace (prefixWord ++ tailWord_7692342) baseStart_7692342 baseEnd_7692342 := by
    simpa [prefixWord, tailWord_7692342, baseEnd_7692342] using wordTrace_append hprefix tailTrace_7692342
  have hstable : (prefixWord ++ tailWord_7692342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692342).length < 2 ^ (prefixWord ++ tailWord_7692342).sum := by decide
  have hdescent : baseEnd_7692342 < baseStart_7692342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692385 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_7692385 : Nat := 118140960795 + 7692385 * 2 ^ 59
def prefixEnd_7692385 : Nat := 4983230072969 + 3 ^ 40 * 7692385 * 2
def baseEnd_7692385 : Nat := 3949890884435991242010871

theorem tailTrace_7692385 : CollatzResearch.WordTrace tailWord_7692385 prefixEnd_7692385 3949890884435991242010871 := by
  unfold tailWord_7692385
  simp only [CollatzResearch.WordTrace]
  refine ⟨280564330236810374609750609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187042886824540249739833739 280564330236810374609750609)
  ·
    refine ⟨210423247677607780957312957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280564330236810374609750609 210423247677607780957312957)
    ·
      refine ⟨78908717879102917858992359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210423247677607780957312957 78908717879102917858992359)
      ·
        refine ⟨118363076818654376788488539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78908717879102917858992359 118363076818654376788488539)
        ·
          refine ⟨177544615227981565182732809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118363076818654376788488539 177544615227981565182732809)
          ·
            refine ⟨133158461420986173887049607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177544615227981565182732809 133158461420986173887049607)
            ·
              refine ⟨199737692131479260830574411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133158461420986173887049607 199737692131479260830574411)
              ·
                refine ⟨299606538197218891245861617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199737692131479260830574411 299606538197218891245861617)
                ·
                  refine ⟨224704903647914168434396213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299606538197218891245861617 224704903647914168434396213)
                  ·
                    refine ⟨21066084716991953290724645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224704903647914168434396213 21066084716991953290724645)
                    ·
                      refine ⟨3949890884435991242010871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21066084716991953290724645 3949890884435991242010871)
                      ·
                        rfl

theorem cell23_7692385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_7692385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692385 prefixEnd_7692385 := by exact prefixLift 7692385
  have htrace : WordTrace (prefixWord ++ tailWord_7692385) baseStart_7692385 baseEnd_7692385 := by
    simpa [prefixWord, tailWord_7692385, baseEnd_7692385] using wordTrace_append hprefix tailTrace_7692385
  have hstable : (prefixWord ++ tailWord_7692385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692385).length < 2 ^ (prefixWord ++ tailWord_7692385).sum := by decide
  have hdescent : baseEnd_7692385 < baseStart_7692385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692399 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 1, 5]
def baseStart_7692399 : Nat := 118140960795 + 7692399 * 2 ^ 59
def prefixEnd_7692399 : Nat := 4983230072969 + 3 ^ 40 * 7692399 * 2
def baseEnd_7692399 : Nat := 1316632691055051395745269

theorem tailTrace_7692399 : CollatzResearch.WordTrace tailWord_7692399 prefixEnd_7692399 1316632691055051395745269 := by
  unfold tailWord_7692399
  simp only [CollatzResearch.WordTrace]
  refine ⟨280564840858759655000760251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187043227239173103333840167 280564840858759655000760251)
  ·
    refine ⟨420847261288139482501140377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280564840858759655000760251 420847261288139482501140377)
    ·
      refine ⟨315635445966104611875855283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420847261288139482501140377 315635445966104611875855283)
      ·
        refine ⟨473453168949156917813782925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315635445966104611875855283 473453168949156917813782925)
        ·
          refine ⟨177544938355933844180168597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473453168949156917813782925 177544938355933844180168597)
          ·
            refine ⟨8322418985434398945945403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177544938355933844180168597 8322418985434398945945403)
            ·
              refine ⟨12483628478151598418918105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322418985434398945945403 12483628478151598418918105)
              ·
                refine ⟨9362721358613698814188579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12483628478151598418918105 9362721358613698814188579)
                ·
                  refine ⟨14044082037920548221282869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9362721358613698814188579 14044082037920548221282869)
                  ·
                    refine ⟨1316632691055051395745269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14044082037920548221282869 1316632691055051395745269)
                    ·
                      rfl

theorem cell23_7692399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 5].length) (baseStart_7692399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692399 prefixEnd_7692399 := by exact prefixLift 7692399
  have htrace : WordTrace (prefixWord ++ tailWord_7692399) baseStart_7692399 baseEnd_7692399 := by
    simpa [prefixWord, tailWord_7692399, baseEnd_7692399] using wordTrace_append hprefix tailTrace_7692399
  have hstable : (prefixWord ++ tailWord_7692399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692399).length < 2 ^ (prefixWord ++ tailWord_7692399).sum := by decide
  have hdescent : baseEnd_7692399 < baseStart_7692399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692406 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_7692406 : Nat := 118140960795 + 7692406 * 2 ^ 59
def prefixEnd_7692406 : Nat := 4983230072969 + 3 ^ 40 * 7692406 * 2
def baseEnd_7692406 : Nat := 3949901667529735659848275

theorem tailTrace_7692406 : CollatzResearch.WordTrace tailWord_7692406 prefixEnd_7692406 3949901667529735659848275 := by
  unfold tailWord_7692406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17535318510608393449766567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187043397446489530130843381 17535318510608393449766567)
  ·
    refine ⟨26302977765912590174649851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17535318510608393449766567 26302977765912590174649851)
    ·
      refine ⟨39454466648868885261974777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26302977765912590174649851 39454466648868885261974777)
      ·
        refine ⟨29590849986651663946481083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39454466648868885261974777 29590849986651663946481083)
        ·
          refine ⟨44386274979977495919721625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29590849986651663946481083 44386274979977495919721625)
          ·
            refine ⟨33289706234983121939791219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44386274979977495919721625 33289706234983121939791219)
            ·
              refine ⟨49934559352474682909686829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33289706234983121939791219 49934559352474682909686829)
              ·
                refine ⟨18725459757178006091132561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49934559352474682909686829 18725459757178006091132561)
                ·
                  refine ⟨14044094817883504568349421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18725459757178006091132561 14044094817883504568349421)
                  ·
                    refine ⟨5266535556706314213131033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14044094817883504568349421 5266535556706314213131033)
                    ·
                      refine ⟨3949901667529735659848275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266535556706314213131033 3949901667529735659848275)
                      ·
                        rfl

theorem cell23_7692406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_7692406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692406 prefixEnd_7692406 := by exact prefixLift 7692406
  have htrace : WordTrace (prefixWord ++ tailWord_7692406) baseStart_7692406 baseEnd_7692406 := by
    simpa [prefixWord, tailWord_7692406, baseEnd_7692406] using wordTrace_append hprefix tailTrace_7692406
  have hstable : (prefixWord ++ tailWord_7692406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692406).length < 2 ^ (prefixWord ++ tailWord_7692406).sum := by decide
  have hdescent : baseEnd_7692406 < baseStart_7692406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692412 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_7692412 : Nat := 118140960795 + 7692412 * 2 ^ 59
def prefixEnd_7692412 : Nat := 4983230072969 + 3 ^ 40 * 7692412 * 2
def baseEnd_7692412 : Nat := 1316634916137887545457749

theorem tailTrace_7692412 : CollatzResearch.WordTrace tailWord_7692412 prefixEnd_7692412 1316634916137887545457749 := by
  unfold tailWord_7692412
  simp only [CollatzResearch.WordTrace]
  refine ⟨140282657503856279110491745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187043543338475038813988993 140282657503856279110491745)
  ·
    refine ⟨105211993127892209332868809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140282657503856279110491745 105211993127892209332868809)
    ·
      refine ⟨78908994845919156999651607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105211993127892209332868809 78908994845919156999651607)
      ·
        refine ⟨118363492268878735499477411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78908994845919156999651607 118363492268878735499477411)
        ·
          refine ⟨177545238403318103249216117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118363492268878735499477411 177545238403318103249216117)
          ·
            refine ⟨16644866100311072179614011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177545238403318103249216117 16644866100311072179614011)
            ·
              refine ⟨24967299150466608269421017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16644866100311072179614011 24967299150466608269421017)
              ·
                refine ⟨18725474362849956202065763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24967299150466608269421017 18725474362849956202065763)
                ·
                  refine ⟨28088211544274934303098645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18725474362849956202065763 28088211544274934303098645)
                  ·
                    refine ⟨1316634916137887545457749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28088211544274934303098645 1316634916137887545457749)
                    ·
                      rfl

theorem cell23_7692412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_7692412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692412 prefixEnd_7692412 := by exact prefixLift 7692412
  have htrace : WordTrace (prefixWord ++ tailWord_7692412) baseStart_7692412 baseEnd_7692412 := by
    simpa [prefixWord, tailWord_7692412, baseEnd_7692412] using wordTrace_append hprefix tailTrace_7692412
  have hstable : (prefixWord ++ tailWord_7692412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692412).length < 2 ^ (prefixWord ++ tailWord_7692412).sum := by decide
  have hdescent : baseEnd_7692412 < baseStart_7692412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692446 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_7692446 : Nat := 118140960795 + 7692446 * 2 ^ 59
def prefixEnd_7692446 : Nat := 4983230072969 + 3 ^ 40 * 7692446 * 2
def baseEnd_7692446 : Nat := 1316640735585305167782697

theorem tailTrace_7692446 : CollatzResearch.WordTrace tailWord_7692446 prefixEnd_7692446 1316640735585305167782697 := by
  unfold tailWord_7692446
  simp only [CollatzResearch.WordTrace]
  refine ⟨35070819386198672753465149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187044370059726254685147461 35070819386198672753465149)
  ·
    refine ⟨13151557269824502282549431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35070819386198672753465149 13151557269824502282549431)
    ·
      refine ⟨19727335904736753423824147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13151557269824502282549431 19727335904736753423824147)
      ·
        refine ⟨29591003857105130135736221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19727335904736753423824147 29591003857105130135736221)
        ·
          refine ⟨11096626446414423800901083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29591003857105130135736221 11096626446414423800901083)
          ·
            refine ⟨16644939669621635701351625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11096626446414423800901083 16644939669621635701351625)
            ·
              refine ⟨12483704752216226776013719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16644939669621635701351625 12483704752216226776013719)
              ·
                refine ⟨18725557128324340164020579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483704752216226776013719 18725557128324340164020579)
                ·
                  refine ⟨28088335692486510246030869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18725557128324340164020579 28088335692486510246030869)
                  ·
                    refine ⟨1316640735585305167782697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28088335692486510246030869 1316640735585305167782697)
                    ·
                      rfl

theorem cell23_7692446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_7692446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692446 prefixEnd_7692446 := by exact prefixLift 7692446
  have htrace : WordTrace (prefixWord ++ tailWord_7692446) baseStart_7692446 baseEnd_7692446 := by
    simpa [prefixWord, tailWord_7692446, baseEnd_7692446] using wordTrace_append hprefix tailTrace_7692446
  have hstable : (prefixWord ++ tailWord_7692446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692446).length < 2 ^ (prefixWord ++ tailWord_7692446).sum := by decide
  have hdescent : baseEnd_7692446 < baseStart_7692446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692449 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_7692449 : Nat := 118140960795 + 7692449 * 2 ^ 59
def prefixEnd_7692449 : Nat := 4983230072969 + 3 ^ 40 * 7692449 * 2
def baseEnd_7692449 : Nat := 3949923747197878991610577

theorem tailTrace_7692449 : CollatzResearch.WordTrace tailWord_7692449 prefixEnd_7692449 3949923747197878991610577 := by
  unfold tailWord_7692449
  simp only [CollatzResearch.WordTrace]
  refine ⟨280566664508578513540080401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187044443005719009026720267 280566664508578513540080401)
  ·
    refine ⟨210424998381433885155060301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280566664508578513540080401 210424998381433885155060301)
    ·
      refine ⟨78909374393037706933147613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210424998381433885155060301 78909374393037706933147613)
      ·
        refine ⟨29591015397389140099930355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78909374393037706933147613 29591015397389140099930355)
        ·
          refine ⟨44386523096083710149895533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29591015397389140099930355 44386523096083710149895533)
          ·
            refine ⟨16644946161031391306210825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44386523096083710149895533 16644946161031391306210825)
            ·
              refine ⟨12483709620773543479658119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16644946161031391306210825 12483709620773543479658119)
              ·
                refine ⟨18725564431160315219487179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483709620773543479658119 18725564431160315219487179)
                ·
                  refine ⟨28088346646740472829230769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18725564431160315219487179 28088346646740472829230769)
                  ·
                    refine ⟨21066259985055354621923077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28088346646740472829230769 21066259985055354621923077)
                    ·
                      refine ⟨3949923747197878991610577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21066259985055354621923077 3949923747197878991610577)
                      ·
                        rfl

theorem cell23_7692449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_7692449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692449 prefixEnd_7692449 := by exact prefixLift 7692449
  have htrace : WordTrace (prefixWord ++ tailWord_7692449) baseStart_7692449 baseEnd_7692449 := by
    simpa [prefixWord, tailWord_7692449, baseEnd_7692449] using wordTrace_append hprefix tailTrace_7692449
  have hstable : (prefixWord ++ tailWord_7692449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692449).length < 2 ^ (prefixWord ++ tailWord_7692449).sum := by decide
  have hdescent : baseEnd_7692449 < baseStart_7692449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692512 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_7692512 : Nat := 118140960795 + 7692512 * 2 ^ 59
def prefixEnd_7692512 : Nat := 4983230072969 + 3 ^ 40 * 7692512 * 2
def baseEnd_7692512 : Nat := 3949956096479112245122787

theorem tailTrace_7692512 : CollatzResearch.WordTrace tailWord_7692512 prefixEnd_7692512 3949956096479112245122787 := by
  unfold tailWord_7692512
  simp only [CollatzResearch.WordTrace]
  refine ⟨140284481153675137649811895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187045974871566850199749193 140284481153675137649811895)
  ·
    refine ⟨210426721730512706474717843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140284481153675137649811895 210426721730512706474717843)
    ·
      refine ⟨315640082595769059712076765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210426721730512706474717843 315640082595769059712076765)
      ·
        refine ⟨118365030973413397392028787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315640082595769059712076765 118365030973413397392028787)
        ·
          refine ⟨177547546460120096088043181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118365030973413397392028787 177547546460120096088043181)
          ·
            refine ⟨66580329922545036033016193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177547546460120096088043181 66580329922545036033016193)
            ·
              refine ⟨49935247441908777024762145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66580329922545036033016193 49935247441908777024762145)
              ·
                refine ⟨37451435581431582768571609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49935247441908777024762145 37451435581431582768571609)
                ·
                  refine ⟨28088576686073687076428707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37451435581431582768571609 28088576686073687076428707)
                  ·
                    refine ⟨42132865029110530614643061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28088576686073687076428707 42132865029110530614643061)
                    ·
                      refine ⟨3949956096479112245122787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42132865029110530614643061 3949956096479112245122787)
                      ·
                        rfl

theorem cell23_7692512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_7692512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692512 prefixEnd_7692512 := by exact prefixLift 7692512
  have htrace : WordTrace (prefixWord ++ tailWord_7692512) baseStart_7692512 baseEnd_7692512 := by
    simpa [prefixWord, tailWord_7692512, baseEnd_7692512] using wordTrace_append hprefix tailTrace_7692512
  have hstable : (prefixWord ++ tailWord_7692512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692512).length < 2 ^ (prefixWord ++ tailWord_7692512).sum := by decide
  have hdescent : baseEnd_7692512 < baseStart_7692512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692572 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_7692572 : Nat := 118140960795 + 7692572 * 2 ^ 59
def prefixEnd_7692572 : Nat := 4983230072969 + 3 ^ 40 * 7692572 * 2
def baseEnd_7692572 : Nat := 3949986905318382010372511

theorem tailTrace_7692572 : CollatzResearch.WordTrace tailWord_7692572 prefixEnd_7692572 3949986905318382010372511 := by
  unfold tailWord_7692572
  simp only [CollatzResearch.WordTrace]
  refine ⟨140285575343566452773403985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187047433791421937031205313 140285575343566452773403985)
  ·
    refine ⟨105214181507674839580052989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140285575343566452773403985 105214181507674839580052989)
    ·
      refine ⟨39455318065378064842519871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105214181507674839580052989 39455318065378064842519871)
      ·
        refine ⟨59182977098067097263779807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39455318065378064842519871 59182977098067097263779807)
        ·
          refine ⟨88774465647100645895669711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59182977098067097263779807 88774465647100645895669711)
          ·
            refine ⟨133161698470650968843504567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88774465647100645895669711 133161698470650968843504567)
            ·
              refine ⟨199742547705976453265256851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133161698470650968843504567 199742547705976453265256851)
              ·
                refine ⟨299613821558964679897885277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199742547705976453265256851 299613821558964679897885277)
                ·
                  refine ⟨112355183084611754961706979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299613821558964679897885277 112355183084611754961706979)
                  ·
                    refine ⟨168532774626917632442560469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112355183084611754961706979 168532774626917632442560469)
                    ·
                      refine ⟨3949986905318382010372511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168532774626917632442560469 3949986905318382010372511)
                      ·
                        rfl

theorem cell23_7692572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_7692572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692572 prefixEnd_7692572 := by exact prefixLift 7692572
  have htrace : WordTrace (prefixWord ++ tailWord_7692572) baseStart_7692572 baseEnd_7692572 := by
    simpa [prefixWord, tailWord_7692572, baseEnd_7692572] using wordTrace_append hprefix tailTrace_7692572
  have hstable : (prefixWord ++ tailWord_7692572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692572).length < 2 ^ (prefixWord ++ tailWord_7692572).sum := by decide
  have hdescent : baseEnd_7692572 < baseStart_7692572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692579 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 2, 5]
def baseStart_7692579 : Nat := 118140960795 + 7692579 * 2 ^ 59
def prefixEnd_7692579 : Nat := 4983230072969 + 3 ^ 40 * 7692579 * 2
def baseEnd_7692579 : Nat := 1316663499894321160994993

theorem tailTrace_7692579 : CollatzResearch.WordTrace tailWord_7692579 prefixEnd_7692579 1316663499894321160994993 := by
  unfold tailWord_7692579
  simp only [CollatzResearch.WordTrace]
  refine ⟨280571405998107545742312791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187047603998738363828208527 280571405998107545742312791)
  ·
    refine ⟨420857108997161318613469187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280571405998107545742312791 420857108997161318613469187)
    ·
      refine ⟨631285663495741977920203781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420857108997161318613469187 631285663495741977920203781)
      ·
        refine ⟨118366061905451620860038209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 631285663495741977920203781 118366061905451620860038209)
        ·
          refine ⟨88774546429088715645028657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118366061905451620860038209 88774546429088715645028657)
          ·
            refine ⟨66580909821816536733771493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88774546429088715645028657 66580909821816536733771493)
            ·
              refine ⟨12483920591590600637582155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66580909821816536733771493 12483920591590600637582155)
              ·
                refine ⟨18725880887385900956373233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12483920591590600637582155 18725880887385900956373233)
                ·
                  refine ⟨14044410665539425717279925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18725880887385900956373233 14044410665539425717279925)
                  ·
                    refine ⟨1316663499894321160994993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14044410665539425717279925 1316663499894321160994993)
                    ·
                      rfl

theorem cell23_7692579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 5].length) (baseStart_7692579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692579 prefixEnd_7692579 := by exact prefixLift 7692579
  have htrace : WordTrace (prefixWord ++ tailWord_7692579) baseStart_7692579 baseEnd_7692579 := by
    simpa [prefixWord, tailWord_7692579, baseEnd_7692579] using wordTrace_append hprefix tailTrace_7692579
  have hstable : (prefixWord ++ tailWord_7692579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692579).length < 2 ^ (prefixWord ++ tailWord_7692579).sum := by decide
  have hdescent : baseEnd_7692579 < baseStart_7692579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692596 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_7692596 : Nat := 118140960795 + 7692596 * 2 ^ 59
def prefixEnd_7692596 : Nat := 4983230072969 + 3 ^ 40 * 7692596 * 2
def baseEnd_7692596 : Nat := 1316666409618029972157467

theorem tailTrace_7692596 : CollatzResearch.WordTrace tailWord_7692596 prefixEnd_7692596 1316666409618029972157467 := by
  unfold tailWord_7692596
  simp only [CollatzResearch.WordTrace]
  refine ⟨140286013019522978822840821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187048017359363971763787761 140286013019522978822840821)
  ·
    refine ⟨13151813720580279264641327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140286013019522978822840821 13151813720580279264641327)
    ·
      refine ⟨19727720580870418896961991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13151813720580279264641327 19727720580870418896961991)
      ·
        refine ⟨29591580871305628345442987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19727720580870418896961991 29591580871305628345442987)
        ·
          refine ⟨44387371306958442518164481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29591580871305628345442987 44387371306958442518164481)
          ·
            refine ⟨33290528480218831888623361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44387371306958442518164481 33290528480218831888623361)
            ·
              refine ⟨24967896360164123916467521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33290528480218831888623361 24967896360164123916467521)
              ·
                refine ⟨18725922270123092937350641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24967896360164123916467521 18725922270123092937350641)
                ·
                  refine ⟨14044441702592319703012981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18725922270123092937350641 14044441702592319703012981)
                  ·
                    refine ⟨1316666409618029972157467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14044441702592319703012981 1316666409618029972157467)
                    ·
                      rfl

theorem cell23_7692596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_7692596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692596 prefixEnd_7692596 := by exact prefixLift 7692596
  have htrace : WordTrace (prefixWord ++ tailWord_7692596) baseStart_7692596 baseEnd_7692596 := by
    simpa [prefixWord, tailWord_7692596, baseEnd_7692596] using wordTrace_append hprefix tailTrace_7692596
  have hstable : (prefixWord ++ tailWord_7692596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692596).length < 2 ^ (prefixWord ++ tailWord_7692596).sum := by decide
  have hdescent : baseEnd_7692596 < baseStart_7692596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692599 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 3, 6, 2]
def baseStart_7692599 : Nat := 118140960795 + 7692599 * 2 ^ 59
def prefixEnd_7692599 : Nat := 4983230072969 + 3 ^ 40 * 7692599 * 2
def baseEnd_7692599 : Nat := 3950000769296053404734887

theorem tailTrace_7692599 : CollatzResearch.WordTrace tailWord_7692599 prefixEnd_7692599 3950000769296053404734887 := by
  unfold tailWord_7692599
  simp only [CollatzResearch.WordTrace]
  refine ⟨280572135458035089158040851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187048090305356726105360567 280572135458035089158040851)
  ·
    refine ⟨420858203187052633737061277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280572135458035089158040851 420858203187052633737061277)
    ·
      refine ⟨157821826195144737651397979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420858203187052633737061277 157821826195144737651397979)
      ·
        refine ⟨236732739292717106477096969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157821826195144737651397979 236732739292717106477096969)
        ·
          refine ⟨177549554469537829857822727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236732739292717106477096969 177549554469537829857822727)
          ·
            refine ⟨266324331704306744786734091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177549554469537829857822727 266324331704306744786734091)
            ·
              refine ⟨399486497556460117180101137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266324331704306744786734091 399486497556460117180101137)
              ·
                refine ⟨299614873167345087885075853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399486497556460117180101137 299614873167345087885075853)
                ·
                  refine ⟨112355577437754407956903445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299614873167345087885075853 112355577437754407956903445)
                  ·
                    refine ⟨5266667692394737872979849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112355577437754407956903445 5266667692394737872979849)
                    ·
                      refine ⟨3950000769296053404734887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266667692394737872979849 3950000769296053404734887)
                      ·
                        rfl

theorem cell23_7692599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_7692599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692599 prefixEnd_7692599 := by exact prefixLift 7692599
  have htrace : WordTrace (prefixWord ++ tailWord_7692599) baseStart_7692599 baseEnd_7692599 := by
    simpa [prefixWord, tailWord_7692599, baseEnd_7692599] using wordTrace_append hprefix tailTrace_7692599
  have hstable : (prefixWord ++ tailWord_7692599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692599).length < 2 ^ (prefixWord ++ tailWord_7692599).sum := by decide
  have hdescent : baseEnd_7692599 < baseStart_7692599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692643 : List Nat := [1, 1, 1, 5, 2, 1, 4, 3, 1, 4]
def baseStart_7692643 : Nat := 118140960795 + 7692643 * 2 ^ 59
def prefixEnd_7692643 : Nat := 4983230072969 + 3 ^ 40 * 7692643 * 2
def baseEnd_7692643 : Nat := 1316674454148283744194895

theorem tailTrace_7692643 : CollatzResearch.WordTrace tailWord_7692643 prefixEnd_7692643 1316674454148283744194895 := by
  unfold tailWord_7692643
  simp only [CollatzResearch.WordTrace]
  refine ⟨280573740269875684672642583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187049160179917123115095055 280573740269875684672642583)
  ·
    refine ⟨420860610404813527008963875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280573740269875684672642583 420860610404813527008963875)
    ·
      refine ⟨631290915607220290513445813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420860610404813527008963875 631290915607220290513445813)
      ·
        refine ⟨59183523338176902235635545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 631290915607220290513445813 59183523338176902235635545)
        ·
          refine ⟨44387642503632676676726659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59183523338176902235635545 44387642503632676676726659)
          ·
            refine ⟨66581463755449015015089989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44387642503632676676726659 66581463755449015015089989)
            ·
              refine ⟨12484024454146690315329373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66581463755449015015089989 12484024454146690315329373)
              ·
                refine ⟨4681509170305008868248515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12484024454146690315329373 4681509170305008868248515)
                ·
                  refine ⟨7022263755457513302372773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681509170305008868248515 7022263755457513302372773)
                  ·
                    refine ⟨1316674454148283744194895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7022263755457513302372773 1316674454148283744194895)
                    ·
                      rfl

theorem cell23_7692643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 4].length) (baseStart_7692643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692643 prefixEnd_7692643 := by exact prefixLift 7692643
  have htrace : WordTrace (prefixWord ++ tailWord_7692643) baseStart_7692643 baseEnd_7692643 := by
    simpa [prefixWord, tailWord_7692643, baseEnd_7692643] using wordTrace_append hprefix tailTrace_7692643
  have hstable : (prefixWord ++ tailWord_7692643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692643).length < 2 ^ (prefixWord ++ tailWord_7692643).sum := by decide
  have hdescent : baseEnd_7692643 < baseStart_7692643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692656 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 6]
def baseStart_7692656 : Nat := 118140960795 + 7692656 * 2 ^ 59
def prefixEnd_7692656 : Nat := 4983230072969 + 3 ^ 40 * 7692656 * 2
def baseEnd_7692656 : Nat := 438892226410373297969125

theorem tailTrace_7692656 : CollatzResearch.WordTrace tailWord_7692656 prefixEnd_7692656 438892226410373297969125 := by
  unfold tailWord_7692656
  simp only [CollatzResearch.WordTrace]
  refine ⟨140287107209414293946432911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187049476279219058595243881 140287107209414293946432911)
  ·
    refine ⟨210430660814121440919649367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140287107209414293946432911 210430660814121440919649367)
    ·
      refine ⟨315645991221182161379474051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210430660814121440919649367 315645991221182161379474051)
      ·
        refine ⟨473468986831773242069211077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315645991221182161379474051 473468986831773242069211077)
        ·
          refine ⟨88775435030957482887977077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473468986831773242069211077 88775435030957482887977077)
          ·
            refine ⟨8322697034152264020747851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88775435030957482887977077 8322697034152264020747851)
            ·
              refine ⟨12484045551228396031121777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322697034152264020747851 12484045551228396031121777)
              ·
                refine ⟨9363034163421297023341333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12484045551228396031121777 9363034163421297023341333)
                ·
                  refine ⟨438892226410373297969125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9363034163421297023341333 438892226410373297969125)
                  ·
                    rfl

theorem cell23_7692656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 6].length) (baseStart_7692656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692656 prefixEnd_7692656 := by exact prefixLift 7692656
  have htrace : WordTrace (prefixWord ++ tailWord_7692656) baseStart_7692656 baseEnd_7692656 := by
    simpa [prefixWord, tailWord_7692656, baseEnd_7692656] using wordTrace_append hprefix tailTrace_7692656
  have hstable : (prefixWord ++ tailWord_7692656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692656).length < 2 ^ (prefixWord ++ tailWord_7692656).sum := by decide
  have hdescent : baseEnd_7692656 < baseStart_7692656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692673 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 6]
def baseStart_7692673 : Nat := 118140960795 + 7692673 * 2 ^ 59
def prefixEnd_7692673 : Nat := 4983230072969 + 3 ^ 40 * 7692673 * 2
def baseEnd_7692673 : Nat := 438893196318276235023283

theorem tailTrace_7692673 : CollatzResearch.WordTrace tailWord_7692673 prefixEnd_7692673 438893196318276235023283 := by
  unfold tailWord_7692673
  simp only [CollatzResearch.WordTrace]
  refine ⟨280574834459766999796234673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187049889639844666530823115 280574834459766999796234673)
  ·
    refine ⟨210431125844825249847176005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280574834459766999796234673 210431125844825249847176005)
    ·
      refine ⟨39455836095904734346345501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210431125844825249847176005 39455836095904734346345501)
      ·
        refine ⟨14795938535964275379879563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39455836095904734346345501 14795938535964275379879563)
        ·
          refine ⟨22193907803946413069819345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14795938535964275379879563 22193907803946413069819345)
          ·
            refine ⟨16645430852959809802364509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22193907803946413069819345 16645430852959809802364509)
            ·
              refine ⟨6242036569859928675886691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16645430852959809802364509 6242036569859928675886691)
              ·
                refine ⟨9363054854789893013830037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6242036569859928675886691 9363054854789893013830037)
                ·
                  refine ⟨438893196318276235023283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9363054854789893013830037 438893196318276235023283)
                  ·
                    rfl

theorem cell23_7692673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 6].length) (baseStart_7692673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692673 prefixEnd_7692673 := by exact prefixLift 7692673
  have htrace : WordTrace (prefixWord ++ tailWord_7692673) baseStart_7692673 baseEnd_7692673 := by
    simpa [prefixWord, tailWord_7692673, baseEnd_7692673] using wordTrace_append hprefix tailTrace_7692673
  have hstable : (prefixWord ++ tailWord_7692673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692673).length < 2 ^ (prefixWord ++ tailWord_7692673).sum := by decide
  have hdescent : baseEnd_7692673 < baseStart_7692673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692676 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_7692676 : Nat := 118140960795 + 7692676 * 2 ^ 59
def prefixEnd_7692676 : Nat := 4983230072969 + 3 ^ 40 * 7692676 * 2
def baseEnd_7692676 : Nat := 3950040307306449603472033

theorem tailTrace_7692676 : CollatzResearch.WordTrace tailWord_7692676 prefixEnd_7692676 3950040307306449603472033 := by
  unfold tailWord_7692676
  simp only [CollatzResearch.WordTrace]
  refine ⟨140287471939378065654296941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187049962585837420872395921 140287471939378065654296941)
  ·
    refine ⟨52607801977266774620361353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140287471939378065654296941 52607801977266774620361353)
    ·
      refine ⟨39455851482950080965271015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52607801977266774620361353 39455851482950080965271015)
      ·
        refine ⟨59183777224425121447906523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39455851482950080965271015 59183777224425121447906523)
        ·
          refine ⟨88775665836637682171859785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59183777224425121447906523 88775665836637682171859785)
          ·
            refine ⟨66581749377478261628894839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88775665836637682171859785 66581749377478261628894839)
            ·
              refine ⟨99872624066217392443342259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66581749377478261628894839 99872624066217392443342259)
              ·
                refine ⟨149808936099326088665013389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99872624066217392443342259 149808936099326088665013389)
                ·
                  refine ⟨56178351037247283249380021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149808936099326088665013389 56178351037247283249380021)
                  ·
                    refine ⟨5266720409741932804629377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56178351037247283249380021 5266720409741932804629377)
                    ·
                      refine ⟨3950040307306449603472033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266720409741932804629377 3950040307306449603472033)
                      ·
                        rfl

theorem cell23_7692676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_7692676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692676 prefixEnd_7692676 := by exact prefixLift 7692676
  have htrace : WordTrace (prefixWord ++ tailWord_7692676) baseStart_7692676 baseEnd_7692676 := by
    simpa [prefixWord, tailWord_7692676, baseEnd_7692676] using wordTrace_append hprefix tailTrace_7692676
  have hstable : (prefixWord ++ tailWord_7692676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692676).length < 2 ^ (prefixWord ++ tailWord_7692676).sum := by decide
  have hdescent : baseEnd_7692676 < baseStart_7692676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692716 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_7692716 : Nat := 118140960795 + 7692716 * 2 ^ 59
def prefixEnd_7692716 : Nat := 4983230072969 + 3 ^ 40 * 7692716 * 2
def baseEnd_7692716 : Nat := 1316686948844209815657283

theorem tailTrace_7692716 : CollatzResearch.WordTrace tailWord_7692716 prefixEnd_7692716 1316686948844209815657283 := by
  unfold tailWord_7692716
  simp only [CollatzResearch.WordTrace]
  refine ⟨140288201399305609070025001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187050935199074145426700001 140288201399305609070025001)
  ·
    refine ⟨105216151049479206802518751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140288201399305609070025001 105216151049479206802518751)
    ·
      refine ⟨157824226574218810203778127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105216151049479206802518751 157824226574218810203778127)
      ·
        refine ⟨236736339861328215305667191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157824226574218810203778127 236736339861328215305667191)
        ·
          refine ⟨355104509791992322958500787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236736339861328215305667191 355104509791992322958500787)
          ·
            refine ⟨532656764687988484437751181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355104509791992322958500787 532656764687988484437751181)
            ·
              refine ⟨199746286757995681664156693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532656764687988484437751181 199746286757995681664156693)
              ·
                refine ⟨9363107191781047578007345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199746286757995681664156693 9363107191781047578007345)
                ·
                  refine ⟨7022330393835785683505509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9363107191781047578007345 7022330393835785683505509)
                  ·
                    refine ⟨1316686948844209815657283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7022330393835785683505509 1316686948844209815657283)
                    ·
                      rfl

theorem cell23_7692716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_7692716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692716 prefixEnd_7692716 := by exact prefixLift 7692716
  have htrace : WordTrace (prefixWord ++ tailWord_7692716) baseStart_7692716 baseEnd_7692716 := by
    simpa [prefixWord, tailWord_7692716, baseEnd_7692716] using wordTrace_append hprefix tailTrace_7692716
  have hstable : (prefixWord ++ tailWord_7692716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692716).length < 2 ^ (prefixWord ++ tailWord_7692716).sum := by decide
  have hdescent : baseEnd_7692716 < baseStart_7692716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692717 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_7692717 : Nat := 118140960795 + 7692717 * 2 ^ 59
def prefixEnd_7692717 : Nat := 4983230072969 + 3 ^ 40 * 7692717 * 2
def baseEnd_7692717 : Nat := 3950061360013283943059345

theorem tailTrace_7692717 : CollatzResearch.WordTrace tailWord_7692717 prefixEnd_7692717 3950061360013283943059345 := by
  unfold tailWord_7692717
  simp only [CollatzResearch.WordTrace]
  refine ⟨280576439271607595310836405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187050959514405063540557603 280576439271607595310836405)
  ·
    refine ⟨26304041181713212060390913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280576439271607595310836405 26304041181713212060390913)
    ·
      refine ⟨19728030886284909045293185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26304041181713212060390913 19728030886284909045293185)
      ·
        refine ⟨14796023164713681783969889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19728030886284909045293185 14796023164713681783969889)
        ·
          refine ⟨11097017373535261337977417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14796023164713681783969889 11097017373535261337977417)
          ·
            refine ⟨8322763030151446003483063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11097017373535261337977417 8322763030151446003483063)
            ·
              refine ⟨12484144545227169005224595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8322763030151446003483063 12484144545227169005224595)
              ·
                refine ⟨18726216817840753507836893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12484144545227169005224595 18726216817840753507836893)
                ·
                  refine ⟨7022331306690282565438835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18726216817840753507836893 7022331306690282565438835)
                  ·
                    refine ⟨10533496960035423848158253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7022331306690282565438835 10533496960035423848158253)
                    ·
                      refine ⟨3950061360013283943059345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10533496960035423848158253 3950061360013283943059345)
                      ·
                        rfl

theorem cell23_7692717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_7692717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692717 prefixEnd_7692717 := by exact prefixLift 7692717
  have htrace : WordTrace (prefixWord ++ tailWord_7692717) baseStart_7692717 baseEnd_7692717 := by
    simpa [prefixWord, tailWord_7692717, baseEnd_7692717] using wordTrace_append hprefix tailTrace_7692717
  have hstable : (prefixWord ++ tailWord_7692717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692717).length < 2 ^ (prefixWord ++ tailWord_7692717).sum := by decide
  have hdescent : baseEnd_7692717 < baseStart_7692717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692724 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 6]
def baseStart_7692724 : Nat := 118140960795 + 7692724 * 2 ^ 59
def prefixEnd_7692724 : Nat := 4983230072969 + 3 ^ 40 * 7692724 * 2
def baseEnd_7692724 : Nat := 438896106041985046185757

theorem tailTrace_7692724 : CollatzResearch.WordTrace tailWord_7692724 prefixEnd_7692724 438896106041985046185757 := by
  unfold tailWord_7692724
  simp only [CollatzResearch.WordTrace]
  refine ⟨140288347291291117753170613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187051129721721490337560817 140288347291291117753170613)
  ·
    refine ⟨13152032558558542289359745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140288347291291117753170613 13152032558558542289359745)
    ·
      refine ⟨9864024418918906717019809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13152032558558542289359745 9864024418918906717019809)
      ·
        refine ⟨7398018314189180037764857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9864024418918906717019809 7398018314189180037764857)
        ·
          refine ⟨5548513735641885028323643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7398018314189180037764857 5548513735641885028323643)
          ·
            refine ⟨8322770603462827542485465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5548513735641885028323643 8322770603462827542485465)
            ·
              refine ⟨6242077952597120656864099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8322770603462827542485465 6242077952597120656864099)
              ·
                refine ⟨9363116928895680985296149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6242077952597120656864099 9363116928895680985296149)
                ·
                  refine ⟨438896106041985046185757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9363116928895680985296149 438896106041985046185757)
                  ·
                    rfl

theorem cell23_7692724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_7692724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692724 prefixEnd_7692724 := by exact prefixLift 7692724
  have htrace : WordTrace (prefixWord ++ tailWord_7692724) baseStart_7692724 baseEnd_7692724 := by
    simpa [prefixWord, tailWord_7692724, baseEnd_7692724] using wordTrace_append hprefix tailTrace_7692724
  have hstable : (prefixWord ++ tailWord_7692724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692724).length < 2 ^ (prefixWord ++ tailWord_7692724).sum := by decide
  have hdescent : baseEnd_7692724 < baseStart_7692724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692729 : List Nat := [1, 2, 1, 4, 3, 1, 1, 10]
def baseStart_7692729 : Nat := 118140960795 + 7692729 * 2 ^ 59
def prefixEnd_7692729 : Nat := 4983230072969 + 3 ^ 40 * 7692729 * 2
def baseEnd_7692729 : Nat := 146298797103005107263307

theorem tailTrace_7692729 : CollatzResearch.WordTrace tailWord_7692729 prefixEnd_7692729 146298797103005107263307 := by
  unfold tailWord_7692729
  simp only [CollatzResearch.WordTrace]
  refine ⟨280576876947564121360273241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187051251298376080906848827 280576876947564121360273241)
  ·
    refine ⟨210432657710673091020204931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280576876947564121360273241 210432657710673091020204931)
    ·
      refine ⟨315648986566009636530307397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210432657710673091020204931 315648986566009636530307397)
      ·
        refine ⟨59184184981126806849432637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315648986566009636530307397 59184184981126806849432637)
        ·
          refine ⟨22194069367922552568537239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59184184981126806849432637 22194069367922552568537239)
          ·
            refine ⟨33291104051883828852805859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22194069367922552568537239 33291104051883828852805859)
            ·
              refine ⟨49936656077825743279208789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33291104051883828852805859 49936656077825743279208789)
              ·
                refine ⟨146298797103005107263307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49936656077825743279208789 146298797103005107263307)
                ·
                  rfl

theorem cell23_7692729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 10].length) (baseStart_7692729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692729 prefixEnd_7692729 := by exact prefixLift 7692729
  have htrace : WordTrace (prefixWord ++ tailWord_7692729) baseStart_7692729 baseEnd_7692729 := by
    simpa [prefixWord, tailWord_7692729, baseEnd_7692729] using wordTrace_append hprefix tailTrace_7692729
  have hstable : (prefixWord ++ tailWord_7692729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692729).length < 2 ^ (prefixWord ++ tailWord_7692729).sum := by decide
  have hdescent : baseEnd_7692729 < baseStart_7692729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692733 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_7692733 : Nat := 118140960795 + 7692733 * 2 ^ 59
def prefixEnd_7692733 : Nat := 4983230072969 + 3 ^ 40 * 7692733 * 2
def baseEnd_7692733 : Nat := 1316689858567918626819757

theorem tailTrace_7692733 : CollatzResearch.WordTrace tailWord_7692733 prefixEnd_7692733 1316689858567918626819757 := by
  unfold tailWord_7692733
  simp only [CollatzResearch.WordTrace]
  refine ⟨280577022839549630043418853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187051348559699753362279235 280577022839549630043418853)
  ·
    refine ⟨52608191782415555633141035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280577022839549630043418853 52608191782415555633141035)
    ·
      refine ⟨78912287673623333449711553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52608191782415555633141035 78912287673623333449711553)
      ·
        refine ⟨59184215755217500087283665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78912287673623333449711553 59184215755217500087283665)
        ·
          refine ⟨44388161816413125065462749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59184215755217500087283665 44388161816413125065462749)
          ·
            refine ⟨16645560681154921899548531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44388161816413125065462749 16645560681154921899548531)
            ·
              refine ⟨24968341021732382849322797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16645560681154921899548531 24968341021732382849322797)
              ·
                refine ⟨9363127883149643568496049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24968341021732382849322797 9363127883149643568496049)
                ·
                  refine ⟨7022345912362232676372037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9363127883149643568496049 7022345912362232676372037)
                  ·
                    refine ⟨1316689858567918626819757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7022345912362232676372037 1316689858567918626819757)
                    ·
                      rfl

theorem cell23_7692733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_7692733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692733 prefixEnd_7692733 := by exact prefixLift 7692733
  have htrace : WordTrace (prefixWord ++ tailWord_7692733) baseStart_7692733 baseEnd_7692733 := by
    simpa [prefixWord, tailWord_7692733, baseEnd_7692733] using wordTrace_append hprefix tailTrace_7692733
  have hstable : (prefixWord ++ tailWord_7692733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692733).length < 2 ^ (prefixWord ++ tailWord_7692733).sum := by decide
  have hdescent : baseEnd_7692733 < baseStart_7692733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692743 : List Nat := [1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_7692743 : Nat := 118140960795 + 7692743 * 2 ^ 59
def prefixEnd_7692743 : Nat := 4983230072969 + 3 ^ 40 * 7692743 * 2
def baseEnd_7692743 : Nat := 3950074710510300841334225

theorem tailTrace_7692743 : CollatzResearch.WordTrace tailWord_7692743 prefixEnd_7692743 3950074710510300841334225 := by
  unfold tailWord_7692743
  simp only [CollatzResearch.WordTrace]
  refine ⟨280577387569513401751282883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187051591713008934500855255 280577387569513401751282883)
  ·
    refine ⟨420866081354270102626924325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280577387569513401751282883 420866081354270102626924325)
    ·
      refine ⟨78912390253925644242548311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420866081354270102626924325 78912390253925644242548311)
      ·
        refine ⟨118368585380888466363822467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78912390253925644242548311 118368585380888466363822467)
        ·
          refine ⟨177552878071332699545733701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118368585380888466363822467 177552878071332699545733701)
          ·
            refine ⟨33291164638374881164825069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177552878071332699545733701 33291164638374881164825069)
            ·
              refine ⟨12484186739390580436809401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33291164638374881164825069 12484186739390580436809401)
              ·
                refine ⟨9363140054542935327607051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12484186739390580436809401 9363140054542935327607051)
                ·
                  refine ⟨14044710081814402991410577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9363140054542935327607051 14044710081814402991410577)
                  ·
                    refine ⟨10533532561360802243557933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14044710081814402991410577 10533532561360802243557933)
                    ·
                      refine ⟨3950074710510300841334225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10533532561360802243557933 3950074710510300841334225)
                      ·
                        rfl

theorem cell23_7692743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_7692743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692743 prefixEnd_7692743 := by exact prefixLift 7692743
  have htrace : WordTrace (prefixWord ++ tailWord_7692743) baseStart_7692743 baseEnd_7692743 := by
    simpa [prefixWord, tailWord_7692743, baseEnd_7692743] using wordTrace_append hprefix tailTrace_7692743
  have hstable : (prefixWord ++ tailWord_7692743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692743).length < 2 ^ (prefixWord ++ tailWord_7692743).sum := by decide
  have hdescent : baseEnd_7692743 < baseStart_7692743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692779 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 4]
def baseStart_7692779 : Nat := 118140960795 + 7692779 * 2 ^ 59
def prefixEnd_7692779 : Nat := 4983230072969 + 3 ^ 40 * 7692779 * 2
def baseEnd_7692779 : Nat := 3950093195813862700484059

theorem tailTrace_7692779 : CollatzResearch.WordTrace tailWord_7692779 prefixEnd_7692779 3950093195813862700484059 := by
  unfold tailWord_7692779
  simp only [CollatzResearch.WordTrace]
  refine ⟨280578700597382979899593391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187052467064921986599728927 280578700597382979899593391)
  ·
    refine ⟨420868050896074469849390087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280578700597382979899593391 420868050896074469849390087)
    ·
      refine ⟨631302076344111704774085131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420868050896074469849390087 631302076344111704774085131)
      ·
        refine ⟨946953114516167557161127697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631302076344111704774085131 946953114516167557161127697)
        ·
          refine ⟨710214835887125667870845773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 946953114516167557161127697 710214835887125667870845773)
          ·
            refine ⟨266330563457672125451567165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 710214835887125667870845773 266330563457672125451567165)
            ·
              refine ⟨99873961296627047044337687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266330563457672125451567165 99873961296627047044337687)
              ·
                refine ⟨149810941944940570566506531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99873961296627047044337687 149810941944940570566506531)
                ·
                  refine ⟨224716412917410855849759797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149810941944940570566506531 224716412917410855849759797)
                  ·
                    refine ⟨21067163711007267735914981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224716412917410855849759797 21067163711007267735914981)
                    ·
                      refine ⟨3950093195813862700484059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21067163711007267735914981 3950093195813862700484059)
                      ·
                        rfl

theorem cell23_7692779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 4].length) (baseStart_7692779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692779 prefixEnd_7692779 := by exact prefixLift 7692779
  have htrace : WordTrace (prefixWord ++ tailWord_7692779) baseStart_7692779 baseEnd_7692779 := by
    simpa [prefixWord, tailWord_7692779, baseEnd_7692779] using wordTrace_append hprefix tailTrace_7692779
  have hstable : (prefixWord ++ tailWord_7692779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692779).length < 2 ^ (prefixWord ++ tailWord_7692779).sum := by decide
  have hdescent : baseEnd_7692779 < baseStart_7692779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692790 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_7692790 : Nat := 118140960795 + 7692790 * 2 ^ 59
def prefixEnd_7692790 : Nat := 4983230072969 + 3 ^ 40 * 7692790 * 2
def baseEnd_7692790 : Nat := 3950098844101062157446509

theorem tailTrace_7692790 : CollatzResearch.WordTrace tailWord_7692790 prefixEnd_7692790 3950098844101062157446509 := by
  unfold tailWord_7692790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17536193862521445548640239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187052734533562085852162549 17536193862521445548640239)
  ·
    refine ⟨26304290793782168322960359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17536193862521445548640239 26304290793782168322960359)
    ·
      refine ⟨39456436190673252484440539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26304290793782168322960359 39456436190673252484440539)
      ·
        refine ⟨59184654286009878726660809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39456436190673252484440539 59184654286009878726660809)
        ·
          refine ⟨44388490714507409044995607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59184654286009878726660809 44388490714507409044995607)
          ·
            refine ⟨66582736071761113567493411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44388490714507409044995607 66582736071761113567493411)
            ·
              refine ⟨99874104107641670351240117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66582736071761113567493411 99874104107641670351240117)
              ·
                refine ⟨9363197260091406595428761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99874104107641670351240117 9363197260091406595428761)
                ·
                  refine ⟨7022397945068554946571571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9363197260091406595428761 7022397945068554946571571)
                  ·
                    refine ⟨10533596917602832419857357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7022397945068554946571571 10533596917602832419857357)
                    ·
                      refine ⟨3950098844101062157446509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10533596917602832419857357 3950098844101062157446509)
                      ·
                        rfl

theorem cell23_7692790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_7692790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692790 prefixEnd_7692790 := by exact prefixLift 7692790
  have htrace : WordTrace (prefixWord ++ tailWord_7692790) baseStart_7692790 baseEnd_7692790 := by
    simpa [prefixWord, tailWord_7692790, baseEnd_7692790] using wordTrace_append hprefix tailTrace_7692790
  have hstable : (prefixWord ++ tailWord_7692790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692790).length < 2 ^ (prefixWord ++ tailWord_7692790).sum := by decide
  have hdescent : baseEnd_7692790 < baseStart_7692790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692819 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 9]
def baseStart_7692819 : Nat := 118140960795 + 7692819 * 2 ^ 59
def prefixEnd_7692819 : Nat := 4983230072969 + 3 ^ 40 * 7692819 * 2
def baseEnd_7692819 : Nat := 438901526115560282664875

theorem tailTrace_7692819 : CollatzResearch.WordTrace tailWord_7692819 prefixEnd_7692819 438901526115560282664875 := by
  unfold tailWord_7692819
  simp only [CollatzResearch.WordTrace]
  refine ⟨280580159517238066731049511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187053439678158711154033007 280580159517238066731049511)
  ·
    refine ⟨420870239275857100096574267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280580159517238066731049511 420870239275857100096574267)
    ·
      refine ⟨631305358913785650144861401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420870239275857100096574267 631305358913785650144861401)
      ·
        refine ⟨473479019185339237608646051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631305358913785650144861401 473479019185339237608646051)
        ·
          refine ⟨710218528778008856412969077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473479019185339237608646051 710218528778008856412969077)
          ·
            refine ⟨66582987072938330288715851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 710218528778008856412969077 66582987072938330288715851)
            ·
              refine ⟨99874480609407495433073777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66582987072938330288715851 99874480609407495433073777)
              ·
                refine ⟨74905860457055621574805333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99874480609407495433073777 74905860457055621574805333)
                ·
                  refine ⟨438901526115560282664875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74905860457055621574805333 438901526115560282664875)
                  ·
                    rfl

theorem cell23_7692819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 9].length) (baseStart_7692819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692819 prefixEnd_7692819 := by exact prefixLift 7692819
  have htrace : WordTrace (prefixWord ++ tailWord_7692819) baseStart_7692819 baseEnd_7692819 := by
    simpa [prefixWord, tailWord_7692819, baseEnd_7692819] using wordTrace_append hprefix tailTrace_7692819
  have hstable : (prefixWord ++ tailWord_7692819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692819).length < 2 ^ (prefixWord ++ tailWord_7692819).sum := by decide
  have hdescent : baseEnd_7692819 < baseStart_7692819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692826 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_7692826 : Nat := 118140960795 + 7692826 * 2 ^ 59
def prefixEnd_7692826 : Nat := 4983230072969 + 3 ^ 40 * 7692826 * 2
def baseEnd_7692826 : Nat := 3950117329404624016596343

theorem tailTrace_7692826 : CollatzResearch.WordTrace tailWord_7692826 prefixEnd_7692826 3950117329404624016596343 := by
  unfold tailWord_7692826
  simp only [CollatzResearch.WordTrace]
  refine ⟨70145103707053176731638583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187053609885475137951036221 70145103707053176731638583)
  ·
    refine ⟨105217655560579765097457875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70145103707053176731638583 105217655560579765097457875)
    ·
      refine ⟨157826483340869647646186813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105217655560579765097457875 157826483340869647646186813)
      ·
        refine ⟨59184931252826117867320055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157826483340869647646186813 59184931252826117867320055)
        ·
          refine ⟨88777396879239176800980083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59184931252826117867320055 88777396879239176800980083)
          ·
            refine ⟨133166095318858765201470125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88777396879239176800980083 133166095318858765201470125)
            ·
              refine ⟨49937285744572036950551297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133166095318858765201470125 49937285744572036950551297)
              ·
                refine ⟨37452964308429027712913473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49937285744572036950551297 37452964308429027712913473)
                ·
                  refine ⟨28089723231321770784685105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37452964308429027712913473 28089723231321770784685105)
                  ·
                    refine ⟨21067292423491328088513829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28089723231321770784685105 21067292423491328088513829)
                    ·
                      refine ⟨3950117329404624016596343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21067292423491328088513829 3950117329404624016596343)
                      ·
                        rfl

theorem cell23_7692826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_7692826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692826 prefixEnd_7692826 := by exact prefixLift 7692826
  have htrace : WordTrace (prefixWord ++ tailWord_7692826) baseStart_7692826 baseEnd_7692826 := by
    simpa [prefixWord, tailWord_7692826, baseEnd_7692826] using wordTrace_append hprefix tailTrace_7692826
  have hstable : (prefixWord ++ tailWord_7692826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692826).length < 2 ^ (prefixWord ++ tailWord_7692826).sum := by decide
  have hdescent : baseEnd_7692826 < baseStart_7692826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692876 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_7692876 : Nat := 118140960795 + 7692876 * 2 ^ 59
def prefixEnd_7692876 : Nat := 4983230072969 + 3 ^ 40 * 7692876 * 2
def baseEnd_7692876 : Nat := 3950143003437348820971113

theorem tailTrace_7692876 : CollatzResearch.WordTrace tailWord_7692876 prefixEnd_7692876 3950143003437348820971113 := by
  unfold tailWord_7692876
  simp only [CollatzResearch.WordTrace]
  refine ⟨140291119239015782732937241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187054825652021043643916321 140291119239015782732937241)
  ·
    refine ⟨105218339429261837049702931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140291119239015782732937241 105218339429261837049702931)
    ·
      refine ⟨157827509143892755574554397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105218339429261837049702931 157827509143892755574554397)
      ·
        refine ⟨59185315928959783340457899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157827509143892755574554397 59185315928959783340457899)
        ·
          refine ⟨88777973893439675010686849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59185315928959783340457899 88777973893439675010686849)
          ·
            refine ⟨66583480420079756258015137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88777973893439675010686849 66583480420079756258015137)
            ·
              refine ⟨49937610315059817193511353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66583480420079756258015137 49937610315059817193511353)
              ·
                refine ⟨37453207736294862895133515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49937610315059817193511353 37453207736294862895133515)
                ·
                  refine ⟨56179811604442294342700273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37453207736294862895133515 56179811604442294342700273)
                  ·
                    refine ⟨42134858703331720757025205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56179811604442294342700273 42134858703331720757025205)
                    ·
                      refine ⟨3950143003437348820971113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42134858703331720757025205 3950143003437348820971113)
                      ·
                        rfl

theorem cell23_7692876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_7692876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692876 prefixEnd_7692876 := by exact prefixLift 7692876
  have htrace : WordTrace (prefixWord ++ tailWord_7692876) baseStart_7692876 baseEnd_7692876 := by
    simpa [prefixWord, tailWord_7692876, baseEnd_7692876] using wordTrace_append hprefix tailTrace_7692876
  have hstable : (prefixWord ++ tailWord_7692876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692876).length < 2 ^ (prefixWord ++ tailWord_7692876).sum := by decide
  have hdescent : baseEnd_7692876 < baseStart_7692876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692898 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7692898 : Nat := 118140960795 + 7692898 * 2 ^ 59
def prefixEnd_7692898 : Nat := 4983230072969 + 3 ^ 40 * 7692898 * 2
def baseEnd_7692898 : Nat := 3950154300011747734896013

theorem tailTrace_7692898 : CollatzResearch.WordTrace tailWord_7692898 prefixEnd_7692898 3950154300011747734896013 := by
  unfold tailWord_7692898
  simp only [CollatzResearch.WordTrace]
  refine ⟨70145760220987965805793837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187055360589301242148783565 70145760220987965805793837)
  ·
    refine ⟨26304660082870487177172689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70145760220987965805793837 26304660082870487177172689)
    ·
      refine ⟨19728495062152865382879517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26304660082870487177172689 19728495062152865382879517)
      ·
        refine ⟨7398185648307324518579819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19728495062152865382879517 7398185648307324518579819)
        ·
          refine ⟨11097278472460986777869729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7398185648307324518579819 11097278472460986777869729)
          ·
            refine ⟨8322958854345740083402297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11097278472460986777869729 8322958854345740083402297)
            ·
              refine ⟨6242219140759305062551723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8322958854345740083402297 6242219140759305062551723)
              ·
                refine ⟨9363328711138957593827585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6242219140759305062551723 9363328711138957593827585)
                ·
                  refine ⟨7022496533354218195370689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9363328711138957593827585 7022496533354218195370689)
                  ·
                    refine ⟨5266872400015663646528017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7022496533354218195370689 5266872400015663646528017)
                    ·
                      refine ⟨3950154300011747734896013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266872400015663646528017 3950154300011747734896013)
                      ·
                        rfl

theorem cell23_7692898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7692898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692898 prefixEnd_7692898 := by exact prefixLift 7692898
  have htrace : WordTrace (prefixWord ++ tailWord_7692898) baseStart_7692898 baseEnd_7692898 := by
    simpa [prefixWord, tailWord_7692898, baseEnd_7692898] using wordTrace_append hprefix tailTrace_7692898
  have hstable : (prefixWord ++ tailWord_7692898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692898).length < 2 ^ (prefixWord ++ tailWord_7692898).sum := by decide
  have hdescent : baseEnd_7692898 < baseStart_7692898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692903 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_7692903 : Nat := 118140960795 + 7692903 * 2 ^ 59
def prefixEnd_7692903 : Nat := 4983230072969 + 3 ^ 40 * 7692903 * 2
def baseEnd_7692903 : Nat := 3950156867415020215333489

theorem tailTrace_7692903 : CollatzResearch.WordTrace tailWord_7692903 prefixEnd_7692903 3950156867415020215333489 := by
  unfold tailWord_7692903
  simp only [CollatzResearch.WordTrace]
  refine ⟨280583223248933749077107363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187055482165955832718071575 280583223248933749077107363)
  ·
    refine ⟨420874834873400623615661045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280583223248933749077107363 420874834873400623615661045)
    ·
      refine ⟨39457015769381308463968223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 420874834873400623615661045 39457015769381308463968223)
      ·
        refine ⟨59185523654071962695952335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39457015769381308463968223 59185523654071962695952335)
        ·
          refine ⟨88778285481107944043928503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59185523654071962695952335 88778285481107944043928503)
          ·
            refine ⟨133167428221661916065892755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88778285481107944043928503 133167428221661916065892755)
            ·
              refine ⟨199751142332492874098839133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133167428221661916065892755 199751142332492874098839133)
              ·
                refine ⟨74906678374684827787064675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199751142332492874098839133 74906678374684827787064675)
                ·
                  refine ⟨112360017562027241680597013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74906678374684827787064675 112360017562027241680597013)
                  ·
                    refine ⟨5266875823220026953777985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112360017562027241680597013 5266875823220026953777985)
                    ·
                      refine ⟨3950156867415020215333489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266875823220026953777985 3950156867415020215333489)
                      ·
                        rfl

theorem cell23_7692903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_7692903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692903 prefixEnd_7692903 := by exact prefixLift 7692903
  have htrace : WordTrace (prefixWord ++ tailWord_7692903) baseStart_7692903 baseEnd_7692903 := by
    simpa [prefixWord, tailWord_7692903, baseEnd_7692903] using wordTrace_append hprefix tailTrace_7692903
  have hstable : (prefixWord ++ tailWord_7692903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692903).length < 2 ^ (prefixWord ++ tailWord_7692903).sum := by decide
  have hdescent : baseEnd_7692903 < baseStart_7692903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692974 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_7692974 : Nat := 118140960795 + 7692974 * 2 ^ 59
def prefixEnd_7692974 : Nat := 4983230072969 + 3 ^ 40 * 7692974 * 2
def baseEnd_7692974 : Nat := 3950193324541489437545663

theorem tailTrace_7692974 : CollatzResearch.WordTrace tailWord_7692974 prefixEnd_7692974 3950193324541489437545663 := by
  unfold tailWord_7692974
  simp only [CollatzResearch.WordTrace]
  refine ⟨35073226603959566025367747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187057208554451018801961317 35073226603959566025367747)
  ·
    refine ⟨52609839905939349038051621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35073226603959566025367747 52609839905939349038051621)
    ·
      refine ⟨9864344982363627944634679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52609839905939349038051621 9864344982363627944634679)
      ·
        refine ⟨14796517473545441916952019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9864344982363627944634679 14796517473545441916952019)
        ·
          refine ⟨22194776210318162875428029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14796517473545441916952019 22194776210318162875428029)
          ·
            refine ⟨8323041078869311078285511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22194776210318162875428029 8323041078869311078285511)
            ·
              refine ⟨12484561618303966617428267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323041078869311078285511 12484561618303966617428267)
              ·
                refine ⟨18726842427455949926142401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12484561618303966617428267 18726842427455949926142401)
                ·
                  refine ⟨14045131820591962444606801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18726842427455949926142401 14045131820591962444606801)
                  ·
                    refine ⟨10533848865443971833455101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14045131820591962444606801 10533848865443971833455101)
                    ·
                      refine ⟨3950193324541489437545663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10533848865443971833455101 3950193324541489437545663)
                      ·
                        rfl

theorem cell23_7692974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_7692974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692974 prefixEnd_7692974 := by exact prefixLift 7692974
  have htrace : WordTrace (prefixWord ++ tailWord_7692974) baseStart_7692974 baseEnd_7692974 := by
    simpa [prefixWord, tailWord_7692974, baseEnd_7692974] using wordTrace_append hprefix tailTrace_7692974
  have hstable : (prefixWord ++ tailWord_7692974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692974).length < 2 ^ (prefixWord ++ tailWord_7692974).sum := by decide
  have hdescent : baseEnd_7692974 < baseStart_7692974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7692990 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_7692990 : Nat := 118140960795 + 7692990 * 2 ^ 59
def prefixEnd_7692990 : Nat := 4983230072969 + 3 ^ 40 * 7692990 * 2
def baseEnd_7692990 : Nat := 1316733846743987124981863

theorem tailTrace_7692990 : CollatzResearch.WordTrace tailWord_7692990 prefixEnd_7692990 1316733846743987124981863 := by
  unfold tailWord_7692990
  simp only [CollatzResearch.WordTrace]
  refine ⟨35073299549952320366940553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187057597599745708623682949 35073299549952320366940553)
  ·
    refine ⟨26304974662464240275205415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35073299549952320366940553 26304974662464240275205415)
    ·
      refine ⟨39457461993696360412808123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26304974662464240275205415 39457461993696360412808123)
      ·
        refine ⟨59186192990544540619212185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39457461993696360412808123 59186192990544540619212185)
        ·
          refine ⟨44389644742908405464409139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59186192990544540619212185 44389644742908405464409139)
          ·
            refine ⟨66584467114362608196613709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44389644742908405464409139 66584467114362608196613709)
            ·
              refine ⟨24969175167885978073730141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66584467114362608196613709 24969175167885978073730141)
              ·
                refine ⟨9363440687957241777648803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24969175167885978073730141 9363440687957241777648803)
                ·
                  refine ⟨14045161031935862666473205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9363440687957241777648803 14045161031935862666473205)
                  ·
                    refine ⟨1316733846743987124981863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14045161031935862666473205 1316733846743987124981863)
                    ·
                      rfl

theorem cell23_7692990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_7692990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7692990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7692990 prefixEnd_7692990 := by exact prefixLift 7692990
  have htrace : WordTrace (prefixWord ++ tailWord_7692990) baseStart_7692990 baseEnd_7692990 := by
    simpa [prefixWord, tailWord_7692990, baseEnd_7692990] using wordTrace_append hprefix tailTrace_7692990
  have hstable : (prefixWord ++ tailWord_7692990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7692990).length < 2 ^ (prefixWord ++ tailWord_7692990).sum := by decide
  have hdescent : baseEnd_7692990 < baseStart_7692990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7692990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693004 : List Nat := [2, 2, 1, 5, 1, 1, 2, 4, 1, 1, 3]
def baseStart_7693004 : Nat := 118140960795 + 7693004 * 2 ^ 59
def prefixEnd_7693004 : Nat := 4983230072969 + 3 ^ 40 * 7693004 * 2
def baseEnd_7693004 : Nat := 3950208728961124320170525

theorem tailTrace_7693004 : CollatzResearch.WordTrace tailWord_7693004 prefixEnd_7693004 3950208728961124320170525 := by
  unfold tailWord_7693004
  simp only [CollatzResearch.WordTrace]
  refine ⟨140293453510783921663267033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187057938014378562217689377 140293453510783921663267033)
  ·
    refine ⟨105220090133087941247450275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140293453510783921663267033 105220090133087941247450275)
    ·
      refine ⟨157830135199631911871175413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105220090133087941247450275 157830135199631911871175413)
      ·
        refine ⟨14796575174965491737922695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157830135199631911871175413 14796575174965491737922695)
        ·
          refine ⟨22194862762448237606884043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14796575174965491737922695 22194862762448237606884043)
          ·
            refine ⟨33292294143672356410326065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22194862762448237606884043 33292294143672356410326065)
            ·
              refine ⟨24969220607754267307744549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33292294143672356410326065 24969220607754267307744549)
              ·
                refine ⟨4681728863953925120202103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24969220607754267307744549 4681728863953925120202103)
                ·
                  refine ⟨7022593295930887680303155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681728863953925120202103 7022593295930887680303155)
                  ·
                    refine ⟨10533889943896331520454733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7022593295930887680303155 10533889943896331520454733)
                    ·
                      refine ⟨3950208728961124320170525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10533889943896331520454733 3950208728961124320170525)
                      ·
                        rfl

theorem cell23_7693004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_7693004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693004 prefixEnd_7693004 := by exact prefixLift 7693004
  have htrace : WordTrace (prefixWord ++ tailWord_7693004) baseStart_7693004 baseEnd_7693004 := by
    simpa [prefixWord, tailWord_7693004, baseEnd_7693004] using wordTrace_append hprefix tailTrace_7693004
  have hstable : (prefixWord ++ tailWord_7693004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693004).length < 2 ^ (prefixWord ++ tailWord_7693004).sum := by decide
  have hdescent : baseEnd_7693004 < baseStart_7693004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693023 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_7693023 : Nat := 118140960795 + 7693023 * 2 ^ 59
def prefixEnd_7693023 : Nat := 4983230072969 + 3 ^ 40 * 7693023 * 2
def baseEnd_7693023 : Nat := 3950218485093559745832937

theorem tailTrace_7693023 : CollatzResearch.WordTrace tailWord_7693023 prefixEnd_7693023 3950218485093559745832937 := by
  unfold tailWord_7693023
  simp only [CollatzResearch.WordTrace]
  refine ⟨280587600008499009571475723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187058400005666006380983815 280587600008499009571475723)
  ·
    refine ⟨420881400012748514357213585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280587600008499009571475723 420881400012748514357213585)
    ·
      refine ⟨315661050009561385767910189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420881400012748514357213585 315661050009561385767910189)
      ·
        refine ⟨118372893753585519662966321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315661050009561385767910189 118372893753585519662966321)
        ·
          refine ⟨88779670315189139747224741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118372893753585519662966321 88779670315189139747224741)
          ·
            refine ⟨16646188184097963702604639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88779670315189139747224741 16646188184097963702604639)
            ·
              refine ⟨24969282276146945553906959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16646188184097963702604639 24969282276146945553906959)
              ·
                refine ⟨37453923414220418330860439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24969282276146945553906959 37453923414220418330860439)
                ·
                  refine ⟨56180885121330627496290659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37453923414220418330860439 56180885121330627496290659)
                  ·
                    refine ⟨84271327681995941244435989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56180885121330627496290659 84271327681995941244435989)
                    ·
                      refine ⟨3950218485093559745832937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84271327681995941244435989 3950218485093559745832937)
                      ·
                        rfl

theorem cell23_7693023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_7693023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693023 prefixEnd_7693023 := by exact prefixLift 7693023
  have htrace : WordTrace (prefixWord ++ tailWord_7693023) baseStart_7693023 baseEnd_7693023 := by
    simpa [prefixWord, tailWord_7693023, baseEnd_7693023] using wordTrace_append hprefix tailTrace_7693023
  have hstable : (prefixWord ++ tailWord_7693023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693023).length < 2 ^ (prefixWord ++ tailWord_7693023).sum := by decide
  have hdescent : baseEnd_7693023 < baseStart_7693023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693027 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 4]
def baseStart_7693027 : Nat := 118140960795 + 7693027 * 2 ^ 59
def prefixEnd_7693027 : Nat := 4983230072969 + 3 ^ 40 * 7693027 * 2
def baseEnd_7693027 : Nat := 3950220539016177730182919

theorem tailTrace_7693027 : CollatzResearch.WordTrace tailWord_7693027 prefixEnd_7693027 3950220539016177730182919 := by
  unfold tailWord_7693027
  simp only [CollatzResearch.WordTrace]
  refine ⟨280587745900484518254621335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187058497266989678836414223 280587745900484518254621335)
  ·
    refine ⟨420881618850726777381932003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280587745900484518254621335 420881618850726777381932003)
    ·
      refine ⟨631322428276090166072898005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420881618850726777381932003 631322428276090166072898005)
      ·
        refine ⟨14796619412720863267333547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 631322428276090166072898005 14796619412720863267333547)
        ·
          refine ⟨22194929119081294901000321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14796619412720863267333547 22194929119081294901000321)
          ·
            refine ⟨16646196839310971175750241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22194929119081294901000321 16646196839310971175750241)
            ·
              refine ⟨12484647629483228381812681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16646196839310971175750241 12484647629483228381812681)
              ·
                refine ⟨9363485722112421286359511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12484647629483228381812681 9363485722112421286359511)
                ·
                  refine ⟨14045228583168631929539267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9363485722112421286359511 14045228583168631929539267)
                  ·
                    refine ⟨21067842874752947894308901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14045228583168631929539267 21067842874752947894308901)
                    ·
                      refine ⟨3950220539016177730182919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21067842874752947894308901 3950220539016177730182919)
                      ·
                        rfl

theorem cell23_7693027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_7693027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693027 prefixEnd_7693027 := by exact prefixLift 7693027
  have htrace : WordTrace (prefixWord ++ tailWord_7693027) baseStart_7693027 baseEnd_7693027 := by
    simpa [prefixWord, tailWord_7693027, baseEnd_7693027] using wordTrace_append hprefix tailTrace_7693027
  have hstable : (prefixWord ++ tailWord_7693027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693027).length < 2 ^ (prefixWord ++ tailWord_7693027).sum := by decide
  have hdescent : baseEnd_7693027 < baseStart_7693027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693033 : List Nat := [1, 2, 1, 1, 1, 2, 8, 7]
def baseStart_7693033 : Nat := 118140960795 + 7693033 * 2 ^ 59
def prefixEnd_7693033 : Nat := 4983230072969 + 3 ^ 40 * 7693033 * 2
def baseEnd_7693033 : Nat := 146304578514818692841033

theorem tailTrace_7693033 : CollatzResearch.WordTrace tailWord_7693033 prefixEnd_7693033 146304578514818692841033 := by
  unfold tailWord_7693033
  simp only [CollatzResearch.WordTrace]
  refine ⟨280587964738462781279339753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187058643158975187519559835 280587964738462781279339753)
  ·
    refine ⟨210440973553847085959504815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280587964738462781279339753 210440973553847085959504815)
    ·
      refine ⟨315661460330770628939257223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210440973553847085959504815 315661460330770628939257223)
      ·
        refine ⟨473492190496155943408885835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315661460330770628939257223 473492190496155943408885835)
        ·
          refine ⟨710238285744233915113328753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473492190496155943408885835 710238285744233915113328753)
          ·
            refine ⟨532678714308175436334996565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710238285744233915113328753 532678714308175436334996565)
            ·
              refine ⟨6242328683298930894550741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 532678714308175436334996565 6242328683298930894550741)
              ·
                refine ⟨146304578514818692841033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6242328683298930894550741 146304578514818692841033)
                ·
                  rfl

theorem cell23_7693033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 7].length) (baseStart_7693033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693033 prefixEnd_7693033 := by exact prefixLift 7693033
  have htrace : WordTrace (prefixWord ++ tailWord_7693033) baseStart_7693033 baseEnd_7693033 := by
    simpa [prefixWord, tailWord_7693033, baseEnd_7693033] using wordTrace_append hprefix tailTrace_7693033
  have hstable : (prefixWord ++ tailWord_7693033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693033).length < 2 ^ (prefixWord ++ tailWord_7693033).sum := by decide
  have hdescent : baseEnd_7693033 < baseStart_7693033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
