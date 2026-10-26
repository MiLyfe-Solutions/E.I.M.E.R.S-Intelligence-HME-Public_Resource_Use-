import V185TrunkScan21Chunk148

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1816892 : List Nat := [2, 2, 2, 2, 1, 2, 2, 5, 3]
def baseStart_1816892 : Nat := 118140960795 + 1816892 * 2 ^ 59
def prefixEnd_1816892 : Nat := 4983230072969 + 3 ^ 40 * 1816892 * 2
def baseEnd_1816892 : Nat := 414639508137249171286343

theorem tailTrace_1816892 : CollatzResearch.WordTrace tailWord_1816892 prefixEnd_1816892 414639508137249171286343 := by
  unfold tailWord_1816892
  simp only [CollatzResearch.WordTrace]
  refine ⟨33133747666859029647214465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44178330222478706196285953 33133747666859029647214465)
  ·
    refine ⟨24850310750144272235410849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33133747666859029647214465 24850310750144272235410849)
    ·
      refine ⟨18637733062608204176558137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24850310750144272235410849 18637733062608204176558137)
      ·
        refine ⟨13978299796956153132418603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18637733062608204176558137 13978299796956153132418603)
        ·
          refine ⟨20967449695434229698627905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13978299796956153132418603 20967449695434229698627905)
          ·
            refine ⟨15725587271575672273970929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20967449695434229698627905 15725587271575672273970929)
            ·
              refine ⟨11794190453681754205478197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15725587271575672273970929 11794190453681754205478197)
              ·
                refine ⟨1105705355032664456763581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11794190453681754205478197 1105705355032664456763581)
                ·
                  refine ⟨414639508137249171286343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1105705355032664456763581 414639508137249171286343)
                  ·
                    rfl

theorem cell21_1816892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_1816892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816892 prefixEnd_1816892 := by exact prefixLift 1816892
  have htrace : WordTrace (prefixWord ++ tailWord_1816892) baseStart_1816892 baseEnd_1816892 := by
    simpa [prefixWord, tailWord_1816892, baseEnd_1816892] using wordTrace_append hprefix tailTrace_1816892
  have hstable : (prefixWord ++ tailWord_1816892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816892).length < 2 ^ (prefixWord ++ tailWord_1816892).sum := by decide
  have hdescent : baseEnd_1816892 < baseStart_1816892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1816968 : List Nat := [2, 1, 3, 3, 1, 1, 1, 6, 3]
def baseStart_1816968 : Nat := 118140960795 + 1816968 * 2 ^ 59
def prefixEnd_1816968 : Nat := 4983230072969 + 3 ^ 40 * 1816968 * 2
def baseEnd_1816968 : Nat := 414656852372689928019521

theorem tailTrace_1816968 : CollatzResearch.WordTrace tailWord_1816968 prefixEnd_1816968 414656852372689928019521 := by
  unfold tailWord_1816968
  simp only [CollatzResearch.WordTrace]
  refine ⟨33135133640721362137097779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44180178187628482849463705 33135133640721362137097779)
  ·
    refine ⟨49702700461082043205646669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33135133640721362137097779 49702700461082043205646669)
    ·
      refine ⟨18638512672905766202117501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49702700461082043205646669 18638512672905766202117501)
      ·
        refine ⟨6989442252339662325794063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18638512672905766202117501 6989442252339662325794063)
        ·
          refine ⟨10484163378509493488691095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989442252339662325794063 10484163378509493488691095)
          ·
            refine ⟨15726245067764240233036643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10484163378509493488691095 15726245067764240233036643)
            ·
              refine ⟨23589367601646360349554965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15726245067764240233036643 23589367601646360349554965)
              ·
                refine ⟨1105751606327173141385389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23589367601646360349554965 1105751606327173141385389)
                ·
                  refine ⟨414656852372689928019521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1105751606327173141385389 414656852372689928019521)
                  ·
                    rfl

theorem cell21_1816968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_1816968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1816968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1816968 prefixEnd_1816968 := by exact prefixLift 1816968
  have htrace : WordTrace (prefixWord ++ tailWord_1816968) baseStart_1816968 baseEnd_1816968 := by
    simpa [prefixWord, tailWord_1816968, baseEnd_1816968] using wordTrace_append hprefix tailTrace_1816968
  have hstable : (prefixWord ++ tailWord_1816968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1816968).length < 2 ^ (prefixWord ++ tailWord_1816968).sum := by decide
  have hdescent : baseEnd_1816968 < baseStart_1816968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1816968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817013 : List Nat := [1, 3, 3, 2, 3, 2, 7]
def baseStart_1817013 : Nat := 118140960795 + 1817013 * 2 ^ 59
def prefixEnd_1817013 : Nat := 4983230072969 + 3 ^ 40 * 1817013 * 2
def baseEnd_1817013 : Nat := 46074124665086649974381

theorem tailTrace_1817013 : CollatzResearch.WordTrace tailWord_1817013 prefixEnd_1817013 46074124665086649974381 := by
  unfold tailWord_1817013
  simp only [CollatzResearch.WordTrace]
  refine ⟨66271908566279696959583693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44181272377519797973055795 66271908566279696959583693)
  ·
    refine ⟨24851965712354886359843885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66271908566279696959583693 24851965712354886359843885)
    ·
      refine ⟨9319487142133082384941457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24851965712354886359843885 9319487142133082384941457)
      ·
        refine ⟨6989615356599811788706093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9319487142133082384941457 6989615356599811788706093)
        ·
          refine ⟨2621105758724929420764785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6989615356599811788706093 2621105758724929420764785)
          ·
            refine ⟨1965829319043697065573589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2621105758724929420764785 1965829319043697065573589)
            ·
              refine ⟨46074124665086649974381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1965829319043697065573589 46074124665086649974381)
              ·
                rfl

theorem cell21_1817013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 7].length) (baseStart_1817013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817013 prefixEnd_1817013 := by exact prefixLift 1817013
  have htrace : WordTrace (prefixWord ++ tailWord_1817013) baseStart_1817013 baseEnd_1817013 := by
    simpa [prefixWord, tailWord_1817013, baseEnd_1817013] using wordTrace_append hprefix tailTrace_1817013
  have hstable : (prefixWord ++ tailWord_1817013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817013).length < 2 ^ (prefixWord ++ tailWord_1817013).sum := by decide
  have hdescent : baseEnd_1817013 < baseStart_1817013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817089 : List Nat := [1, 2, 4, 1, 3, 3, 1, 6]
def baseStart_1817089 : Nat := 118140960795 + 1817089 * 2 ^ 59
def prefixEnd_1817089 : Nat := 4983230072969 + 3 ^ 40 * 1817089 * 2
def baseEnd_1817089 : Nat := 138228155407073535500869

theorem tailTrace_1817089 : CollatzResearch.WordTrace tailWord_1817089 prefixEnd_1817089 138228155407073535500869 := by
  unfold tailWord_1817089
  simp only [CollatzResearch.WordTrace]
  refine ⟨66274680514004361939350321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44183120342669574626233547 66274680514004361939350321)
  ·
    refine ⟨49706010385503271454512741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66274680514004361939350321 49706010385503271454512741)
    ·
      refine ⟨9319876947281863397721139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49706010385503271454512741 9319876947281863397721139)
      ·
        refine ⟨13979815420922795096581709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9319876947281863397721139 13979815420922795096581709)
        ·
          refine ⟨5242430782846048161218141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13979815420922795096581709 5242430782846048161218141)
          ·
            refine ⟨1965911543567268060456803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5242430782846048161218141 1965911543567268060456803)
            ·
              refine ⟨2948867315350902090685205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965911543567268060456803 2948867315350902090685205)
              ·
                refine ⟨138228155407073535500869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2948867315350902090685205 138228155407073535500869)
                ·
                  rfl

theorem cell21_1817089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 6].length) (baseStart_1817089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817089 prefixEnd_1817089 := by exact prefixLift 1817089
  have htrace : WordTrace (prefixWord ++ tailWord_1817089) baseStart_1817089 baseEnd_1817089 := by
    simpa [prefixWord, tailWord_1817089, baseEnd_1817089] using wordTrace_append hprefix tailTrace_1817089
  have hstable : (prefixWord ++ tailWord_1817089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817089).length < 2 ^ (prefixWord ++ tailWord_1817089).sum := by decide
  have hdescent : baseEnd_1817089 < baseStart_1817089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817165 : List Nat := [1, 6, 1, 1, 2, 2, 1, 7]
def baseStart_1817165 : Nat := 118140960795 + 1817165 * 2 ^ 59
def prefixEnd_1817165 : Nat := 4983230072969 + 3 ^ 40 * 1817165 * 2
def baseEnd_1817165 : Nat := 138233936818887121078595

theorem tailTrace_1817165 : CollatzResearch.WordTrace tailWord_1817165 prefixEnd_1817165 138233936818887121078595 := by
  unfold tailWord_1817165
  simp only [CollatzResearch.WordTrace]
  refine ⟨66277452461729026919116949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44184968307819351279411299 66277452461729026919116949)
  ·
    refine ⟨3106755584143548136833607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66277452461729026919116949 3106755584143548136833607)
    ·
      refine ⟨4660133376215322205250411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3106755584143548136833607 4660133376215322205250411)
      ·
        refine ⟨6990200064322983307875617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660133376215322205250411 6990200064322983307875617)
        ·
          refine ⟨5242650048242237480906713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6990200064322983307875617 5242650048242237480906713)
          ·
            refine ⟨3931987536181678110680035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5242650048242237480906713 3931987536181678110680035)
            ·
              refine ⟨5897981304272517166020053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3931987536181678110680035 5897981304272517166020053)
              ·
                refine ⟨138233936818887121078595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5897981304272517166020053 138233936818887121078595)
                ·
                  rfl

theorem cell21_1817165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 7].length) (baseStart_1817165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817165 prefixEnd_1817165 := by exact prefixLift 1817165
  have htrace : WordTrace (prefixWord ++ tailWord_1817165) baseStart_1817165 baseEnd_1817165 := by
    simpa [prefixWord, tailWord_1817165, baseEnd_1817165] using wordTrace_append hprefix tailTrace_1817165
  have hstable : (prefixWord ++ tailWord_1817165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817165).length < 2 ^ (prefixWord ++ tailWord_1817165).sum := by decide
  have hdescent : baseEnd_1817165 < baseStart_1817165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817193 : List Nat := [1, 2, 1, 1, 1, 4, 1, 6, 4]
def baseStart_1817193 : Nat := 118140960795 + 1817193 * 2 ^ 59
def prefixEnd_1817193 : Nat := 4983230072969 + 3 ^ 40 * 1817193 * 2
def baseEnd_1817193 : Nat := 414708200438139536769061

theorem tailTrace_1817193 : CollatzResearch.WordTrace tailWord_1817193 prefixEnd_1817193 414708200438139536769061 := by
  unfold tailWord_1817193
  simp only [CollatzResearch.WordTrace]
  refine ⟨66278473705627587701136233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44185649137085058467424155 66278473705627587701136233)
  ·
    refine ⟨49708855279220690775852175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66278473705627587701136233 49708855279220690775852175)
    ·
      refine ⟨74563282918831036163778263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49708855279220690775852175 74563282918831036163778263)
      ·
        refine ⟨111844924378246554245667395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74563282918831036163778263 111844924378246554245667395)
        ·
          refine ⟨167767386567369831368501093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111844924378246554245667395 167767386567369831368501093)
          ·
            refine ⟨31456384981381843381593955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167767386567369831368501093 31456384981381843381593955)
            ·
              refine ⟨47184577472072765072390933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31456384981381843381593955 47184577472072765072390933)
              ·
                refine ⟨2211777069003410862768325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47184577472072765072390933 2211777069003410862768325)
                ·
                  refine ⟨414708200438139536769061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2211777069003410862768325 414708200438139536769061)
                  ·
                    rfl

theorem cell21_1817193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_1817193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817193 prefixEnd_1817193 := by exact prefixLift 1817193
  have htrace : WordTrace (prefixWord ++ tailWord_1817193) baseStart_1817193 baseEnd_1817193 := by
    simpa [prefixWord, tailWord_1817193, baseEnd_1817193] using wordTrace_append hprefix tailTrace_1817193
  have hstable : (prefixWord ++ tailWord_1817193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817193).length < 2 ^ (prefixWord ++ tailWord_1817193).sum := by decide
  have hdescent : baseEnd_1817193 < baseStart_1817193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817207 : List Nat := [1, 1, 3, 1, 1, 3, 3, 8]
def baseStart_1817207 : Nat := 118140960795 + 1817207 * 2 ^ 59
def prefixEnd_1817207 : Nat := 4983230072969 + 3 ^ 40 * 1817207 * 2
def baseEnd_1817207 : Nat := 138237131809626207845233

theorem tailTrace_1817207 : CollatzResearch.WordTrace tailWord_1817207 prefixEnd_1817207 138237131809626207845233 := by
  unfold tailWord_1817207
  simp only [CollatzResearch.WordTrace]
  refine ⟨66278984327576868092145875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44185989551717912061430583 66278984327576868092145875)
  ·
    refine ⟨99418476491365302138218813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66278984327576868092145875 99418476491365302138218813)
    ·
      refine ⟨37281928684261988301832055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99418476491365302138218813 37281928684261988301832055)
      ·
        refine ⟨55922893026392982452748083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37281928684261988301832055 55922893026392982452748083)
        ·
          refine ⟨83884339539589473679122125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55922893026392982452748083 83884339539589473679122125)
          ·
            refine ⟨31456627327346052629670797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83884339539589473679122125 31456627327346052629670797)
            ·
              refine ⟨11796235247754769736126549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31456627327346052629670797 11796235247754769736126549)
              ·
                refine ⟨138237131809626207845233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11796235247754769736126549 138237131809626207845233)
                ·
                  rfl

theorem cell21_1817207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 8].length) (baseStart_1817207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817207 prefixEnd_1817207 := by exact prefixLift 1817207
  have htrace : WordTrace (prefixWord ++ tailWord_1817207) baseStart_1817207 baseEnd_1817207 := by
    simpa [prefixWord, tailWord_1817207, baseEnd_1817207] using wordTrace_append hprefix tailTrace_1817207
  have hstable : (prefixWord ++ tailWord_1817207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817207).length < 2 ^ (prefixWord ++ tailWord_1817207).sum := by decide
  have hdescent : baseEnd_1817207 < baseStart_1817207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817376 : List Nat := [2, 1, 1, 5, 1, 3, 2, 6]
def baseStart_1817376 : Nat := 118140960795 + 1817376 * 2 ^ 59
def prefixEnd_1817376 : Nat := 4983230072969 + 3 ^ 40 * 1817376 * 2
def baseEnd_1817376 : Nat := 138249987843790628406229

theorem tailTrace_1817376 : CollatzResearch.WordTrace tailWord_1817376 prefixEnd_1817376 138249987843790628406229 := by
  unfold tailWord_1817376
  simp only [CollatzResearch.WordTrace]
  refine ⟨33142574131982304977523991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44190098842643073303365321 33142574131982304977523991)
  ·
    refine ⟨49713861197973457466285987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33142574131982304977523991 49713861197973457466285987)
    ·
      refine ⟨74570791796960186199428981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49713861197973457466285987 74570791796960186199428981)
      ·
        refine ⟨6991011730965017456196467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74570791796960186199428981 6991011730965017456196467)
        ·
          refine ⟨10486517596447526184294701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6991011730965017456196467 10486517596447526184294701)
          ·
            refine ⟨3932444098667822319110513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10486517596447526184294701 3932444098667822319110513)
            ·
              refine ⟨2949333074000866739332885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3932444098667822319110513 2949333074000866739332885)
              ·
                refine ⟨138249987843790628406229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2949333074000866739332885 138249987843790628406229)
                ·
                  rfl

theorem cell21_1817376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 6].length) (baseStart_1817376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817376 prefixEnd_1817376 := by exact prefixLift 1817376
  have htrace : WordTrace (prefixWord ++ tailWord_1817376) baseStart_1817376 baseEnd_1817376 := by
    simpa [prefixWord, tailWord_1817376, baseEnd_1817376] using wordTrace_append hprefix tailTrace_1817376
  have hstable : (prefixWord ++ tailWord_1817376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817376).length < 2 ^ (prefixWord ++ tailWord_1817376).sum := by decide
  have hdescent : baseEnd_1817376 < baseStart_1817376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817424 : List Nat := [2, 1, 1, 1, 1, 4, 6, 2, 3]
def baseStart_1817424 : Nat := 118140960795 + 1817424 * 2 ^ 59
def prefixEnd_1817424 : Nat := 4983230072969 + 3 ^ 40 * 1817424 * 2
def baseEnd_1817424 : Nat := 414760917785334468418589

theorem tailTrace_1817424 : CollatzResearch.WordTrace tailWord_1817424 prefixEnd_1817424 414760917785334468418589 := by
  unfold tailWord_1817424
  simp only [CollatzResearch.WordTrace]
  refine ⟨33143449483895357076397663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44191265978527142768530217 33143449483895357076397663)
  ·
    refine ⟨49715174225843035614596495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33143449483895357076397663 49715174225843035614596495)
    ·
      refine ⟨74572761338764553421894743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49715174225843035614596495 74572761338764553421894743)
      ·
        refine ⟨111859142008146830132842115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74572761338764553421894743 111859142008146830132842115)
        ·
          refine ⟨167788713012220245199263173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111859142008146830132842115 167788713012220245199263173)
          ·
            refine ⟨31460383689791295974861845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167788713012220245199263173 31460383689791295974861845)
            ·
              refine ⟨1474705485458966998821649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31460383689791295974861845 1474705485458966998821649)
              ·
                refine ⟨1106029114094225249116237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474705485458966998821649 1106029114094225249116237)
                ·
                  refine ⟨414760917785334468418589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106029114094225249116237 414760917785334468418589)
                  ·
                    rfl

theorem cell21_1817424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 3].length) (baseStart_1817424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817424 prefixEnd_1817424 := by exact prefixLift 1817424
  have htrace : WordTrace (prefixWord ++ tailWord_1817424) baseStart_1817424 baseEnd_1817424 := by
    simpa [prefixWord, tailWord_1817424, baseEnd_1817424] using wordTrace_append hprefix tailTrace_1817424
  have hstable : (prefixWord ++ tailWord_1817424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817424).length < 2 ^ (prefixWord ++ tailWord_1817424).sum := by decide
  have hdescent : baseEnd_1817424 < baseStart_1817424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817452 : List Nat := [2, 2, 1, 1, 4, 1, 5, 5]
def baseStart_1817452 : Nat := 118140960795 + 1817452 * 2 ^ 59
def prefixEnd_1817452 : Nat := 4983230072969 + 3 ^ 40 * 1817452 * 2
def baseEnd_1817452 : Nat := 138255769255604213983955

theorem tailTrace_1817452 : CollatzResearch.WordTrace tailWord_1817452 prefixEnd_1817452 138255769255604213983955 := by
  unfold tailWord_1817452
  simp only [CollatzResearch.WordTrace]
  refine ⟨33143960105844637467407305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44191946807792849956543073 33143960105844637467407305)
  ·
    refine ⟨24857970079383478100555479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33143960105844637467407305 24857970079383478100555479)
    ·
      refine ⟨37286955119075217150833219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24857970079383478100555479 37286955119075217150833219)
      ·
        refine ⟨55930432678612825726249829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37286955119075217150833219 55930432678612825726249829)
        ·
          refine ⟨10486956127239904823671843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55930432678612825726249829 10486956127239904823671843)
          ·
            refine ⟨15730434190859857235507765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10486956127239904823671843 15730434190859857235507765)
            ·
              refine ⟨1474728205393111615828853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15730434190859857235507765 1474728205393111615828853)
              ·
                refine ⟨138255769255604213983955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1474728205393111615828853 138255769255604213983955)
                ·
                  rfl

theorem cell21_1817452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 5].length) (baseStart_1817452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817452 prefixEnd_1817452 := by exact prefixLift 1817452
  have htrace : WordTrace (prefixWord ++ tailWord_1817452) baseStart_1817452 baseEnd_1817452 := by
    simpa [prefixWord, tailWord_1817452, baseEnd_1817452] using wordTrace_append hprefix tailTrace_1817452
  have hstable : (prefixWord ++ tailWord_1817452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817452).length < 2 ^ (prefixWord ++ tailWord_1817452).sum := by decide
  have hdescent : baseEnd_1817452 < baseStart_1817452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817483 : List Nat := [1, 1, 1, 1, 4, 2, 4, 4, 3]
def baseStart_1817483 : Nat := 118140960795 + 1817483 * 2 ^ 59
def prefixEnd_1817483 : Nat := 4983230072969 + 3 ^ 40 * 1817483 * 2
def baseEnd_1817483 : Nat := 414774382389163476935135

theorem tailTrace_1817483 : CollatzResearch.WordTrace tailWord_1817483 prefixEnd_1817483 414774382389163476935135 := by
  unfold tailWord_1817483
  simp only [CollatzResearch.WordTrace]
  refine ⟨66289050874576967229193103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44192700583051311486128735 66289050874576967229193103)
  ·
    refine ⟨99433576311865450843789655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66289050874576967229193103 99433576311865450843789655)
    ·
      refine ⟨149150364467798176265684483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99433576311865450843789655 149150364467798176265684483)
      ·
        refine ⟨223725546701697264398526725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149150364467798176265684483 223725546701697264398526725)
        ·
          refine ⟨41948540006568237074723761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223725546701697264398526725 41948540006568237074723761)
          ·
            refine ⟨31461405004926177806042821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41948540006568237074723761 31461405004926177806042821)
            ·
              refine ⟨5899013438423658338633029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31461405004926177806042821 5899013438423658338633029)
              ·
                refine ⟨1106065019704435938493693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5899013438423658338633029 1106065019704435938493693)
                ·
                  refine ⟨414774382389163476935135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106065019704435938493693 414774382389163476935135)
                  ·
                    rfl

theorem cell21_1817483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 4, 3].length) (baseStart_1817483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817483 prefixEnd_1817483 := by exact prefixLift 1817483
  have htrace : WordTrace (prefixWord ++ tailWord_1817483) baseStart_1817483 baseEnd_1817483 := by
    simpa [prefixWord, tailWord_1817483, baseEnd_1817483] using wordTrace_append hprefix tailTrace_1817483
  have hstable : (prefixWord ++ tailWord_1817483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817483).length < 2 ^ (prefixWord ++ tailWord_1817483).sum := by decide
  have hdescent : baseEnd_1817483 < baseStart_1817483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817590 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1817590 : Nat := 118140960795 + 1817590 * 2 ^ 59
def prefixEnd_1817590 : Nat := 4983230072969 + 3 ^ 40 * 1817590 * 2
def baseEnd_1817590 : Nat := 414798801246955068651583

theorem tailTrace_1817590 : CollatzResearch.WordTrace tailWord_1817590 prefixEnd_1817590 414798801246955068651583 := by
  unfold tailWord_1817590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143309592824332781458639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44195302323459549668892149 4143309592824332781458639)
  ·
    refine ⟨6214964389236499172187959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4143309592824332781458639 6214964389236499172187959)
    ·
      refine ⟨9322446583854748758281939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6214964389236499172187959 9322446583854748758281939)
      ·
        refine ⟨13983669875782123137422909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9322446583854748758281939 13983669875782123137422909)
        ·
          refine ⟨5243876203418296176533591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13983669875782123137422909 5243876203418296176533591)
          ·
            refine ⟨7865814305127444264800387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5243876203418296176533591 7865814305127444264800387)
            ·
              refine ⟨11798721457691166397200581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7865814305127444264800387 11798721457691166397200581)
              ·
                refine ⟨2212260273317093699475109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11798721457691166397200581 2212260273317093699475109)
                ·
                  refine ⟨414798801246955068651583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212260273317093699475109 414798801246955068651583)
                  ·
                    rfl

theorem cell21_1817590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1817590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817590 prefixEnd_1817590 := by exact prefixLift 1817590
  have htrace : WordTrace (prefixWord ++ tailWord_1817590) baseStart_1817590 baseEnd_1817590 := by
    simpa [prefixWord, tailWord_1817590, baseEnd_1817590] using wordTrace_append hprefix tailTrace_1817590
  have hstable : (prefixWord ++ tailWord_1817590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817590).length < 2 ^ (prefixWord ++ tailWord_1817590).sum := by decide
  have hdescent : baseEnd_1817590 < baseStart_1817590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817635 : List Nat := [1, 1, 1, 4, 3, 2, 1, 5, 3]
def baseStart_1817635 : Nat := 118140960795 + 1817635 * 2 ^ 59
def prefixEnd_1817635 : Nat := 4983230072969 + 3 ^ 40 * 1817635 * 2
def baseEnd_1817635 : Nat := 414809070860044990401491

theorem tailTrace_1817635 : CollatzResearch.WordTrace tailWord_1817635 prefixEnd_1817635 414809070860044990401491 := by
  unfold tailWord_1817635
  simp only [CollatzResearch.WordTrace]
  refine ⟨66294594770026297188726359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44196396513350864792484239 66294594770026297188726359)
  ·
    refine ⟨99441892155039445783089539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66294594770026297188726359 99441892155039445783089539)
    ·
      refine ⟨149162838232559168674634309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99441892155039445783089539 149162838232559168674634309)
      ·
        refine ⟨27968032168604844126493933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149162838232559168674634309 27968032168604844126493933)
        ·
          refine ⟨10488012063226816547435225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27968032168604844126493933 10488012063226816547435225)
          ·
            refine ⟨7866009047420112410576419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10488012063226816547435225 7866009047420112410576419)
            ·
              refine ⟨11799013571130168615864629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7866009047420112410576419 11799013571130168615864629)
              ·
                refine ⟨1106157522293453307737309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11799013571130168615864629 1106157522293453307737309)
                ·
                  refine ⟨414809070860044990401491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106157522293453307737309 414809070860044990401491)
                  ·
                    rfl

theorem cell21_1817635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 3].length) (baseStart_1817635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817635 prefixEnd_1817635 := by exact prefixLift 1817635
  have htrace : WordTrace (prefixWord ++ tailWord_1817635) baseStart_1817635 baseEnd_1817635 := by
    simpa [prefixWord, tailWord_1817635, baseEnd_1817635] using wordTrace_append hprefix tailTrace_1817635
  have hstable : (prefixWord ++ tailWord_1817635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817635).length < 2 ^ (prefixWord ++ tailWord_1817635).sum := by decide
  have hdescent : baseEnd_1817635 < baseStart_1817635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817652 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1817652 : Nat := 118140960795 + 1817652 * 2 ^ 59
def prefixEnd_1817652 : Nat := 4983230072969 + 3 ^ 40 * 1817652 * 2
def baseEnd_1817652 : Nat := 414812950491656738618123

theorem tailTrace_1817652 : CollatzResearch.WordTrace tailWord_1817652 prefixEnd_1817652 414812950491656738618123 := by
  unfold tailWord_1817652
  simp only [CollatzResearch.WordTrace]
  refine ⟨33147607405482354546047605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44196809873976472728063473 33147607405482354546047605)
  ·
    refine ⟨3107588194263970738691963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33147607405482354546047605 3107588194263970738691963)
    ·
      refine ⟨4661382291395956108037945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3107588194263970738691963 4661382291395956108037945)
      ·
        refine ⟨3496036718546967081028459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4661382291395956108037945 3496036718546967081028459)
        ·
          refine ⟨5244055077820450621542689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496036718546967081028459 5244055077820450621542689)
          ·
            refine ⟨3933041308365337966157017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5244055077820450621542689 3933041308365337966157017)
            ·
              refine ⟨2949780981274003474617763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3933041308365337966157017 2949780981274003474617763)
              ·
                refine ⟨4424671471911005211926645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2949780981274003474617763 4424671471911005211926645)
                ·
                  refine ⟨414812950491656738618123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4424671471911005211926645 414812950491656738618123)
                  ·
                    rfl

theorem cell21_1817652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1817652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817652 prefixEnd_1817652 := by exact prefixLift 1817652
  have htrace : WordTrace (prefixWord ++ tailWord_1817652) baseStart_1817652 baseEnd_1817652 := by
    simpa [prefixWord, tailWord_1817652, baseEnd_1817652] using wordTrace_append hprefix tailTrace_1817652
  have hstable : (prefixWord ++ tailWord_1817652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817652).length < 2 ^ (prefixWord ++ tailWord_1817652).sum := by decide
  have hdescent : baseEnd_1817652 < baseStart_1817652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817708 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 6]
def baseStart_1817708 : Nat := 118140960795 + 1817708 * 2 ^ 59
def prefixEnd_1817708 : Nat := 4983230072969 + 3 ^ 40 * 1817708 * 2
def baseEnd_1817708 : Nat := 414825730454613085684675

theorem tailTrace_1817708 : CollatzResearch.WordTrace tailWord_1817708 prefixEnd_1817708 414825730454613085684675 := by
  unfold tailWord_1817708
  simp only [CollatzResearch.WordTrace]
  refine ⟨33148628649380915328066889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44198171532507887104089185 33148628649380915328066889)
  ·
    refine ⟨24861471487035686496050167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33148628649380915328066889 24861471487035686496050167)
    ·
      refine ⟨37292207230553529744075251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24861471487035686496050167 37292207230553529744075251)
      ·
        refine ⟨55938310845830294616112877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37292207230553529744075251 55938310845830294616112877)
        ·
          refine ⟨20976866567186360481042329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55938310845830294616112877 20976866567186360481042329)
          ·
            refine ⟨15732649925389770360781747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20976866567186360481042329 15732649925389770360781747)
            ·
              refine ⟨23598974888084655541172621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15732649925389770360781747 23598974888084655541172621)
              ·
                refine ⟨8849615583031745827939733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23598974888084655541172621 8849615583031745827939733)
                ·
                  refine ⟨414825730454613085684675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8849615583031745827939733 414825730454613085684675)
                  ·
                    rfl

theorem cell21_1817708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_1817708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817708 prefixEnd_1817708 := by exact prefixLift 1817708
  have htrace : WordTrace (prefixWord ++ tailWord_1817708) baseStart_1817708 baseEnd_1817708 := by
    simpa [prefixWord, tailWord_1817708, baseEnd_1817708] using wordTrace_append hprefix tailTrace_1817708
  have hstable : (prefixWord ++ tailWord_1817708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817708).length < 2 ^ (prefixWord ++ tailWord_1817708).sum := by decide
  have hdescent : baseEnd_1817708 < baseStart_1817708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817717 : List Nat := [1, 3, 4, 3, 2, 1, 2, 1, 4]
def baseStart_1817717 : Nat := 118140960795 + 1817717 * 2 ^ 59
def prefixEnd_1817717 : Nat := 4983230072969 + 3 ^ 40 * 1817717 * 2
def baseEnd_1817717 : Nat := 414827784377231070034657

theorem tailTrace_1817717 : CollatzResearch.WordTrace tailWord_1817717 prefixEnd_1817717 414827784377231070034657 := by
  unfold tailWord_1817717
  simp only [CollatzResearch.WordTrace]
  refine ⟨66297585555729225193211405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44198390370486150128807603 66297585555729225193211405)
  ·
    refine ⟨24861594583398459447454277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66297585555729225193211405 24861594583398459447454277)
    ·
      refine ⟨4661548984387211146397677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24861594583398459447454277 4661548984387211146397677)
      ·
        refine ⟨1748080869145204179899129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4661548984387211146397677 1748080869145204179899129)
        ·
          refine ⟨1311060651858903134924347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748080869145204179899129 1311060651858903134924347)
          ·
            refine ⟨1966590977788354702386521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311060651858903134924347 1966590977788354702386521)
            ·
              refine ⟨1474943233341266026789891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966590977788354702386521 1474943233341266026789891)
              ·
                refine ⟨2212414850011899040184837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474943233341266026789891 2212414850011899040184837)
                ·
                  refine ⟨414827784377231070034657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212414850011899040184837 414827784377231070034657)
                  ·
                    rfl

theorem cell21_1817717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_1817717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817717 prefixEnd_1817717 := by exact prefixLift 1817717
  have htrace : WordTrace (prefixWord ++ tailWord_1817717) baseStart_1817717 baseEnd_1817717 := by
    simpa [prefixWord, tailWord_1817717, baseEnd_1817717] using wordTrace_append hprefix tailTrace_1817717
  have hstable : (prefixWord ++ tailWord_1817717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817717).length < 2 ^ (prefixWord ++ tailWord_1817717).sum := by decide
  have hdescent : baseEnd_1817717 < baseStart_1817717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817725 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 4]
def baseStart_1817725 : Nat := 118140960795 + 1817725 * 2 ^ 59
def prefixEnd_1817725 : Nat := 4983230072969 + 3 ^ 40 * 1817725 * 2
def baseEnd_1817725 : Nat := 414829610086224833901307

theorem tailTrace_1817725 : CollatzResearch.WordTrace tailWord_1817725 prefixEnd_1817725 414829610086224833901307 := by
  unfold tailWord_1817725
  simp only [CollatzResearch.WordTrace]
  refine ⟨66297877339700242559502629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44198584893133495039668419 66297877339700242559502629)
  ·
    refine ⟨12430852001193795479906743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66297877339700242559502629 12430852001193795479906743)
    ·
      refine ⟨18646278001790693219860115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12430852001193795479906743 18646278001790693219860115)
      ·
        refine ⟨27969417002686039829790173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18646278001790693219860115 27969417002686039829790173)
        ·
          refine ⟨10488531376007264936171315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27969417002686039829790173 10488531376007264936171315)
          ·
            refine ⟨15732797064010897404256973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10488531376007264936171315 15732797064010897404256973)
            ·
              refine ⟨5899798899004086526596365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15732797064010897404256973 5899798899004086526596365)
              ·
                refine ⟨2212424587126532447473637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5899798899004086526596365 2212424587126532447473637)
                ·
                  refine ⟨414829610086224833901307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212424587126532447473637 414829610086224833901307)
                  ·
                    rfl

theorem cell21_1817725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_1817725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817725 prefixEnd_1817725 := by exact prefixLift 1817725
  have htrace : WordTrace (prefixWord ++ tailWord_1817725) baseStart_1817725 baseEnd_1817725 := by
    simpa [prefixWord, tailWord_1817725, baseEnd_1817725] using wordTrace_append hprefix tailTrace_1817725
  have hstable : (prefixWord ++ tailWord_1817725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817725).length < 2 ^ (prefixWord ++ tailWord_1817725).sum := by decide
  have hdescent : baseEnd_1817725 < baseStart_1817725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817762 : List Nat := [3, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1817762 : Nat := 118140960795 + 1817762 * 2 ^ 59
def prefixEnd_1817762 : Nat := 4983230072969 + 3 ^ 40 * 1817762 * 2
def baseEnd_1817762 : Nat := 414838053990320991784565

theorem tailTrace_1817762 : CollatzResearch.WordTrace tailWord_1817762 prefixEnd_1817762 414838053990320991784565 := by
  unfold tailWord_1817762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16574806710141549469649885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44199484560377465252399693 16574806710141549469649885)
  ·
    refine ⟨6215552516303081051118707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16574806710141549469649885 6215552516303081051118707)
    ·
      refine ⟨9323328774454621576678061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6215552516303081051118707 9323328774454621576678061)
      ·
        refine ⟨3496248290420483091254273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9323328774454621576678061 3496248290420483091254273)
        ·
          refine ⟨2622186217815362318440705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3496248290420483091254273 2622186217815362318440705)
          ·
            refine ⟨1966639663361521738830529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622186217815362318440705 1966639663361521738830529)
            ·
              refine ⟨1474979747521141304122897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966639663361521738830529 1474979747521141304122897)
              ·
                refine ⟨1106234810640855978092173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474979747521141304122897 1106234810640855978092173)
                ·
                  refine ⟨414838053990320991784565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106234810640855978092173 414838053990320991784565)
                  ·
                    rfl

theorem cell21_1817762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1817762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817762 prefixEnd_1817762 := by exact prefixLift 1817762
  have htrace : WordTrace (prefixWord ++ tailWord_1817762) baseStart_1817762 baseEnd_1817762 := by
    simpa [prefixWord, tailWord_1817762, baseEnd_1817762] using wordTrace_append hprefix tailTrace_1817762
  have hstable : (prefixWord ++ tailWord_1817762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817762).length < 2 ^ (prefixWord ++ tailWord_1817762).sum := by decide
  have hdescent : baseEnd_1817762 < baseStart_1817762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817773 : List Nat := [1, 5, 2, 1, 3, 2, 1, 6]
def baseStart_1817773 : Nat := 118140960795 + 1817773 * 2 ^ 59
def prefixEnd_1817773 : Nat := 4983230072969 + 3 ^ 40 * 1817773 * 2
def baseEnd_1817773 : Nat := 138280188113395805700403

theorem tailTrace_1817773 : CollatzResearch.WordTrace tailWord_1817773 prefixEnd_1817773 138280188113395805700403 := by
  unfold tailWord_1817773
  simp only [CollatzResearch.WordTrace]
  refine ⟨66299628043526346757249973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44199752029017564504833315 66299628043526346757249973)
  ·
    refine ⟨6215590129080595008492185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66299628043526346757249973 6215590129080595008492185)
    ·
      refine ⟨4661692596810446256369139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6215590129080595008492185 4661692596810446256369139)
      ·
        refine ⟨6992538895215669384553709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4661692596810446256369139 6992538895215669384553709)
        ·
          refine ⟨2622202085705876019207641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6992538895215669384553709 2622202085705876019207641)
          ·
            refine ⟨1966651564279407014405731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622202085705876019207641 1966651564279407014405731)
            ·
              refine ⟨2949977346419110521608597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966651564279407014405731 2949977346419110521608597)
              ·
                refine ⟨138280188113395805700403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2949977346419110521608597 138280188113395805700403)
                ·
                  rfl

theorem cell21_1817773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 6].length) (baseStart_1817773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817773 prefixEnd_1817773 := by exact prefixLift 1817773
  have htrace : WordTrace (prefixWord ++ tailWord_1817773) baseStart_1817773 baseEnd_1817773 := by
    simpa [prefixWord, tailWord_1817773, baseEnd_1817773] using wordTrace_append hprefix tailTrace_1817773
  have hstable : (prefixWord ++ tailWord_1817773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817773).length < 2 ^ (prefixWord ++ tailWord_1817773).sum := by decide
  have hdescent : baseEnd_1817773 < baseStart_1817773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817880 : List Nat := [2, 1, 2, 3, 1, 4, 3, 2, 3]
def baseStart_1817880 : Nat := 118140960795 + 1817880 * 2 ^ 59
def prefixEnd_1817880 : Nat := 4983230072969 + 3 ^ 40 * 1817880 * 2
def baseEnd_1817880 : Nat := 414864983197979008817657

theorem tailTrace_1817880 : CollatzResearch.WordTrace tailWord_1817880 prefixEnd_1817880 414864983197979008817657 := by
  unfold tailWord_1817880
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151765327069352015697547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44202353769425802687596729 33151765327069352015697547)
  ·
    refine ⟨49727647990604028023546321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33151765327069352015697547 49727647990604028023546321)
    ·
      refine ⟨37295735992953021017659741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49727647990604028023546321 37295735992953021017659741)
      ·
        refine ⟨13985900997357382881622403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37295735992953021017659741 13985900997357382881622403)
        ·
          refine ⟨20978851496036074322433605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13985900997357382881622403 20978851496036074322433605)
          ·
            refine ⟨3933534655506763935456301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20978851496036074322433605 3933534655506763935456301)
            ·
              refine ⟨1475075495815036475796113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3933534655506763935456301 1475075495815036475796113)
              ·
                refine ⟨1106306621861277356847085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475075495815036475796113 1106306621861277356847085)
                ·
                  refine ⟨414864983197979008817657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106306621861277356847085 414864983197979008817657)
                  ·
                    rfl

theorem cell21_1817880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 3].length) (baseStart_1817880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817880 prefixEnd_1817880 := by exact prefixLift 1817880
  have htrace : WordTrace (prefixWord ++ tailWord_1817880) baseStart_1817880 baseEnd_1817880 := by
    simpa [prefixWord, tailWord_1817880, baseEnd_1817880] using wordTrace_append hprefix tailTrace_1817880
  have hstable : (prefixWord ++ tailWord_1817880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817880).length < 2 ^ (prefixWord ++ tailWord_1817880).sum := by decide
  have hdescent : baseEnd_1817880 < baseStart_1817880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817891 : List Nat := [1, 1, 1, 4, 2, 4, 2, 6]
def baseStart_1817891 : Nat := 118140960795 + 1817891 * 2 ^ 59
def prefixEnd_1817891 : Nat := 4983230072969 + 3 ^ 40 * 1817891 * 2
def baseEnd_1817891 : Nat := 138289164515948478044767

theorem tailTrace_1817891 : CollatzResearch.WordTrace tailWord_1817891 prefixEnd_1817891 138289164515948478044767 := by
  unfold tailWord_1817891
  simp only [CollatzResearch.WordTrace]
  refine ⟨66303931857098852910045527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44202621238065901940030351 66303931857098852910045527)
  ·
    refine ⟨99455897785648279365068291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66303931857098852910045527 99455897785648279365068291)
    ·
      refine ⟨149183846678472419047602437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99455897785648279365068291 149183846678472419047602437)
      ·
        refine ⟨27971971252213578571425457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149183846678472419047602437 27971971252213578571425457)
        ·
          refine ⟨20978978439160183928569093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27971971252213578571425457 20978978439160183928569093)
          ·
            refine ⟨3933558457342534486606705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20978978439160183928569093 3933558457342534486606705)
            ·
              refine ⟨2950168843006900864955029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3933558457342534486606705 2950168843006900864955029)
              ·
                refine ⟨138289164515948478044767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2950168843006900864955029 138289164515948478044767)
                ·
                  rfl

theorem cell21_1817891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 6].length) (baseStart_1817891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817891 prefixEnd_1817891 := by exact prefixLift 1817891
  have htrace : WordTrace (prefixWord ++ tailWord_1817891) baseStart_1817891 baseEnd_1817891 := by
    simpa [prefixWord, tailWord_1817891, baseEnd_1817891] using wordTrace_append hprefix tailTrace_1817891
  have hstable : (prefixWord ++ tailWord_1817891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817891).length < 2 ^ (prefixWord ++ tailWord_1817891).sum := by decide
  have hdescent : baseEnd_1817891 < baseStart_1817891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817967 : List Nat := [1, 1, 2, 1, 3, 1, 7, 5]
def baseStart_1817967 : Nat := 118140960795 + 1817967 * 2 ^ 59
def prefixEnd_1817967 : Nat := 4983230072969 + 3 ^ 40 * 1817967 * 2
def baseEnd_1817967 : Nat := 138294945927762063622493

theorem tailTrace_1817967 : CollatzResearch.WordTrace tailWord_1817967 prefixEnd_1817967 138294945927762063622493 := by
  unfold tailWord_1817967
  simp only [CollatzResearch.WordTrace]
  refine ⟨66306703804823517889812155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44204469203215678593208103 66306703804823517889812155)
  ·
    refine ⟨99460055707235276834718233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66306703804823517889812155 99460055707235276834718233)
    ·
      refine ⟨74595041780426457626038675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99460055707235276834718233 74595041780426457626038675)
      ·
        refine ⟨111892562670639686439058013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74595041780426457626038675 111892562670639686439058013)
        ·
          refine ⟨41959711001489882414646755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111892562670639686439058013 41959711001489882414646755)
          ·
            refine ⟨62939566502234823621970133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41959711001489882414646755 62939566502234823621970133)
            ·
              refine ⟨1475146089896128678639925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 62939566502234823621970133 1475146089896128678639925)
              ·
                refine ⟨138294945927762063622493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1475146089896128678639925 138294945927762063622493)
                ·
                  rfl

theorem cell21_1817967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 5].length) (baseStart_1817967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817967 prefixEnd_1817967 := by exact prefixLift 1817967
  have htrace : WordTrace (prefixWord ++ tailWord_1817967) baseStart_1817967 baseEnd_1817967 := by
    simpa [prefixWord, tailWord_1817967, baseEnd_1817967] using wordTrace_append hprefix tailTrace_1817967
  have hstable : (prefixWord ++ tailWord_1817967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817967).length < 2 ^ (prefixWord ++ tailWord_1817967).sum := by decide
  have hdescent : baseEnd_1817967 < baseStart_1817967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1817981 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 7]
def baseStart_1817981 : Nat := 118140960795 + 1817981 * 2 ^ 59
def prefixEnd_1817981 : Nat := 4983230072969 + 3 ^ 40 * 1817981 * 2
def baseEnd_1817981 : Nat := 414888032774025277634117

theorem tailTrace_1817981 : CollatzResearch.WordTrace tailWord_1817981 prefixEnd_1817981 414888032774025277634117 := by
  unfold tailWord_1817981
  simp only [CollatzResearch.WordTrace]
  refine ⟨66307214426772798280821797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44204809617848532187214531 66307214426772798280821797)
  ·
    refine ⟨12432602705019899677654087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66307214426772798280821797 12432602705019899677654087)
    ·
      refine ⟨18648904057529849516481131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12432602705019899677654087 18648904057529849516481131)
      ·
        refine ⟨27973356086294774274721697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18648904057529849516481131 27973356086294774274721697)
        ·
          refine ⟨20980017064721080706041273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27973356086294774274721697 20980017064721080706041273)
          ·
            refine ⟨15735012798540810529530955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20980017064721080706041273 15735012798540810529530955)
            ·
              refine ⟨23602519197811215794296433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15735012798540810529530955 23602519197811215794296433)
              ·
                refine ⟨17701889398358411845722325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23602519197811215794296433 17701889398358411845722325)
                ·
                  refine ⟨414888032774025277634117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17701889398358411845722325 414888032774025277634117)
                  ·
                    rfl

theorem cell21_1817981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_1817981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1817981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1817981 prefixEnd_1817981 := by exact prefixLift 1817981
  have htrace : WordTrace (prefixWord ++ tailWord_1817981) baseStart_1817981 baseEnd_1817981 := by
    simpa [prefixWord, tailWord_1817981, baseEnd_1817981] using wordTrace_append hprefix tailTrace_1817981
  have hstable : (prefixWord ++ tailWord_1817981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1817981).length < 2 ^ (prefixWord ++ tailWord_1817981).sum := by decide
  have hdescent : baseEnd_1817981 < baseStart_1817981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1817981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818029 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1818029 : Nat := 118140960795 + 1818029 * 2 ^ 59
def prefixEnd_1818029 : Nat := 4983230072969 + 3 ^ 40 * 1818029 * 2
def baseEnd_1818029 : Nat := 414898987027987860834019

theorem tailTrace_1818029 : CollatzResearch.WordTrace tailWord_1818029 prefixEnd_1818029 414898987027987860834019 := by
  unfold tailWord_1818029
  simp only [CollatzResearch.WordTrace]
  refine ⟨66308965130598902478569141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44205976753732601652379427 66308965130598902478569141)
  ·
    refine ⟨6216465480993647107365857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66308965130598902478569141 6216465480993647107365857)
    ·
      refine ⟨4662349110745235330524393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6216465480993647107365857 4662349110745235330524393)
      ·
        refine ⟨3496761833058926497893295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4662349110745235330524393 3496761833058926497893295)
        ·
          refine ⟨5245142749588389746839943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496761833058926497893295 5245142749588389746839943)
          ·
            refine ⟨7867714124382584620259915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245142749588389746839943 7867714124382584620259915)
            ·
              refine ⟨11801571186573876930389873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867714124382584620259915 11801571186573876930389873)
              ·
                refine ⟨8851178389930407697792405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11801571186573876930389873 8851178389930407697792405)
                ·
                  refine ⟨414898987027987860834019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8851178389930407697792405 414898987027987860834019)
                  ·
                    rfl

theorem cell21_1818029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1818029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818029 prefixEnd_1818029 := by exact prefixLift 1818029
  have htrace : WordTrace (prefixWord ++ tailWord_1818029) baseStart_1818029 baseEnd_1818029 := by
    simpa [prefixWord, tailWord_1818029, baseEnd_1818029] using wordTrace_append hprefix tailTrace_1818029
  have hstable : (prefixWord ++ tailWord_1818029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818029).length < 2 ^ (prefixWord ++ tailWord_1818029).sum := by decide
  have hdescent : baseEnd_1818029 < baseStart_1818029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818119 : List Nat := [1, 1, 4, 3, 2, 1, 3, 6]
def baseStart_1818119 : Nat := 118140960795 + 1818119 * 2 ^ 59
def prefixEnd_1818119 : Nat := 4983230072969 + 3 ^ 40 * 1818119 * 2
def baseEnd_1818119 : Nat := 138306508751389234777945

theorem tailTrace_1818119 : CollatzResearch.WordTrace tailWord_1818119 prefixEnd_1818119 138306508751389234777945 := by
  unfold tailWord_1818119
  simp only [CollatzResearch.WordTrace]
  refine ⟨66312247700272847849345411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44208165133515231899563607 66312247700272847849345411)
  ·
    refine ⟨99468371550409271774018117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66312247700272847849345411 99468371550409271774018117)
    ·
      refine ⟨18650319665701738457628397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99468371550409271774018117 18650319665701738457628397)
      ·
        refine ⟨6993869874638151921610649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18650319665701738457628397 6993869874638151921610649)
        ·
          refine ⟨5245402405978613941207987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6993869874638151921610649 5245402405978613941207987)
          ·
            refine ⟨7868103608967920911811981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245402405978613941207987 7868103608967920911811981)
            ·
              refine ⟨2950538853362970341929493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7868103608967920911811981 2950538853362970341929493)
              ·
                refine ⟨138306508751389234777945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2950538853362970341929493 138306508751389234777945)
                ·
                  rfl

theorem cell21_1818119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 6].length) (baseStart_1818119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818119 prefixEnd_1818119 := by exact prefixLift 1818119
  have htrace : WordTrace (prefixWord ++ tailWord_1818119) baseStart_1818119 baseEnd_1818119 := by
    simpa [prefixWord, tailWord_1818119, baseEnd_1818119] using wordTrace_append hprefix tailTrace_1818119
  have hstable : (prefixWord ++ tailWord_1818119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818119).length < 2 ^ (prefixWord ++ tailWord_1818119).sum := by decide
  have hdescent : baseEnd_1818119 < baseStart_1818119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818133 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 7]
def baseStart_1818133 : Nat := 118140960795 + 1818133 * 2 ^ 59
def prefixEnd_1818133 : Nat := 4983230072969 + 3 ^ 40 * 1818133 * 2
def baseEnd_1818133 : Nat := 414922721244906791100473

theorem tailTrace_1818133 : CollatzResearch.WordTrace tailWord_1818133 prefixEnd_1818133 414922721244906791100473 := by
  unfold tailWord_1818133
  simp only [CollatzResearch.WordTrace]
  refine ⟨66312758322222128240355053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44208505548148085493570035 66312758322222128240355053)
  ·
    refine ⟨24867284370833298090133145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66312758322222128240355053 24867284370833298090133145)
    ·
      refine ⟨18650463278124973567599859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24867284370833298090133145 18650463278124973567599859)
      ·
        refine ⟨27975694917187460351399789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18650463278124973567599859 27975694917187460351399789)
        ·
          refine ⟨10490885593945297631774921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27975694917187460351399789 10490885593945297631774921)
          ·
            refine ⟨7868164195458973223831191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10490885593945297631774921 7868164195458973223831191)
            ·
              refine ⟨11802246293188459835746787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7868164195458973223831191 11802246293188459835746787)
              ·
                refine ⟨17703369439782689753620181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11802246293188459835746787 17703369439782689753620181)
                ·
                  refine ⟨414922721244906791100473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17703369439782689753620181 414922721244906791100473)
                  ·
                    rfl

theorem cell21_1818133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_1818133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818133 prefixEnd_1818133 := by exact prefixLift 1818133
  have htrace : WordTrace (prefixWord ++ tailWord_1818133) baseStart_1818133 baseEnd_1818133 := by
    simpa [prefixWord, tailWord_1818133, baseEnd_1818133] using wordTrace_append hprefix tailTrace_1818133
  have hstable : (prefixWord ++ tailWord_1818133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818133).length < 2 ^ (prefixWord ++ tailWord_1818133).sum := by decide
  have hdescent : baseEnd_1818133 < baseStart_1818133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818136 : List Nat := [2, 1, 2, 3, 4, 1, 3, 5]
def baseStart_1818136 : Nat := 118140960795 + 1818136 * 2 ^ 59
def prefixEnd_1818136 : Nat := 4983230072969 + 3 ^ 40 * 1818136 * 2
def baseEnd_1818136 : Nat := 138307801961926484183489

theorem tailTrace_1818136 : CollatzResearch.WordTrace tailWord_1818136 prefixEnd_1818136 138307801961926484183489 := by
  unfold tailWord_1818136
  simp only [CollatzResearch.WordTrace]
  refine ⟨33156433870605629876357131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44208578494140839835142841 33156433870605629876357131)
  ·
    refine ⟨49734650805908444814535697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33156433870605629876357131 49734650805908444814535697)
    ·
      refine ⟨37300988104431333610901773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49734650805908444814535697 37300988104431333610901773)
      ·
        refine ⟨13987870539161750104088165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37300988104431333610901773 13987870539161750104088165)
        ·
          refine ⟨2622725726092828144516531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13987870539161750104088165 2622725726092828144516531)
          ·
            refine ⟨3934088589139242216774797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622725726092828144516531 3934088589139242216774797)
            ·
              refine ⟨1475283220927215831290549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3934088589139242216774797 1475283220927215831290549)
              ·
                refine ⟨138307801961926484183489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1475283220927215831290549 138307801961926484183489)
                ·
                  rfl

theorem cell21_1818136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 5].length) (baseStart_1818136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818136 prefixEnd_1818136 := by exact prefixLift 1818136
  have htrace : WordTrace (prefixWord ++ tailWord_1818136) baseStart_1818136 baseEnd_1818136 := by
    simpa [prefixWord, tailWord_1818136, baseEnd_1818136] using wordTrace_append hprefix tailTrace_1818136
  have hstable : (prefixWord ++ tailWord_1818136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818136).length < 2 ^ (prefixWord ++ tailWord_1818136).sum := by decide
  have hdescent : baseEnd_1818136 < baseStart_1818136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818181 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 4]
def baseStart_1818181 : Nat := 118140960795 + 1818181 * 2 ^ 59
def prefixEnd_1818181 : Nat := 4983230072969 + 3 ^ 40 * 1818181 * 2
def baseEnd_1818181 : Nat := 414933675498869374300375

theorem tailTrace_1818181 : CollatzResearch.WordTrace tailWord_1818181 prefixEnd_1818181 414933675498869374300375 := by
  unfold tailWord_1818181
  simp only [CollatzResearch.WordTrace]
  refine ⟨66314509026048232438102397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44209672684032154958734931 66314509026048232438102397)
  ·
    refine ⟨24867940884768087164288399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66314509026048232438102397 24867940884768087164288399)
    ·
      refine ⟨37301911327152130746432599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24867940884768087164288399 37301911327152130746432599)
      ·
        refine ⟨55952866990728196119648899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37301911327152130746432599 55952866990728196119648899)
        ·
          refine ⟨83929300486092294179473349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55952866990728196119648899 83929300486092294179473349)
          ·
            refine ⟨15736743841142305158651253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83929300486092294179473349 15736743841142305158651253)
            ·
              refine ⟨1475319735107091108623555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15736743841142305158651253 1475319735107091108623555)
              ·
                refine ⟨2212979602660636662935333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475319735107091108623555 2212979602660636662935333)
                ·
                  refine ⟨414933675498869374300375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212979602660636662935333 414933675498869374300375)
                  ·
                    rfl

theorem cell21_1818181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_1818181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818181 prefixEnd_1818181 := by exact prefixLift 1818181
  have htrace : WordTrace (prefixWord ++ tailWord_1818181) baseStart_1818181 baseEnd_1818181 := by
    simpa [prefixWord, tailWord_1818181, baseEnd_1818181] using wordTrace_append hprefix tailTrace_1818181
  have hstable : (prefixWord ++ tailWord_1818181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818181).length < 2 ^ (prefixWord ++ tailWord_1818181).sum := by decide
  have hdescent : baseEnd_1818181 < baseStart_1818181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818226 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 5]
def baseStart_1818226 : Nat := 118140960795 + 1818226 * 2 ^ 59
def prefixEnd_1818226 : Nat := 4983230072969 + 3 ^ 40 * 1818226 * 2
def baseEnd_1818226 : Nat := 414943945111959296050283

theorem tailTrace_1818226 : CollatzResearch.WordTrace tailWord_1818226 prefixEnd_1818226 414943945111959296050283 := by
  unfold tailWord_1818226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16579037577721301280872633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44210766873923470082327021 16579037577721301280872633)
  ·
    refine ⟨12434278183290975960654475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16579037577721301280872633 12434278183290975960654475)
    ·
      refine ⟨18651417274936463940981713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12434278183290975960654475 18651417274936463940981713)
      ·
        refine ⟨13988562956202347955736285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18651417274936463940981713 13988562956202347955736285)
        ·
          refine ⟨5245711108575880483401107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13988562956202347955736285 5245711108575880483401107)
          ·
            refine ⟨7868566662863820725101661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245711108575880483401107 7868566662863820725101661)
            ·
              refine ⟨2950712498573932771913123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7868566662863820725101661 2950712498573932771913123)
              ·
                refine ⟨4426068747860899157869685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950712498573932771913123 4426068747860899157869685)
                ·
                  refine ⟨414943945111959296050283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4426068747860899157869685 414943945111959296050283)
                  ·
                    rfl

theorem cell21_1818226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_1818226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818226 prefixEnd_1818226 := by exact prefixLift 1818226
  have htrace : WordTrace (prefixWord ++ tailWord_1818226) baseStart_1818226 baseEnd_1818226 := by
    simpa [prefixWord, tailWord_1818226, baseEnd_1818226] using wordTrace_append hprefix tailTrace_1818226
  have hstable : (prefixWord ++ tailWord_1818226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818226).length < 2 ^ (prefixWord ++ tailWord_1818226).sum := by decide
  have hdescent : baseEnd_1818226 < baseStart_1818226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818240 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 4]
def baseStart_1818240 : Nat := 118140960795 + 1818240 * 2 ^ 59
def prefixEnd_1818240 : Nat := 4983230072969 + 3 ^ 40 * 1818240 * 2
def baseEnd_1818240 : Nat := 414947140102698382816921

theorem tailTrace_1818240 : CollatzResearch.WordTrace tailWord_1818240 prefixEnd_1818240 414947140102698382816921 := by
  unfold tailWord_1818240
  simp only [CollatzResearch.WordTrace]
  refine ⟨33158330466417242757250087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44211107288556323676333449 33158330466417242757250087)
  ·
    refine ⟨49737495699625864135875131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33158330466417242757250087 49737495699625864135875131)
    ·
      refine ⟨74606243549438796203812697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49737495699625864135875131 74606243549438796203812697)
      ·
        refine ⟨55954682662079097152859523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74606243549438796203812697 55954682662079097152859523)
        ·
          refine ⟨83932023993118645729289285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55954682662079097152859523 83932023993118645729289285)
          ·
            refine ⟨15737254498709746074241741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83932023993118645729289285 15737254498709746074241741)
            ·
              refine ⟨5901470437016154777840653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15737254498709746074241741 5901470437016154777840653)
              ·
                refine ⟨2213051413881058041690245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5901470437016154777840653 2213051413881058041690245)
                ·
                  refine ⟨414947140102698382816921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2213051413881058041690245 414947140102698382816921)
                  ·
                    rfl

theorem cell21_1818240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 4].length) (baseStart_1818240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818240 prefixEnd_1818240 := by exact prefixLift 1818240
  have htrace : WordTrace (prefixWord ++ tailWord_1818240) baseStart_1818240 baseEnd_1818240 := by
    simpa [prefixWord, tailWord_1818240, baseEnd_1818240] using wordTrace_append hprefix tailTrace_1818240
  have hstable : (prefixWord ++ tailWord_1818240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818240).length < 2 ^ (prefixWord ++ tailWord_1818240).sum := by decide
  have hdescent : baseEnd_1818240 < baseStart_1818240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818271 : List Nat := [1, 1, 2, 7, 1, 9]
def baseStart_1818271 : Nat := 118140960795 + 1818271 * 2 ^ 59
def prefixEnd_1818271 : Nat := 4983230072969 + 3 ^ 40 * 1818271 * 2
def baseEnd_1818271 : Nat := 15368674619446267325933

theorem tailTrace_1818271 : CollatzResearch.WordTrace tailWord_1818271 prefixEnd_1818271 15368674619446267325933 := by
  unfold tailWord_1818271
  simp only [CollatzResearch.WordTrace]
  refine ⟨66317791595722177808878667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44211861063814785205919111 66317791595722177808878667)
  ·
    refine ⟨99476687393583266713318001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66317791595722177808878667 99476687393583266713318001)
    ·
      refine ⟨74607515545187450034988501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99476687393583266713318001 74607515545187450034988501)
      ·
        refine ⟨1748613645590330860195043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 74607515545187450034988501 1748613645590330860195043)
        ·
          refine ⟨2622920468385496290292565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748613645590330860195043 2622920468385496290292565)
          ·
            refine ⟨15368674619446267325933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2622920468385496290292565 15368674619446267325933)
            ·
              rfl

theorem cell21_1818271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 9].length) (baseStart_1818271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818271 prefixEnd_1818271 := by exact prefixLift 1818271
  have htrace : WordTrace (prefixWord ++ tailWord_1818271) baseStart_1818271 baseEnd_1818271 := by
    simpa [prefixWord, tailWord_1818271, baseEnd_1818271] using wordTrace_append hprefix tailTrace_1818271
  have hstable : (prefixWord ++ tailWord_1818271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818271).length < 2 ^ (prefixWord ++ tailWord_1818271).sum := by decide
  have hdescent : baseEnd_1818271 < baseStart_1818271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818302 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1818302 : Nat := 118140960795 + 1818302 * 2 ^ 59
def prefixEnd_1818302 : Nat := 4983230072969 + 3 ^ 40 * 1818302 * 2
def baseEnd_1818302 : Nat := 414961289347400052783461

theorem tailTrace_1818302 : CollatzResearch.WordTrace tailWord_1818302 prefixEnd_1818302 414961289347400052783461 := by
  unfold tailWord_1818302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8289865282326233762907145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44212614839073246735504773 8289865282326233762907145)
  ·
    refine ⟨6217398961744675322180359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8289865282326233762907145 6217398961744675322180359)
    ·
      refine ⟨9326098442617012983270539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6217398961744675322180359 9326098442617012983270539)
      ·
        refine ⟨13989147663925519474905809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9326098442617012983270539 13989147663925519474905809)
        ·
          refine ⟨10491860747944139606179357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13989147663925519474905809 10491860747944139606179357)
          ·
            refine ⟨3934447780479052352317259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10491860747944139606179357 3934447780479052352317259)
            ·
              refine ⟨5901671670718578528475889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934447780479052352317259 5901671670718578528475889)
              ·
                refine ⟨4426253753038933896356917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5901671670718578528475889 4426253753038933896356917)
                ·
                  refine ⟨414961289347400052783461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4426253753038933896356917 414961289347400052783461)
                  ·
                    rfl

theorem cell21_1818302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1818302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818302 prefixEnd_1818302 := by exact prefixLift 1818302
  have htrace : WordTrace (prefixWord ++ tailWord_1818302) baseStart_1818302 baseEnd_1818302 := by
    simpa [prefixWord, tailWord_1818302, baseEnd_1818302] using wordTrace_append hprefix tailTrace_1818302
  have hstable : (prefixWord ++ tailWord_1818302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818302).length < 2 ^ (prefixWord ++ tailWord_1818302).sum := by decide
  have hdescent : baseEnd_1818302 < baseStart_1818302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818330 : List Nat := [3, 1, 1, 2, 2, 4, 8]
def baseStart_1818330 : Nat := 118140960795 + 1818330 * 2 ^ 59
def prefixEnd_1818330 : Nat := 4983230072969 + 3 ^ 40 * 1818330 * 2
def baseEnd_1818330 : Nat := 46107519925430914035193

theorem tailTrace_1818330 : CollatzResearch.WordTrace tailWord_1818330 prefixEnd_1818330 46107519925430914035193 := by
  unfold tailWord_1818330
  simp only [CollatzResearch.WordTrace]
  refine ⟨16579985875627107721319111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44213295668338953923517629 16579985875627107721319111)
  ·
    refine ⟨24869978813440661581978667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16579985875627107721319111 24869978813440661581978667)
    ·
      refine ⟨37304968220160992372968001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24869978813440661581978667 37304968220160992372968001)
      ·
        refine ⟨27978726165120744279726001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37304968220160992372968001 27978726165120744279726001)
        ·
          refine ⟨20984044623840558209794501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27978726165120744279726001 20984044623840558209794501)
          ·
            refine ⟨3934508366970104664336469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20984044623840558209794501 3934508366970104664336469)
            ·
              refine ⟨46107519925430914035193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3934508366970104664336469 46107519925430914035193)
              ·
                rfl

theorem cell21_1818330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 8].length) (baseStart_1818330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818330 prefixEnd_1818330 := by exact prefixLift 1818330
  have htrace : WordTrace (prefixWord ++ tailWord_1818330) baseStart_1818330 baseEnd_1818330 := by
    simpa [prefixWord, tailWord_1818330, baseEnd_1818330] using wordTrace_append hprefix tailTrace_1818330
  have hstable : (prefixWord ++ tailWord_1818330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818330).length < 2 ^ (prefixWord ++ tailWord_1818330).sum := by decide
  have hdescent : baseEnd_1818330 < baseStart_1818330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818496 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_1818496 : Nat := 118140960795 + 1818496 * 2 ^ 59
def prefixEnd_1818496 : Nat := 4983230072969 + 3 ^ 40 * 1818496 * 2
def baseEnd_1818496 : Nat := 415005562790498826549731

theorem tailTrace_1818496 : CollatzResearch.WordTrace tailWord_1818496 prefixEnd_1818496 415005562790498826549731 := by
  unfold tailWord_1818496
  simp only [CollatzResearch.WordTrace]
  refine ⟨33162999009953520617909671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44217332013271360823879561 33162999009953520617909671)
  ·
    refine ⟨49744498514930280926864507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33162999009953520617909671 49744498514930280926864507)
    ·
      refine ⟨74616747772395421390296761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49744498514930280926864507 74616747772395421390296761)
      ·
        refine ⟨55962560829296566042722571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74616747772395421390296761 55962560829296566042722571)
        ·
          refine ⟨83943841243944849064083857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55962560829296566042722571 83943841243944849064083857)
          ·
            refine ⟨62957880932958636798062893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83943841243944849064083857 62957880932958636798062893)
            ·
              refine ⟨23609205349859488799273585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62957880932958636798062893 23609205349859488799273585)
              ·
                refine ⟨17706904012394616599455189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23609205349859488799273585 17706904012394616599455189)
                ·
                  refine ⟨415005562790498826549731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17706904012394616599455189 415005562790498826549731)
                  ·
                    rfl

theorem cell21_1818496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_1818496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818496 prefixEnd_1818496 := by exact prefixLift 1818496
  have htrace : WordTrace (prefixWord ++ tailWord_1818496) baseStart_1818496 baseEnd_1818496 := by
    simpa [prefixWord, tailWord_1818496, baseEnd_1818496] using wordTrace_append hprefix tailTrace_1818496
  have hstable : (prefixWord ++ tailWord_1818496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818496).length < 2 ^ (prefixWord ++ tailWord_1818496).sum := by decide
  have hdescent : baseEnd_1818496 < baseStart_1818496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818558 : List Nat := [4, 2, 1, 1, 1, 3, 9]
def baseStart_1818558 : Nat := 118140960795 + 1818558 * 2 ^ 59
def prefixEnd_1818558 : Nat := 4983230072969 + 3 ^ 40 * 1818558 * 2
def baseEnd_1818558 : Nat := 46113301337244499612919

theorem tailTrace_1818558 : CollatzResearch.WordTrace tailWord_1818558 prefixEnd_1818558 46113301337244499612919 := by
  unfold tailWord_1818558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8291032418210303228072041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44218839563788283883050885 8291032418210303228072041)
  ·
    refine ⟨6218274313657727421054031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8291032418210303228072041 6218274313657727421054031)
    ·
      refine ⟨9327411470486591131581047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6218274313657727421054031 9327411470486591131581047)
      ·
        refine ⟨13991117205729886697371571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9327411470486591131581047 13991117205729886697371571)
        ·
          refine ⟨20986675808594830046057357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13991117205729886697371571 20986675808594830046057357)
          ·
            refine ⟨7870003428223061267271509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20986675808594830046057357 7870003428223061267271509)
            ·
              refine ⟨46113301337244499612919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7870003428223061267271509 46113301337244499612919)
              ·
                rfl

theorem cell21_1818558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 9].length) (baseStart_1818558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818558 prefixEnd_1818558 := by exact prefixLift 1818558
  have htrace : WordTrace (prefixWord ++ tailWord_1818558) baseStart_1818558 baseEnd_1818558 := by
    simpa [prefixWord, tailWord_1818558, baseEnd_1818558] using wordTrace_append hprefix tailTrace_1818558
  have hstable : (prefixWord ++ tailWord_1818558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818558).length < 2 ^ (prefixWord ++ tailWord_1818558).sum := by decide
  have hdescent : baseEnd_1818558 < baseStart_1818558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818617 : List Nat := [1, 2, 1, 3, 1, 13]
def baseStart_1818617 : Nat := 118140960795 + 1818617 * 2 ^ 59
def prefixEnd_1818617 : Nat := 4983230072969 + 3 ^ 40 * 1818617 * 2
def baseEnd_1818617 : Nat := 15371599134778870556771

theorem tailTrace_1818617 : CollatzResearch.WordTrace tailWord_1818617 prefixEnd_1818617 15371599134778870556771 := by
  unfold tailWord_1818617
  simp only [CollatzResearch.WordTrace]
  refine ⟨66330411252468678900974105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44220274168312452600649403 66330411252468678900974105)
  ·
    refine ⟨49747808439351509175730579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66330411252468678900974105 49747808439351509175730579)
    ·
      refine ⟨74621712659027263763595869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49747808439351509175730579 74621712659027263763595869)
      ·
        refine ⟨27983142247135223911348451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74621712659027263763595869 27983142247135223911348451)
        ·
          refine ⟨41974713370702835867022677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27983142247135223911348451 41974713370702835867022677)
          ·
            refine ⟨15371599134778870556771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 41974713370702835867022677 15371599134778870556771)
            ·
              rfl

theorem cell21_1818617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 13].length) (baseStart_1818617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818617 prefixEnd_1818617 := by exact prefixLift 1818617
  have htrace : WordTrace (prefixWord ++ tailWord_1818617) baseStart_1818617 baseEnd_1818617 := by
    simpa [prefixWord, tailWord_1818617, baseEnd_1818617] using wordTrace_append hprefix tailTrace_1818617
  have hstable : (prefixWord ++ tailWord_1818617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818617).length < 2 ^ (prefixWord ++ tailWord_1818617).sum := by decide
  have hdescent : baseEnd_1818617 < baseStart_1818617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818620 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 4]
def baseStart_1818620 : Nat := 118140960795 + 1818620 * 2 ^ 59
def prefixEnd_1818620 : Nat := 4983230072969 + 3 ^ 40 * 1818620 * 2
def baseEnd_1818620 : Nat := 415033861279902166482811

theorem tailTrace_1818620 : CollatzResearch.WordTrace tailWord_1818620 prefixEnd_1818620 415033861279902166482811 := by
  unfold tailWord_1818620
  simp only [CollatzResearch.WordTrace]
  refine ⟨33165260335728905206666657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44220347114305206942222209 33165260335728905206666657)
  ·
    refine ⟨24873945251796678904999993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33165260335728905206666657 24873945251796678904999993)
    ·
      refine ⟨18655458938847509178749995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24873945251796678904999993 18655458938847509178749995)
      ·
        refine ⟨27983188408271263768124993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18655458938847509178749995 27983188408271263768124993)
        ·
          refine ⟨20987391306203447826093745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27983188408271263768124993 20987391306203447826093745)
          ·
            refine ⟨15740543479652585869570309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20987391306203447826093745 15740543479652585869570309)
            ·
              refine ⟨2951351902434859850544433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15740543479652585869570309 2951351902434859850544433)
              ·
                refine ⟨2213513926826144887908325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2951351902434859850544433 2213513926826144887908325)
                ·
                  refine ⟨415033861279902166482811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2213513926826144887908325 415033861279902166482811)
                  ·
                    rfl

theorem cell21_1818620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_1818620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818620 prefixEnd_1818620 := by exact prefixLift 1818620
  have htrace : WordTrace (prefixWord ++ tailWord_1818620) baseStart_1818620 baseEnd_1818620 := by
    simpa [prefixWord, tailWord_1818620, baseEnd_1818620] using wordTrace_append hprefix tailTrace_1818620
  have hstable : (prefixWord ++ tailWord_1818620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818620).length < 2 ^ (prefixWord ++ tailWord_1818620).sum := by decide
  have hdescent : baseEnd_1818620 < baseStart_1818620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818693 : List Nat := [1, 3, 1, 1, 1, 3, 1, 10]
def baseStart_1818693 : Nat := 118140960795 + 1818693 * 2 ^ 59
def prefixEnd_1818693 : Nat := 4983230072969 + 3 ^ 40 * 1818693 * 2
def baseEnd_1818693 : Nat := 138350173624823420588665

theorem tailTrace_1818693 : CollatzResearch.WordTrace tailWord_1818693 prefixEnd_1818693 138350173624823420588665 := by
  unfold tailWord_1818693
  simp only [CollatzResearch.WordTrace]
  refine ⟨66333183200193343880740733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44222122133462229253827155 66333183200193343880740733)
  ·
    refine ⟨24874943700072503955277775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66333183200193343880740733 24874943700072503955277775)
    ·
      refine ⟨37312415550108755932916663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24874943700072503955277775 37312415550108755932916663)
      ·
        refine ⟨55968623325163133899374995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37312415550108755932916663 55968623325163133899374995)
        ·
          refine ⟨83952934987744700849062493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55968623325163133899374995 83952934987744700849062493)
          ·
            refine ⟨31482350620404262818398435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83952934987744700849062493 31482350620404262818398435)
            ·
              refine ⟨47223525930606394227597653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31482350620404262818398435 47223525930606394227597653)
              ·
                refine ⟨138350173624823420588665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47223525930606394227597653 138350173624823420588665)
                ·
                  rfl

theorem cell21_1818693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 10].length) (baseStart_1818693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818693 prefixEnd_1818693 := by exact prefixLift 1818693
  have htrace : WordTrace (prefixWord ++ tailWord_1818693) baseStart_1818693 baseEnd_1818693 := by
    simpa [prefixWord, tailWord_1818693, baseEnd_1818693] using wordTrace_append hprefix tailTrace_1818693
  have hstable : (prefixWord ++ tailWord_1818693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818693).length < 2 ^ (prefixWord ++ tailWord_1818693).sum := by decide
  have hdescent : baseEnd_1818693 < baseStart_1818693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818724 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_1818724 : Nat := 118140960795 + 1818724 * 2 ^ 59
def prefixEnd_1818724 : Nat := 4983230072969 + 3 ^ 40 * 1818724 * 2
def baseEnd_1818724 : Nat := 415057595496821096749265

theorem tailTrace_1818724 : CollatzResearch.WordTrace tailWord_1818724 prefixEnd_1818724 415057595496821096749265 := by
  unfold tailWord_1818724
  simp only [CollatzResearch.WordTrace]
  refine ⟨33167156931540518087559613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44222875908720690783412817 33167156931540518087559613)
  ·
    refine ⟨12437683849327694282834855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33167156931540518087559613 12437683849327694282834855)
    ·
      refine ⟨18656525773991541424252283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12437683849327694282834855 18656525773991541424252283)
      ·
        refine ⟨27984788660987312136378425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18656525773991541424252283 27984788660987312136378425)
        ·
          refine ⟨20988591495740484102283819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27984788660987312136378425 20988591495740484102283819)
          ·
            refine ⟨31482887243610726153425729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20988591495740484102283819 31482887243610726153425729)
            ·
              refine ⟨23612165432708044615069297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31482887243610726153425729 23612165432708044615069297)
              ·
                refine ⟨17709124074531033461301973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23612165432708044615069297 17709124074531033461301973)
                ·
                  refine ⟨415057595496821096749265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17709124074531033461301973 415057595496821096749265)
                  ·
                    rfl

theorem cell21_1818724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_1818724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818724 prefixEnd_1818724 := by exact prefixLift 1818724
  have htrace : WordTrace (prefixWord ++ tailWord_1818724) baseStart_1818724 baseEnd_1818724 := by
    simpa [prefixWord, tailWord_1818724, baseEnd_1818724] using wordTrace_append hprefix tailTrace_1818724
  have hstable : (prefixWord ++ tailWord_1818724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818724).length < 2 ^ (prefixWord ++ tailWord_1818724).sum := by decide
  have hdescent : baseEnd_1818724 < baseStart_1818724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818786 : List Nat := [3, 3, 1, 3, 1, 10]
def baseStart_1818786 : Nat := 118140960795 + 1818786 * 2 ^ 59
def prefixEnd_1818786 : Nat := 4983230072969 + 3 ^ 40 * 1818786 * 2
def baseEnd_1818786 : Nat := 15373027583019361730215

theorem tailTrace_1818786 : CollatzResearch.WordTrace tailWord_1818786 prefixEnd_1818786 15373027583019361730215 := by
  unfold tailWord_1818786
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584143797214105190969053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44224383459237613842584141 16584143797214105190969053)
  ·
    refine ⟨6219053923955289446613395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16584143797214105190969053 6219053923955289446613395)
    ·
      refine ⟨9328580885932934169920093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6219053923955289446613395 9328580885932934169920093)
      ·
        refine ⟨3498217832224850313720035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9328580885932934169920093 3498217832224850313720035)
        ·
          refine ⟨5247326748337275470580053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3498217832224850313720035 5247326748337275470580053)
          ·
            refine ⟨15373027583019361730215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5247326748337275470580053 15373027583019361730215)
            ·
              rfl

theorem cell21_1818786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 10].length) (baseStart_1818786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818786 prefixEnd_1818786 := by exact prefixLift 1818786
  have htrace : WordTrace (prefixWord ++ tailWord_1818786) baseStart_1818786 baseEnd_1818786 := by
    simpa [prefixWord, tailWord_1818786, baseEnd_1818786] using wordTrace_append hprefix tailTrace_1818786
  have hstable : (prefixWord ++ tailWord_1818786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818786).length < 2 ^ (prefixWord ++ tailWord_1818786).sum := by decide
  have hdescent : baseEnd_1818786 < baseStart_1818786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818834 : List Nat := [3, 2, 2, 2, 1, 2, 1, 5, 3]
def baseStart_1818834 : Nat := 118140960795 + 1818834 * 2 ^ 59
def prefixEnd_1818834 : Nat := 4983230072969 + 3 ^ 40 * 1818834 * 2
def baseEnd_1818834 : Nat := 415082698995485349915707

theorem tailTrace_1818834 : CollatzResearch.WordTrace tailWord_1818834 prefixEnd_1818834 415082698995485349915707 := by
  unfold tailWord_1818834
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584581473170631240405889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44225550595121683307749037 16584581473170631240405889)
  ·
    refine ⟨12438436104877973430304417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16584581473170631240405889 12438436104877973430304417)
    ·
      refine ⟨9328827078658480072728313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12438436104877973430304417 9328827078658480072728313)
      ·
        refine ⟨6996620308993860054546235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9328827078658480072728313 6996620308993860054546235)
        ·
          refine ⟨10494930463490790081819353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6996620308993860054546235 10494930463490790081819353)
          ·
            refine ⟨7871197847618092561364515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10494930463490790081819353 7871197847618092561364515)
            ·
              refine ⟨11806796771427138842046773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7871197847618092561364515 11806796771427138842046773)
              ·
                refine ⟨1106887197321294266441885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11806796771427138842046773 1106887197321294266441885)
                ·
                  refine ⟨415082698995485349915707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106887197321294266441885 415082698995485349915707)
                  ·
                    rfl

theorem cell21_1818834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_1818834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818834 prefixEnd_1818834 := by exact prefixLift 1818834
  have htrace : WordTrace (prefixWord ++ tailWord_1818834) baseStart_1818834 baseEnd_1818834 := by
    simpa [prefixWord, tailWord_1818834, baseEnd_1818834] using wordTrace_append hprefix tailTrace_1818834
  have hstable : (prefixWord ++ tailWord_1818834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818834).length < 2 ^ (prefixWord ++ tailWord_1818834).sum := by decide
  have hdescent : baseEnd_1818834 < baseStart_1818834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818924 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 4]
def baseStart_1818924 : Nat := 118140960795 + 1818924 * 2 ^ 59
def prefixEnd_1818924 : Nat := 4983230072969 + 3 ^ 40 * 1818924 * 2
def baseEnd_1818924 : Nat := 415103238221665193415523

theorem tailTrace_1818924 : CollatzResearch.WordTrace tailWord_1818924 prefixEnd_1818924 415103238221665193415523 := by
  unfold tailWord_1818924
  simp only [CollatzResearch.WordTrace]
  refine ⟨33170804231178235166199913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44227738974904313554933217 33170804231178235166199913)
  ·
    refine ⟨24878103173383676374649935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33170804231178235166199913 24878103173383676374649935)
    ·
      refine ⟨37317154760075514561974903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24878103173383676374649935 37317154760075514561974903)
      ·
        refine ⟨55975732140113271842962355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37317154760075514561974903 55975732140113271842962355)
        ·
          refine ⟨83963598210169907764443533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55975732140113271842962355 83963598210169907764443533)
          ·
            refine ⟨31486349328813715411666325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83963598210169907764443533 31486349328813715411666325)
            ·
              refine ⟨1475922624788142909921859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31486349328813715411666325 1475922624788142909921859)
              ·
                refine ⟨2213883937182214364882789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475922624788142909921859 2213883937182214364882789)
                ·
                  refine ⟨415103238221665193415523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2213883937182214364882789 415103238221665193415523)
                  ·
                    rfl

theorem cell21_1818924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_1818924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818924 prefixEnd_1818924 := by exact prefixLift 1818924
  have htrace : WordTrace (prefixWord ++ tailWord_1818924) baseStart_1818924 baseEnd_1818924 := by
    simpa [prefixWord, tailWord_1818924, baseEnd_1818924] using wordTrace_append hprefix tailTrace_1818924
  have hstable : (prefixWord ++ tailWord_1818924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818924).length < 2 ^ (prefixWord ++ tailWord_1818924).sum := by decide
  have hdescent : baseEnd_1818924 < baseStart_1818924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1818972 : List Nat := [2, 2, 4, 3, 1, 2, 1, 6]
def baseStart_1818972 : Nat := 118140960795 + 1818972 * 2 ^ 59
def prefixEnd_1818972 : Nat := 4983230072969 + 3 ^ 40 * 1818972 * 2
def baseEnd_1818972 : Nat := 138371397491875925538475

theorem tailTrace_1818972 : CollatzResearch.WordTrace tailWord_1818972 prefixEnd_1818972 138371397491875925538475 := by
  unfold tailWord_1818972
  simp only [CollatzResearch.WordTrace]
  refine ⟨33171679583091287265073585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44228906110788383020098113 33171679583091287265073585)
  ·
    refine ⟨24878759687318465448805189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33171679583091287265073585 24878759687318465448805189)
    ·
      refine ⟨4664767441372212271650973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24878759687318465448805189 4664767441372212271650973)
      ·
        refine ⟨1749287790514579601869115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4664767441372212271650973 1749287790514579601869115)
        ·
          refine ⟨2623931685771869402803673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749287790514579601869115 2623931685771869402803673)
          ·
            refine ⟨1967948764328902052102755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2623931685771869402803673 1967948764328902052102755)
            ·
              refine ⟨2951923146493353078154133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967948764328902052102755 2951923146493353078154133)
              ·
                refine ⟨138371397491875925538475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2951923146493353078154133 138371397491875925538475)
                ·
                  rfl

theorem cell21_1818972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 6].length) (baseStart_1818972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1818972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1818972 prefixEnd_1818972 := by exact prefixLift 1818972
  have htrace : WordTrace (prefixWord ++ tailWord_1818972) baseStart_1818972 baseEnd_1818972 := by
    simpa [prefixWord, tailWord_1818972, baseEnd_1818972] using wordTrace_append hprefix tailTrace_1818972
  have hstable : (prefixWord ++ tailWord_1818972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1818972).length < 2 ^ (prefixWord ++ tailWord_1818972).sum := by decide
  have hdescent : baseEnd_1818972 < baseStart_1818972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1818972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819048 : List Nat := [2, 1, 6, 1, 1, 3, 2, 5]
def baseStart_1819048 : Nat := 118140960795 + 1819048 * 2 ^ 59
def prefixEnd_1819048 : Nat := 4983230072969 + 3 ^ 40 * 1819048 * 2
def baseEnd_1819048 : Nat := 138377178903689511116201

theorem tailTrace_1819048 : CollatzResearch.WordTrace tailWord_1819048 prefixEnd_1819048 138377178903689511116201 := by
  unfold tailWord_1819048
  simp only [CollatzResearch.WordTrace]
  refine ⟨33173065556953619754956899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44230754075938159673275865 33173065556953619754956899)
  ·
    refine ⟨49759598335430429632435349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33173065556953619754956899 49759598335430429632435349)
    ·
      refine ⟨2332481171973301389020407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49759598335430429632435349 2332481171973301389020407)
      ·
        refine ⟨3498721757959952083530611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332481171973301389020407 3498721757959952083530611)
        ·
          refine ⟨5248082636939928125295917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3498721757959952083530611 5248082636939928125295917)
          ·
            refine ⟨1968030988852473046985969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5248082636939928125295917 1968030988852473046985969)
            ·
              refine ⟨1476023241639354785239477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968030988852473046985969 1476023241639354785239477)
              ·
                refine ⟨138377178903689511116201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1476023241639354785239477 138377178903689511116201)
                ·
                  rfl

theorem cell21_1819048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 5].length) (baseStart_1819048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819048 prefixEnd_1819048 := by exact prefixLift 1819048
  have htrace : WordTrace (prefixWord ++ tailWord_1819048) baseStart_1819048 baseEnd_1819048 := by
    simpa [prefixWord, tailWord_1819048, baseEnd_1819048] using wordTrace_append hprefix tailTrace_1819048
  have hstable : (prefixWord ++ tailWord_1819048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819048).length < 2 ^ (prefixWord ++ tailWord_1819048).sum := by decide
  have hdescent : baseEnd_1819048 < baseStart_1819048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819093 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 4]
def baseStart_1819093 : Nat := 118140960795 + 1819093 * 2 ^ 59
def prefixEnd_1819093 : Nat := 4983230072969 + 3 ^ 40 * 1819093 * 2
def baseEnd_1819093 : Nat := 415141806324158455098511

theorem tailTrace_1819093 : CollatzResearch.WordTrace tailWord_1819093 prefixEnd_1819093 415141806324158455098511 := by
  unfold tailWord_1819093
  simp only [CollatzResearch.WordTrace]
  refine ⟨66347772398744212195301933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44231848265829474796867955 66347772398744212195301933)
  ·
    refine ⟨24880414649529079573238225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66347772398744212195301933 24880414649529079573238225)
    ·
      refine ⟨18660310987146809679928669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24880414649529079573238225 18660310987146809679928669)
      ·
        refine ⟨6997616620180053629973251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18660310987146809679928669 6997616620180053629973251)
        ·
          refine ⟨10496424930270080444959877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6997616620180053629973251 10496424930270080444959877)
          ·
            refine ⟨1968079674425640083429977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10496424930270080444959877 1968079674425640083429977)
            ·
              refine ⟨1476059755819230062572483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968079674425640083429977 1476059755819230062572483)
              ·
                refine ⟨2214089633728845093858725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476059755819230062572483 2214089633728845093858725)
                ·
                  refine ⟨415141806324158455098511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2214089633728845093858725 415141806324158455098511)
                  ·
                    rfl

theorem cell21_1819093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_1819093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819093 prefixEnd_1819093 := by exact prefixLift 1819093
  have htrace : WordTrace (prefixWord ++ tailWord_1819093) baseStart_1819093 baseEnd_1819093 := by
    simpa [prefixWord, tailWord_1819093, baseEnd_1819093] using wordTrace_append hprefix tailTrace_1819093
  have hstable : (prefixWord ++ tailWord_1819093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819093).length < 2 ^ (prefixWord ++ tailWord_1819093).sum := by decide
  have hdescent : baseEnd_1819093 < baseStart_1819093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819121 : List Nat := [1, 2, 2, 2, 3, 1, 2, 5, 3]
def baseStart_1819121 : Nat := 118140960795 + 1819121 * 2 ^ 59
def prefixEnd_1819121 : Nat := 4983230072969 + 3 ^ 40 * 1819121 * 2
def baseEnd_1819121 : Nat := 415148196305636628631787

theorem tailTrace_1819121 : CollatzResearch.WordTrace tailWord_1819121 prefixEnd_1819121 415148196305636628631787 := by
  unfold tailWord_1819121
  simp only [CollatzResearch.WordTrace]
  refine ⟨66348793642642772977321217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44232529095095181984880811 66348793642642772977321217)
  ·
    refine ⟨49761595231982079732990913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66348793642642772977321217 49761595231982079732990913)
    ·
      refine ⟨37321196423986559799743185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49761595231982079732990913 37321196423986559799743185)
      ·
        refine ⟨27990897317989919849807389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37321196423986559799743185 27990897317989919849807389)
        ·
          refine ⟨10496586494246219943677771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27990897317989919849807389 10496586494246219943677771)
          ·
            refine ⟨15744879741369329915516657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10496586494246219943677771 15744879741369329915516657)
            ·
              refine ⟨11808659806026997436637493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15744879741369329915516657 11808659806026997436637493)
              ·
                refine ⟨1107061856815031009684765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11808659806026997436637493 1107061856815031009684765)
                ·
                  refine ⟨415148196305636628631787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107061856815031009684765 415148196305636628631787)
                  ·
                    rfl

theorem cell21_1819121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_1819121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819121 prefixEnd_1819121 := by exact prefixLift 1819121
  have htrace : WordTrace (prefixWord ++ tailWord_1819121) baseStart_1819121 baseEnd_1819121 := by
    simpa [prefixWord, tailWord_1819121, baseEnd_1819121] using wordTrace_append hprefix tailTrace_1819121
  have hstable : (prefixWord ++ tailWord_1819121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819121).length < 2 ^ (prefixWord ++ tailWord_1819121).sum := by decide
  have hdescent : baseEnd_1819121 < baseStart_1819121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819135 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 4]
def baseStart_1819135 : Nat := 118140960795 + 1819135 * 2 ^ 59
def prefixEnd_1819135 : Nat := 4983230072969 + 3 ^ 40 * 1819135 * 2
def baseEnd_1819135 : Nat := 415151391296375715398425

theorem tailTrace_1819135 : CollatzResearch.WordTrace tailWord_1819135 prefixEnd_1819135 415151391296375715398425 := by
  unfold tailWord_1819135
  simp only [CollatzResearch.WordTrace]
  refine ⟨66349304264592053368330859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44232869509728035578887239 66349304264592053368330859)
  ·
    refine ⟨99523956396888080052496289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66349304264592053368330859 99523956396888080052496289)
    ·
      refine ⟨74642967297666060039372217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99523956396888080052496289 74642967297666060039372217)
      ·
        refine ⟨55982225473249545029529163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74642967297666060039372217 55982225473249545029529163)
        ·
          refine ⟨83973338209874317544293745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55982225473249545029529163 83973338209874317544293745)
          ·
            refine ⟨62980003657405738158220309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83973338209874317544293745 62980003657405738158220309)
            ·
              refine ⟨2952187671440893976166577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62980003657405738158220309 2952187671440893976166577)
              ·
                refine ⟨2214140753580670482124933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2952187671440893976166577 2214140753580670482124933)
                ·
                  refine ⟨415151391296375715398425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2214140753580670482124933 415151391296375715398425)
                  ·
                    rfl

theorem cell21_1819135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 4].length) (baseStart_1819135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819135 prefixEnd_1819135 := by exact prefixLift 1819135
  have htrace : WordTrace (prefixWord ++ tailWord_1819135) baseStart_1819135 baseEnd_1819135 := by
    simpa [prefixWord, tailWord_1819135, baseEnd_1819135] using wordTrace_append hprefix tailTrace_1819135
  have hstable : (prefixWord ++ tailWord_1819135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819135).length < 2 ^ (prefixWord ++ tailWord_1819135).sum := by decide
  have hdescent : baseEnd_1819135 < baseStart_1819135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819197 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1819197 : Nat := 118140960795 + 1819197 * 2 ^ 59
def prefixEnd_1819197 : Nat := 4983230072969 + 3 ^ 40 * 1819197 * 2
def baseEnd_1819197 : Nat := 415165540541077385364965

theorem tailTrace_1819197 : CollatzResearch.WordTrace tailWord_1819197 prefixEnd_1819197 415165540541077385364965 := by
  unfold tailWord_1819197
  simp only [CollatzResearch.WordTrace]
  refine ⟨66351565590367437957087845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44234377060244958638058563 66351565590367437957087845)
  ·
    refine ⟨12440918548193894616953971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66351565590367437957087845 12440918548193894616953971)
    ·
      refine ⟨18661377822290841925430957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12440918548193894616953971 18661377822290841925430957)
      ·
        refine ⟨6998016683359065722036609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18661377822290841925430957 6998016683359065722036609)
        ·
          refine ⟨5248512512519299291527457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6998016683359065722036609 5248512512519299291527457)
          ·
            refine ⟨3936384384389474468645593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5248512512519299291527457 3936384384389474468645593)
            ·
              refine ⟨2952288288292105851484195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3936384384389474468645593 2952288288292105851484195)
              ·
                refine ⟨4428432432438158777226293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2952288288292105851484195 4428432432438158777226293)
                ·
                  refine ⟨415165540541077385364965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4428432432438158777226293 415165540541077385364965)
                  ·
                    rfl

theorem cell21_1819197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1819197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819197 prefixEnd_1819197 := by exact prefixLift 1819197
  have htrace : WordTrace (prefixWord ++ tailWord_1819197) baseStart_1819197 baseEnd_1819197 := by
    simpa [prefixWord, tailWord_1819197, baseEnd_1819197] using wordTrace_append hprefix tailTrace_1819197
  have hstable : (prefixWord ++ tailWord_1819197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819197).length < 2 ^ (prefixWord ++ tailWord_1819197).sum := by decide
  have hdescent : baseEnd_1819197 < baseStart_1819197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819332 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1819332 : Nat := 118140960795 + 1819332 * 2 ^ 59
def prefixEnd_1819332 : Nat := 4983230072969 + 3 ^ 40 * 1819332 * 2
def baseEnd_1819332 : Nat := 415196349380347150614689

theorem tailTrace_1819332 : CollatzResearch.WordTrace tailWord_1819332 prefixEnd_1819332 415196349380347150614689 := by
  unfold tailWord_1819332
  simp only [CollatzResearch.WordTrace]
  refine ⟨33178244722439178006626125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44237659629918904008834833 33178244722439178006626125)
  ·
    refine ⟨12441841770914691752484797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33178244722439178006626125 12441841770914691752484797)
    ·
      refine ⟨4665690664093009407181799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12441841770914691752484797 4665690664093009407181799)
      ·
        refine ⟨6998535996139514110772699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4665690664093009407181799 6998535996139514110772699)
        ·
          refine ⟨10497803994209271166159049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6998535996139514110772699 10497803994209271166159049)
          ·
            refine ⟨7873352995656953374619287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10497803994209271166159049 7873352995656953374619287)
            ·
              refine ⟨11810029493485430061928931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7873352995656953374619287 11810029493485430061928931)
              ·
                refine ⟨17715044240228145092893397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11810029493485430061928931 17715044240228145092893397)
                ·
                  refine ⟨415196349380347150614689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17715044240228145092893397 415196349380347150614689)
                  ·
                    rfl

theorem cell21_1819332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1819332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819332 prefixEnd_1819332 := by exact prefixLift 1819332
  have htrace : WordTrace (prefixWord ++ tailWord_1819332) baseStart_1819332 baseEnd_1819332 := by
    simpa [prefixWord, tailWord_1819332, baseEnd_1819332] using wordTrace_append hprefix tailTrace_1819332
  have hstable : (prefixWord ++ tailWord_1819332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819332).length < 2 ^ (prefixWord ++ tailWord_1819332).sum := by decide
  have hdescent : baseEnd_1819332 < baseStart_1819332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819363 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 6]
def baseStart_1819363 : Nat := 118140960795 + 1819363 * 2 ^ 59
def prefixEnd_1819363 : Nat := 4983230072969 + 3 ^ 40 * 1819363 * 2
def baseEnd_1819363 : Nat := 415203424002697985597959

theorem tailTrace_1819363 : CollatzResearch.WordTrace tailWord_1819363 prefixEnd_1819363 415203424002697985597959 := by
  unfold tailWord_1819363
  simp only [CollatzResearch.WordTrace]
  refine ⟨66357620107766048307630743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44238413405177365538420495 66357620107766048307630743)
  ·
    refine ⟨99536430161649072461446115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66357620107766048307630743 99536430161649072461446115)
    ·
      refine ⟨149304645242473608692169173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99536430161649072461446115 149304645242473608692169173)
      ·
        refine ⟨3499327622870475203722715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 149304645242473608692169173 3499327622870475203722715)
        ·
          refine ⟨5248991434305712805584073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3499327622870475203722715 5248991434305712805584073)
          ·
            refine ⟨3936743575729284604188055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5248991434305712805584073 3936743575729284604188055)
            ·
              refine ⟨5905115363593926906282083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936743575729284604188055 5905115363593926906282083)
              ·
                refine ⟨8857673045390890359423125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5905115363593926906282083 8857673045390890359423125)
                ·
                  refine ⟨415203424002697985597959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8857673045390890359423125 415203424002697985597959)
                  ·
                    rfl

theorem cell21_1819363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_1819363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819363 prefixEnd_1819363 := by exact prefixLift 1819363
  have htrace : WordTrace (prefixWord ++ tailWord_1819363) baseStart_1819363 baseEnd_1819363 := by
    simpa [prefixWord, tailWord_1819363, baseEnd_1819363] using wordTrace_append hprefix tailTrace_1819363
  have hstable : (prefixWord ++ tailWord_1819363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819363).length < 2 ^ (prefixWord ++ tailWord_1819363).sum := by decide
  have hdescent : baseEnd_1819363 < baseStart_1819363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819394 : List Nat := [3, 4, 1, 1, 1, 3, 1, 7]
def baseStart_1819394 : Nat := 118140960795 + 1819394 * 2 ^ 59
def prefixEnd_1819394 : Nat := 4983230072969 + 3 ^ 40 * 1819394 * 2
def baseEnd_1819394 : Nat := 138403499541682940193743

theorem tailTrace_1819394 : CollatzResearch.WordTrace tailWord_1819394 prefixEnd_1819394 138403499541682940193743 := by
  unfold tailWord_1819394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16589687692663435150502309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44239167180435827068006157 16589687692663435150502309)
  ·
    refine ⟨3110566442374394090719183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16589687692663435150502309 3110566442374394090719183)
    ·
      refine ⟨4665849663561591136078775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3110566442374394090719183 4665849663561591136078775)
      ·
        refine ⟨6998774495342386704118163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4665849663561591136078775 6998774495342386704118163)
        ·
          refine ⟨10498161743013580056177245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6998774495342386704118163 10498161743013580056177245)
          ·
            refine ⟨3936810653630092521066467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10498161743013580056177245 3936810653630092521066467)
            ·
              refine ⟨5905215980445138781599701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936810653630092521066467 5905215980445138781599701)
              ·
                refine ⟨138403499541682940193743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5905215980445138781599701 138403499541682940193743)
                ·
                  rfl

theorem cell21_1819394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_1819394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819394 prefixEnd_1819394 := by exact prefixLift 1819394
  have htrace : WordTrace (prefixWord ++ tailWord_1819394) baseStart_1819394 baseEnd_1819394 := by
    simpa [prefixWord, tailWord_1819394, baseEnd_1819394] using wordTrace_append hprefix tailTrace_1819394
  have hstable : (prefixWord ++ tailWord_1819394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819394).length < 2 ^ (prefixWord ++ tailWord_1819394).sum := by decide
  have hdescent : baseEnd_1819394 < baseStart_1819394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819476 : List Nat := [2, 4, 1, 1, 5, 1, 2, 2, 3]
def baseStart_1819476 : Nat := 118140960795 + 1819476 * 2 ^ 59
def prefixEnd_1819476 : Nat := 4983230072969 + 3 ^ 40 * 1819476 * 2
def baseEnd_1819476 : Nat := 415229212142234900214395

theorem tailTrace_1819476 : CollatzResearch.WordTrace tailWord_1819476 prefixEnd_1819476 415229212142234900214395 := by
  unfold tailWord_1819476
  simp only [CollatzResearch.WordTrace]
  refine ⟨33180870778178334303247141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44241161037571112404329521 33180870778178334303247141)
  ·
    refine ⟨6221413270908437681858839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33180870778178334303247141 6221413270908437681858839)
    ·
      refine ⟨9332119906362656522788259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6221413270908437681858839 9332119906362656522788259)
      ·
        refine ⟨13998179859543984784182389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9332119906362656522788259 13998179859543984784182389)
        ·
          refine ⟨1312329361832248573517099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13998179859543984784182389 1312329361832248573517099)
          ·
            refine ⟨1968494042748372860275649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312329361832248573517099 1968494042748372860275649)
            ·
              refine ⟨1476370532061279645206737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968494042748372860275649 1476370532061279645206737)
              ·
                refine ⟨1107277899045959733905053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476370532061279645206737 1107277899045959733905053)
                ·
                  refine ⟨415229212142234900214395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107277899045959733905053 415229212142234900214395)
                  ·
                    rfl

theorem cell21_1819476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_1819476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819476 prefixEnd_1819476 := by exact prefixLift 1819476
  have htrace : WordTrace (prefixWord ++ tailWord_1819476) baseStart_1819476 baseEnd_1819476 := by
    simpa [prefixWord, tailWord_1819476, baseEnd_1819476] using wordTrace_append hprefix tailTrace_1819476
  have hstable : (prefixWord ++ tailWord_1819476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819476).length < 2 ^ (prefixWord ++ tailWord_1819476).sum := by decide
  have hdescent : baseEnd_1819476 < baseStart_1819476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819577 : List Nat := [1, 2, 1, 4, 2, 2, 3, 3, 3]
def baseStart_1819577 : Nat := 118140960795 + 1819577 * 2 ^ 59
def prefixEnd_1819577 : Nat := 4983230072969 + 3 ^ 40 * 1819577 * 2
def baseEnd_1819577 : Nat := 415252261718281169030855

theorem tailTrace_1819577 : CollatzResearch.WordTrace tailWord_1819577 prefixEnd_1819577 415252261718281169030855 := by
  unfold tailWord_1819577
  simp only [CollatzResearch.WordTrace]
  refine ⟨66365425328990762855920985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44243616885993841903947323 66365425328990762855920985)
  ·
    refine ⟨49774068996743072141940739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66365425328990762855920985 49774068996743072141940739)
    ·
      refine ⟨74661103495114608212911109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49774068996743072141940739 74661103495114608212911109)
      ·
        refine ⟨13998956905333989039920833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74661103495114608212911109 13998956905333989039920833)
        ·
          refine ⟨10499217679000491779940625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13998956905333989039920833 10499217679000491779940625)
          ·
            refine ⟨7874413259250368834955469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10499217679000491779940625 7874413259250368834955469)
            ·
              refine ⟨2952904972218888313108301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7874413259250368834955469 2952904972218888313108301)
              ·
                refine ⟨1107339364582083117415613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2952904972218888313108301 1107339364582083117415613)
                ·
                  refine ⟨415252261718281169030855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107339364582083117415613 415252261718281169030855)
                  ·
                    rfl

theorem cell21_1819577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 3].length) (baseStart_1819577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819577 prefixEnd_1819577 := by exact prefixLift 1819577
  have htrace : WordTrace (prefixWord ++ tailWord_1819577) baseStart_1819577 baseEnd_1819577 := by
    simpa [prefixWord, tailWord_1819577, baseEnd_1819577] using wordTrace_append hprefix tailTrace_1819577
  have hstable : (prefixWord ++ tailWord_1819577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819577).length < 2 ^ (prefixWord ++ tailWord_1819577).sum := by decide
  have hdescent : baseEnd_1819577 < baseStart_1819577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819608 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 4]
def baseStart_1819608 : Nat := 118140960795 + 1819608 * 2 ^ 59
def prefixEnd_1819608 : Nat := 4983230072969 + 3 ^ 40 * 1819608 * 2
def baseEnd_1819608 : Nat := 415259336340632004014125

theorem tailTrace_1819608 : CollatzResearch.WordTrace tailWord_1819608 prefixEnd_1819608 415259336340632004014125 := by
  unfold tailWord_1819608
  simp only [CollatzResearch.WordTrace]
  refine ⟨33183277995939227575149739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44244370661252303433532985 33183277995939227575149739)
  ·
    refine ⟨49774916993908841362724609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33183277995939227575149739 49774916993908841362724609)
    ·
      refine ⟨37331187745431631022043457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49774916993908841362724609 37331187745431631022043457)
      ·
        refine ⟨27998390809073723266532593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37331187745431631022043457 27998390809073723266532593)
        ·
          refine ⟨20998793106805292449899445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27998390809073723266532593 20998793106805292449899445)
          ·
            refine ⟨1968636853762996167178073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20998793106805292449899445 1968636853762996167178073)
            ·
              refine ⟨1476477640322247125383555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968636853762996167178073 1476477640322247125383555)
              ·
                refine ⟨2214716460483370688075333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476477640322247125383555 2214716460483370688075333)
                ·
                  refine ⟨415259336340632004014125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2214716460483370688075333 415259336340632004014125)
                  ·
                    rfl

theorem cell21_1819608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 4].length) (baseStart_1819608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819608 prefixEnd_1819608 := by exact prefixLift 1819608
  have htrace : WordTrace (prefixWord ++ tailWord_1819608) baseStart_1819608 baseEnd_1819608 := by
    simpa [prefixWord, tailWord_1819608, baseEnd_1819608] using wordTrace_append hprefix tailTrace_1819608
  have hstable : (prefixWord ++ tailWord_1819608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819608).length < 2 ^ (prefixWord ++ tailWord_1819608).sum := by decide
  have hdescent : baseEnd_1819608 < baseStart_1819608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819619 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 7]
def baseStart_1819619 : Nat := 118140960795 + 1819619 * 2 ^ 59
def prefixEnd_1819619 : Nat := 4983230072969 + 3 ^ 40 * 1819619 * 2
def baseEnd_1819619 : Nat := 415261846690498429330769

theorem tailTrace_1819619 : CollatzResearch.WordTrace tailWord_1819619 prefixEnd_1819619 415261846690498429330769 := by
  unfold tailWord_1819619
  simp only [CollatzResearch.WordTrace]
  refine ⟨66366957194838604028949911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44244638129892402685966607 66366957194838604028949911)
  ·
    refine ⟨99550435792257906043424867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66366957194838604028949911 99550435792257906043424867)
    ·
      refine ⟨149325653688386859065137301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99550435792257906043424867 149325653688386859065137301)
      ·
        refine ⟨6999640016643134018678311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149325653688386859065137301 6999640016643134018678311)
        ·
          refine ⟨10499460024964701028017467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6999640016643134018678311 10499460024964701028017467)
          ·
            refine ⟨15749190037447051542026201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10499460024964701028017467 15749190037447051542026201)
            ·
              refine ⟨11811892528085288656519651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15749190037447051542026201 11811892528085288656519651)
              ·
                refine ⟨17717838792127932984779477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11811892528085288656519651 17717838792127932984779477)
                ·
                  refine ⟨415261846690498429330769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17717838792127932984779477 415261846690498429330769)
                  ·
                    rfl

theorem cell21_1819619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_1819619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819619 prefixEnd_1819619 := by exact prefixLift 1819619
  have htrace : WordTrace (prefixWord ++ tailWord_1819619) baseStart_1819619 baseEnd_1819619 := by
    simpa [prefixWord, tailWord_1819619, baseEnd_1819619] using wordTrace_append hprefix tailTrace_1819619
  have hstable : (prefixWord ++ tailWord_1819619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819619).length < 2 ^ (prefixWord ++ tailWord_1819619).sum := by decide
  have hdescent : baseEnd_1819619 < baseStart_1819619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819712 : List Nat := [2, 1, 1, 2, 2, 3, 1, 6, 3]
def baseStart_1819712 : Nat := 118140960795 + 1819712 * 2 ^ 59
def prefixEnd_1819712 : Nat := 4983230072969 + 3 ^ 40 * 1819712 * 2
def baseEnd_1819712 : Nat := 415283070557550934280579

theorem tailTrace_1819712 : CollatzResearch.WordTrace tailWord_1819712 prefixEnd_1819712 415283070557550934280579 := by
  unfold tailWord_1819712
  simp only [CollatzResearch.WordTrace]
  refine ⟨33185174591750840456042695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44246899455667787274723593 33185174591750840456042695)
  ·
    refine ⟨49777761887626260684064043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33185174591750840456042695 49777761887626260684064043)
    ·
      refine ⟨74666642831439391026096065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49777761887626260684064043 74666642831439391026096065)
      ·
        refine ⟨55999982123579543269572049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74666642831439391026096065 55999982123579543269572049)
        ·
          refine ⟨41999986592684657452179037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55999982123579543269572049 41999986592684657452179037)
          ·
            refine ⟨15749994972256746544567139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41999986592684657452179037 15749994972256746544567139)
            ·
              refine ⟨23624992458385119816850709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15749994972256746544567139 23624992458385119816850709)
              ·
                refine ⟨1107421521486802491414877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23624992458385119816850709 1107421521486802491414877)
                ·
                  refine ⟨415283070557550934280579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107421521486802491414877 415283070557550934280579)
                  ·
                    rfl

theorem cell21_1819712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 3].length) (baseStart_1819712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819712 prefixEnd_1819712 := by exact prefixLift 1819712
  have htrace : WordTrace (prefixWord ++ tailWord_1819712) baseStart_1819712 baseEnd_1819712 := by
    simpa [prefixWord, tailWord_1819712, baseEnd_1819712] using wordTrace_append hprefix tailTrace_1819712
  have hstable : (prefixWord ++ tailWord_1819712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819712).length < 2 ^ (prefixWord ++ tailWord_1819712).sum := by decide
  have hdescent : baseEnd_1819712 < baseStart_1819712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819746 : List Nat := [3, 3, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1819746 : Nat := 118140960795 + 1819746 * 2 ^ 59
def prefixEnd_1819746 : Nat := 4983230072969 + 3 ^ 40 * 1819746 * 2
def baseEnd_1819746 : Nat := 415290829820774430713843

theorem tailTrace_1819746 : CollatzResearch.WordTrace tailWord_1819746 prefixEnd_1819746 415290829820774430713843 := by
  unfold tailWord_1819746
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592897316344626179705773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44247726176919003145882061 16592897316344626179705773)
  ·
    refine ⟨6222336493629234817389665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16592897316344626179705773 6222336493629234817389665)
    ·
      refine ⟨4666752370221926113042249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6222336493629234817389665 4666752370221926113042249)
      ·
        refine ⟨3500064277666444584781687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4666752370221926113042249 3500064277666444584781687)
        ·
          refine ⟨5250096416499666877172531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500064277666444584781687 5250096416499666877172531)
          ·
            refine ⟨7875144624749500315758797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250096416499666877172531 7875144624749500315758797)
            ·
              refine ⟨2953179234281062618409549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7875144624749500315758797 2953179234281062618409549)
              ·
                refine ⟨1107442212855398481903581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2953179234281062618409549 1107442212855398481903581)
                ·
                  refine ⟨415290829820774430713843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107442212855398481903581 415290829820774430713843)
                  ·
                    rfl

theorem cell21_1819746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1819746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819746 prefixEnd_1819746 := by exact prefixLift 1819746
  have htrace : WordTrace (prefixWord ++ tailWord_1819746) baseStart_1819746 baseEnd_1819746 := by
    simpa [prefixWord, tailWord_1819746, baseEnd_1819746] using wordTrace_append hprefix tailTrace_1819746
  have hstable : (prefixWord ++ tailWord_1819746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819746).length < 2 ^ (prefixWord ++ tailWord_1819746).sum := by decide
  have hdescent : baseEnd_1819746 < baseStart_1819746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819757 : List Nat := [1, 5, 1, 1, 2, 4, 7]
def baseStart_1819757 : Nat := 118140960795 + 1819757 * 2 ^ 59
def prefixEnd_1819757 : Nat := 4983230072969 + 3 ^ 40 * 1819757 * 2
def baseEnd_1819757 : Nat := 46143704463404539558943

theorem tailTrace_1819757 : CollatzResearch.WordTrace tailWord_1819757 prefixEnd_1819757 46143704463404539558943 := by
  unfold tailWord_1819757
  simp only [CollatzResearch.WordTrace]
  refine ⟨66371990468338653597473525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44247993645559102398315683 66371990468338653597473525)
  ·
    refine ⟨6222374106406748774763143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66371990468338653597473525 6222374106406748774763143)
    ·
      refine ⟨9333561159610123162144715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6222374106406748774763143 9333561159610123162144715)
      ·
        refine ⟨14000341739415184743217073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9333561159610123162144715 14000341739415184743217073)
        ·
          refine ⟨10500256304561388557412805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14000341739415184743217073 10500256304561388557412805)
          ·
            refine ⟨1968798057105260354514901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10500256304561388557412805 1968798057105260354514901)
            ·
              refine ⟨46143704463404539558943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1968798057105260354514901 46143704463404539558943)
              ·
                rfl

theorem cell21_1819757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 7].length) (baseStart_1819757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819757 prefixEnd_1819757 := by exact prefixLift 1819757
  have htrace : WordTrace (prefixWord ++ tailWord_1819757) baseStart_1819757 baseEnd_1819757 := by
    simpa [prefixWord, tailWord_1819757, baseEnd_1819757] using wordTrace_append hprefix tailTrace_1819757
  have hstable : (prefixWord ++ tailWord_1819757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819757).length < 2 ^ (prefixWord ++ tailWord_1819757).sum := by decide
  have hdescent : baseEnd_1819757 < baseStart_1819757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1819833 : List Nat := [1, 2, 1, 4, 1, 5, 1, 6]
def baseStart_1819833 : Nat := 118140960795 + 1819833 * 2 ^ 59
def prefixEnd_1819833 : Nat := 4983230072969 + 3 ^ 40 * 1819833 * 2
def baseEnd_1819833 : Nat := 138436894802027204254555

theorem tailTrace_1819833 : CollatzResearch.WordTrace tailWord_1819833 prefixEnd_1819833 138436894802027204254555 := by
  unfold tailWord_1819833
  simp only [CollatzResearch.WordTrace]
  refine ⟨66374762416063318577240153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44249841610708879051493435 66374762416063318577240153)
  ·
    refine ⟨49781071812047488932930115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66374762416063318577240153 49781071812047488932930115)
    ·
      refine ⟨74671607718071233399395173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49781071812047488932930115 74671607718071233399395173)
      ·
        refine ⟨14000926447138356262386595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74671607718071233399395173 14000926447138356262386595)
        ·
          refine ⟨21001389670707534393579893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14000926447138356262386595 21001389670707534393579893)
          ·
            refine ⟨1968880281628831349398115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21001389670707534393579893 1968880281628831349398115)
            ·
              refine ⟨2953320422443247024097173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968880281628831349398115 2953320422443247024097173)
              ·
                refine ⟨138436894802027204254555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2953320422443247024097173 138436894802027204254555)
                ·
                  rfl

theorem cell21_1819833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 6].length) (baseStart_1819833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1819833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1819833 prefixEnd_1819833 := by exact prefixLift 1819833
  have htrace : WordTrace (prefixWord ++ tailWord_1819833) baseStart_1819833 baseEnd_1819833 := by
    simpa [prefixWord, tailWord_1819833, baseEnd_1819833] using wordTrace_append hprefix tailTrace_1819833
  have hstable : (prefixWord ++ tailWord_1819833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1819833).length < 2 ^ (prefixWord ++ tailWord_1819833).sum := by decide
  have hdescent : baseEnd_1819833 < baseStart_1819833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1819833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820210 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_1820210 : Nat := 118140960795 + 1820210 * 2 ^ 59
def prefixEnd_1820210 : Nat := 4983230072969 + 3 ^ 40 * 1820210 * 2
def baseEnd_1820210 : Nat := 415396720942412734979561

theorem tailTrace_1820210 : CollatzResearch.WordTrace tailWord_1820210 prefixEnd_1820210 415396720942412734979561 := by
  unfold tailWord_1820210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16597128183924377990928521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44259008490465007975809389 16597128183924377990928521)
  ·
    refine ⟨12447846137943283493196391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16597128183924377990928521 12447846137943283493196391)
    ·
      refine ⟨18671769206914925239794587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12447846137943283493196391 18671769206914925239794587)
      ·
        refine ⟨28007653810372387859691881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18671769206914925239794587 28007653810372387859691881)
        ·
          refine ⟨21005740357779290894768911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28007653810372387859691881 21005740357779290894768911)
          ·
            refine ⟨31508610536668936342153367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21005740357779290894768911 31508610536668936342153367)
            ·
              refine ⟨47262915805003404513230051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31508610536668936342153367 47262915805003404513230051)
              ·
                refine ⟨70894373707505106769845077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47262915805003404513230051 70894373707505106769845077)
                ·
                  refine ⟨415396720942412734979561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70894373707505106769845077 415396720942412734979561)
                  ·
                    rfl

theorem cell21_1820210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_1820210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820210 prefixEnd_1820210 := by exact prefixLift 1820210
  have htrace : WordTrace (prefixWord ++ tailWord_1820210) baseStart_1820210 baseEnd_1820210 := by
    simpa [prefixWord, tailWord_1820210, baseEnd_1820210] using wordTrace_append hprefix tailTrace_1820210
  have hstable : (prefixWord ++ tailWord_1820210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820210).length < 2 ^ (prefixWord ++ tailWord_1820210).sum := by decide
  have hdescent : baseEnd_1820210 < baseStart_1820210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820261 : List Nat := [1, 3, 1, 3, 3, 3, 1, 3, 3]
def baseStart_1820261 : Nat := 118140960795 + 1820261 * 2 ^ 59
def prefixEnd_1820261 : Nat := 4983230072969 + 3 ^ 40 * 1820261 * 2
def baseEnd_1820261 : Nat := 415408359837247979629457

theorem tailTrace_1820261 : CollatzResearch.WordTrace tailWord_1820261 prefixEnd_1820261 415408359837247979629457 := by
  unfold tailWord_1820261
  simp only [CollatzResearch.WordTrace]
  refine ⟨66390372858512747673820637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44260248572341831782547091 66390372858512747673820637)
  ·
    refine ⟨24896389821942280377682739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66390372858512747673820637 24896389821942280377682739)
    ·
      refine ⟨37344584732913420566524109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24896389821942280377682739 37344584732913420566524109)
      ·
        refine ⟨14004219274842532712446541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37344584732913420566524109 14004219274842532712446541)
        ·
          refine ⟨5251582228065949767167453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14004219274842532712446541 5251582228065949767167453)
          ·
            refine ⟨1969343335524731162687795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5251582228065949767167453 1969343335524731162687795)
            ·
              refine ⟨2954015003287096744031693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969343335524731162687795 2954015003287096744031693)
              ·
                refine ⟨1107755626232661279011885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2954015003287096744031693 1107755626232661279011885)
                ·
                  refine ⟨415408359837247979629457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107755626232661279011885 415408359837247979629457)
                  ·
                    rfl

theorem cell21_1820261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_1820261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820261 prefixEnd_1820261 := by exact prefixLift 1820261
  have htrace : WordTrace (prefixWord ++ tailWord_1820261) baseStart_1820261 baseEnd_1820261 := by
    simpa [prefixWord, tailWord_1820261, baseEnd_1820261] using wordTrace_append hprefix tailTrace_1820261
  have hstable : (prefixWord ++ tailWord_1820261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820261).length < 2 ^ (prefixWord ++ tailWord_1820261).sum := by decide
  have hdescent : baseEnd_1820261 < baseStart_1820261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820272 : List Nat := [2, 1, 1, 1, 6, 3, 7]
def baseStart_1820272 : Nat := 118140960795 + 1820272 * 2 ^ 59
def prefixEnd_1820272 : Nat := 4983230072969 + 3 ^ 40 * 1820272 * 2
def baseEnd_1820272 : Nat := 46156763354123822771789

theorem tailTrace_1820272 : CollatzResearch.WordTrace tailWord_1820272 prefixEnd_1820272 46156763354123822771789 := by
  unfold tailWord_1820272
  simp only [CollatzResearch.WordTrace]
  refine ⟨33195387030736448276235535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44260516040981931034980713 33195387030736448276235535)
  ·
    refine ⟨49793080546104672414353303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33195387030736448276235535 49793080546104672414353303)
    ·
      refine ⟨74689620819157008621529955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49793080546104672414353303 74689620819157008621529955)
      ·
        refine ⟨112034431228735512932294933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74689620819157008621529955 112034431228735512932294933)
        ·
          refine ⟨5251613963846977168701325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112034431228735512932294933 5251613963846977168701325)
          ·
            refine ⟨1969355236442616438262997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5251613963846977168701325 1969355236442616438262997)
            ·
              refine ⟨46156763354123822771789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1969355236442616438262997 46156763354123822771789)
              ·
                rfl

theorem cell21_1820272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 7].length) (baseStart_1820272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820272 prefixEnd_1820272 := by exact prefixLift 1820272
  have htrace : WordTrace (prefixWord ++ tailWord_1820272) baseStart_1820272 baseEnd_1820272 := by
    simpa [prefixWord, tailWord_1820272, baseEnd_1820272] using wordTrace_append hprefix tailTrace_1820272
  have hstable : (prefixWord ++ tailWord_1820272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820272).length < 2 ^ (prefixWord ++ tailWord_1820272).sum := by decide
  have hdescent : baseEnd_1820272 < baseStart_1820272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820278 : List Nat := [5, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1820278 : Nat := 118140960795 + 1820278 * 2 ^ 59
def prefixEnd_1820278 : Nat := 4983230072969 + 3 ^ 40 * 1820278 * 2
def baseEnd_1820278 : Nat := 415412239468859727846089

theorem tailTrace_1820278 : CollatzResearch.WordTrace tailWord_1820278 prefixEnd_1820278 415412239468859727846089 := by
  unfold tailWord_1820278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4149437056215697473574343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44260661932967439718126325 4149437056215697473574343)
  ·
    refine ⟨6224155584323546210361515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4149437056215697473574343 6224155584323546210361515)
    ·
      refine ⟨9336233376485319315542273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6224155584323546210361515 9336233376485319315542273)
      ·
        refine ⟨7002175032363989486656705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9336233376485319315542273 7002175032363989486656705)
        ·
          refine ⟨5251631274272992114992529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7002175032363989486656705 5251631274272992114992529)
          ·
            refine ⟨3938723455704744086244397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5251631274272992114992529 3938723455704744086244397)
            ·
              refine ⟨1477021295889279032341649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3938723455704744086244397 1477021295889279032341649)
              ·
                refine ⟨1107765971916959274256237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1477021295889279032341649 1107765971916959274256237)
                ·
                  refine ⟨415412239468859727846089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107765971916959274256237 415412239468859727846089)
                  ·
                    rfl

theorem cell21_1820278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1820278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820278 prefixEnd_1820278 := by exact prefixLift 1820278
  have htrace : WordTrace (prefixWord ++ tailWord_1820278) baseStart_1820278 baseEnd_1820278 := by
    simpa [prefixWord, tailWord_1820278, baseEnd_1820278] using wordTrace_append hprefix tailTrace_1820278
  have hstable : (prefixWord ++ tailWord_1820278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820278).length < 2 ^ (prefixWord ++ tailWord_1820278).sum := by decide
  have hdescent : baseEnd_1820278 < baseStart_1820278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820292 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 4]
def baseStart_1820292 : Nat := 118140960795 + 1820292 * 2 ^ 59
def prefixEnd_1820292 : Nat := 4983230072969 + 3 ^ 40 * 1820292 * 2
def baseEnd_1820292 : Nat := 415415434459598814612727

theorem tailTrace_1820292 : CollatzResearch.WordTrace tailWord_1820292 prefixEnd_1820292 415415434459598814612727 := by
  unfold tailWord_1820292
  simp only [CollatzResearch.WordTrace]
  refine ⟨33195751760700219984099565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44261002347600293312132753 33195751760700219984099565)
  ·
    refine ⟨12448406910262582494037337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33195751760700219984099565 12448406910262582494037337)
    ·
      refine ⟨9336305182696936870528003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12448406910262582494037337 9336305182696936870528003)
      ·
        refine ⟨14004457774045405305792005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9336305182696936870528003 14004457774045405305792005)
        ·
          refine ⟨2625835832633513494836001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14004457774045405305792005 2625835832633513494836001)
          ·
            refine ⟨1969376874475135121127001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2625835832633513494836001 1969376874475135121127001)
            ·
              refine ⟨1477032655856351340845251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1969376874475135121127001 1477032655856351340845251)
              ·
                refine ⟨2215548983784527011267877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477032655856351340845251 2215548983784527011267877)
                ·
                  refine ⟨415415434459598814612727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2215548983784527011267877 415415434459598814612727)
                  ·
                    rfl

theorem cell21_1820292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_1820292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820292 prefixEnd_1820292 := by exact prefixLift 1820292
  have htrace : WordTrace (prefixWord ++ tailWord_1820292) baseStart_1820292 baseEnd_1820292 := by
    simpa [prefixWord, tailWord_1820292, baseEnd_1820292] using wordTrace_append hprefix tailTrace_1820292
  have hstable : (prefixWord ++ tailWord_1820292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820292).length < 2 ^ (prefixWord ++ tailWord_1820292).sum := by decide
  have hdescent : baseEnd_1820292 < baseStart_1820292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820348 : List Nat := [2, 2, 2, 3, 1, 2, 3, 6]
def baseStart_1820348 : Nat := 118140960795 + 1820348 * 2 ^ 59
def prefixEnd_1820348 : Nat := 4983230072969 + 3 ^ 40 * 1820348 * 2
def baseEnd_1820348 : Nat := 138476071474185053893093

theorem tailTrace_1820348 : CollatzResearch.WordTrace tailWord_1820348 prefixEnd_1820348 138476071474185053893093 := by
  unfold tailWord_1820348
  simp only [CollatzResearch.WordTrace]
  refine ⟨33196773004598780766118849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44262364006131707688158465 33196773004598780766118849)
  ·
    refine ⟨24897579753449085574589137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33196773004598780766118849 24897579753449085574589137)
    ·
      refine ⟨18673184815086814180941853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24897579753449085574589137 18673184815086814180941853)
      ·
        refine ⟨7002444305657555317853195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18673184815086814180941853 7002444305657555317853195)
        ·
          refine ⟨10503666458486332976779793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7002444305657555317853195 10503666458486332976779793)
          ·
            refine ⟨7877749843864749732584845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10503666458486332976779793 7877749843864749732584845)
            ·
              refine ⟨2954156191449281149719317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7877749843864749732584845 2954156191449281149719317)
              ·
                refine ⟨138476071474185053893093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2954156191449281149719317 138476071474185053893093)
                ·
                  rfl

theorem cell21_1820348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 6].length) (baseStart_1820348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820348 prefixEnd_1820348 := by exact prefixLift 1820348
  have htrace : WordTrace (prefixWord ++ tailWord_1820348) baseStart_1820348 baseEnd_1820348 := by
    simpa [prefixWord, tailWord_1820348, baseEnd_1820348] using wordTrace_append hprefix tailTrace_1820348
  have hstable : (prefixWord ++ tailWord_1820348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820348).length < 2 ^ (prefixWord ++ tailWord_1820348).sum := by decide
  have hdescent : baseEnd_1820348 < baseStart_1820348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820354 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1820354 : Nat := 118140960795 + 1820354 * 2 ^ 59
def prefixEnd_1820354 : Nat := 4983230072969 + 3 ^ 40 * 1820354 * 2
def baseEnd_1820354 : Nat := 415429583704300484579267

theorem tailTrace_1820354 : CollatzResearch.WordTrace tailWord_1820354 prefixEnd_1820354 415429583704300484579267 := by
  unfold tailWord_1820354
  simp only [CollatzResearch.WordTrace]
  refine ⟨16598441211793956139239029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44262509898117216371304077 16598441211793956139239029)
  ·
    refine ⟨1556103863605683388053659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16598441211793956139239029 1556103863605683388053659)
    ·
      refine ⟨2334155795408525082080489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1556103863605683388053659 2334155795408525082080489)
      ·
        refine ⟨1750616846556393811560367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2334155795408525082080489 1750616846556393811560367)
        ·
          refine ⟨2625925269834590717340551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750616846556393811560367 2625925269834590717340551)
          ·
            refine ⟨3938887904751886076010827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625925269834590717340551 3938887904751886076010827)
            ·
              refine ⟨5908331857127829114016241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3938887904751886076010827 5908331857127829114016241)
              ·
                refine ⟨4431248892845871835512181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5908331857127829114016241 4431248892845871835512181)
                ·
                  refine ⟨415429583704300484579267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4431248892845871835512181 415429583704300484579267)
                  ·
                    rfl

theorem cell21_1820354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1820354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820354 prefixEnd_1820354 := by exact prefixLift 1820354
  have htrace : WordTrace (prefixWord ++ tailWord_1820354) baseStart_1820354 baseEnd_1820354 := by
    simpa [prefixWord, tailWord_1820354, baseEnd_1820354] using wordTrace_append hprefix tailTrace_1820354
  have hstable : (prefixWord ++ tailWord_1820354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820354).length < 2 ^ (prefixWord ++ tailWord_1820354).sum := by decide
  have hdescent : baseEnd_1820354 < baseStart_1820354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820422 : List Nat := [6, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1820422 : Nat := 118140960795 + 1820422 * 2 ^ 59
def prefixEnd_1820422 : Nat := 4983230072969 + 3 ^ 40 * 1820422 * 2
def baseEnd_1820422 : Nat := 415445102230747477445795

theorem tailTrace_1820422 : CollatzResearch.WordTrace tailWord_1820422 prefixEnd_1820422 415445102230747477445795 := by
  unfold tailWord_1820422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074882656591546005325985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44264163340619648113621013 2074882656591546005325985)
  ·
    refine ⟨1556161992443659503994489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2074882656591546005325985 1556161992443659503994489)
    ·
      refine ⟨1167121494332744627995867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1556161992443659503994489 1167121494332744627995867)
      ·
        refine ⟨1750682241499116941993801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167121494332744627995867 1750682241499116941993801)
        ·
          refine ⟨1313011681124337706495351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1750682241499116941993801 1313011681124337706495351)
          ·
            refine ⟨1969517521686506559743027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313011681124337706495351 1969517521686506559743027)
            ·
              refine ⟨2954276282529759839614541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969517521686506559743027 2954276282529759839614541)
              ·
                refine ⟨1107853605948659939855453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2954276282529759839614541 1107853605948659939855453)
                ·
                  refine ⟨415445102230747477445795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107853605948659939855453 415445102230747477445795)
                  ·
                    rfl

theorem cell21_1820422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1820422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820422 prefixEnd_1820422 := by exact prefixLift 1820422
  have htrace : WordTrace (prefixWord ++ tailWord_1820422) baseStart_1820422 baseEnd_1820422 := by
    simpa [prefixWord, tailWord_1820422, baseEnd_1820422] using wordTrace_append hprefix tailTrace_1820422
  have hstable : (prefixWord ++ tailWord_1820422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820422).length < 2 ^ (prefixWord ++ tailWord_1820422).sum := by decide
  have hdescent : baseEnd_1820422 < baseStart_1820422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820483 : List Nat := [1, 1, 1, 3, 1, 5, 2, 7]
def baseStart_1820483 : Nat := 118140960795 + 1820483 * 2 ^ 59
def prefixEnd_1820483 : Nat := 4983230072969 + 3 ^ 40 * 1820483 * 2
def baseEnd_1820483 : Nat := 138486341087274975643001

theorem tailTrace_1820483 : CollatzResearch.WordTrace tailWord_1820483 prefixEnd_1820483 138486341087274975643001 := by
  unfold tailWord_1820483
  simp only [CollatzResearch.WordTrace]
  refine ⟨66398469863708479588402103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44265646575805653058934735 66398469863708479588402103)
  ·
    refine ⟨99597704795562719382603155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66398469863708479588402103 99597704795562719382603155)
    ·
      refine ⟨149396557193344079073904733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99597704795562719382603155 149396557193344079073904733)
      ·
        refine ⟨56023708947504029652714275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149396557193344079073904733 56023708947504029652714275)
        ·
          refine ⟨84035563421256044479071413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56023708947504029652714275 84035563421256044479071413)
          ·
            refine ⟨7878334070742754169912945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84035563421256044479071413 7878334070742754169912945)
            ·
              refine ⟨5908750553057065627434709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7878334070742754169912945 5908750553057065627434709)
              ·
                refine ⟨138486341087274975643001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5908750553057065627434709 138486341087274975643001)
                ·
                  rfl

theorem cell21_1820483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 7].length) (baseStart_1820483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820483 prefixEnd_1820483 := by exact prefixLift 1820483
  have htrace : WordTrace (prefixWord ++ tailWord_1820483) baseStart_1820483 baseEnd_1820483 := by
    simpa [prefixWord, tailWord_1820483, baseEnd_1820483] using wordTrace_append hprefix tailTrace_1820483
  have hstable : (prefixWord ++ tailWord_1820483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820483).length < 2 ^ (prefixWord ++ tailWord_1820483).sum := by decide
  have hdescent : baseEnd_1820483 < baseStart_1820483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820528 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_1820528 : Nat := 118140960795 + 1820528 * 2 ^ 59
def prefixEnd_1820528 : Nat := 4983230072969 + 3 ^ 40 * 1820528 * 2
def baseEnd_1820528 : Nat := 415469292874914848678911

theorem tailTrace_1820528 : CollatzResearch.WordTrace tailWord_1820528 prefixEnd_1820528 415469292874914848678911 := by
  unfold tailWord_1820528
  simp only [CollatzResearch.WordTrace]
  refine ⟨33200055574272726136895119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44266740765696968182526825 33200055574272726136895119)
  ·
    refine ⟨49800083361409089205342679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33200055574272726136895119 49800083361409089205342679)
    ·
      refine ⟨74700125042113633808014019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49800083361409089205342679 74700125042113633808014019)
      ·
        refine ⟨112050187563170450712021029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74700125042113633808014019 112050187563170450712021029)
        ·
          refine ⟨21009410168094459508503943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112050187563170450712021029 21009410168094459508503943)
          ·
            refine ⟨31514115252141689262755915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21009410168094459508503943 31514115252141689262755915)
            ·
              refine ⟨47271172878212533894133873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31514115252141689262755915 47271172878212533894133873)
              ·
                refine ⟨35453379658659400420600405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47271172878212533894133873 35453379658659400420600405)
                ·
                  refine ⟨415469292874914848678911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35453379658659400420600405 415469292874914848678911)
                  ·
                    rfl

theorem cell21_1820528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_1820528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820528 prefixEnd_1820528 := by exact prefixLift 1820528
  have htrace : WordTrace (prefixWord ++ tailWord_1820528) baseStart_1820528 baseEnd_1820528 := by
    simpa [prefixWord, tailWord_1820528, baseEnd_1820528] using wordTrace_append hprefix tailTrace_1820528
  have hstable : (prefixWord ++ tailWord_1820528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820528).length < 2 ^ (prefixWord ++ tailWord_1820528).sum := by decide
  have hdescent : baseEnd_1820528 < baseStart_1820528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820534 : List Nat := [5, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1820534 : Nat := 118140960795 + 1820534 * 2 ^ 59
def prefixEnd_1820534 : Nat := 4983230072969 + 3 ^ 40 * 1820534 * 2
def baseEnd_1820534 : Nat := 138490220718886723859633

theorem tailTrace_1820534 : CollatzResearch.WordTrace tailWord_1820534 prefixEnd_1820534 138490220718886723859633 := by
  unfold tailWord_1820534
  simp only [CollatzResearch.WordTrace]
  refine ⟨4150020624157732206156791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44266886657682476865672437 4150020624157732206156791)
  ·
    refine ⟨6225030936236598309235187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4150020624157732206156791 6225030936236598309235187)
    ·
      refine ⟨9337546404354897463852781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6225030936236598309235187 9337546404354897463852781)
      ·
        refine ⟨3501579901633086548944793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9337546404354897463852781 3501579901633086548944793)
        ·
          refine ⟨2626184926224814911708595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3501579901633086548944793 2626184926224814911708595)
          ·
            refine ⟨3939277389337222367562893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626184926224814911708595 3939277389337222367562893)
            ·
              refine ⟨1477229021001458387836085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3939277389337222367562893 1477229021001458387836085)
              ·
                refine ⟨138490220718886723859633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1477229021001458387836085 138490220718886723859633)
                ·
                  rfl

theorem cell21_1820534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1820534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820534 prefixEnd_1820534 := by exact prefixLift 1820534
  have htrace : WordTrace (prefixWord ++ tailWord_1820534) baseStart_1820534 baseEnd_1820534 := by
    simpa [prefixWord, tailWord_1820534, baseEnd_1820534] using wordTrace_append hprefix tailTrace_1820534
  have hstable : (prefixWord ++ tailWord_1820534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820534).length < 2 ^ (prefixWord ++ tailWord_1820534).sum := by decide
  have hdescent : baseEnd_1820534 < baseStart_1820534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820562 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1820562 : Nat := 118140960795 + 1820562 * 2 ^ 59
def prefixEnd_1820562 : Nat := 4983230072969 + 3 ^ 40 * 1820562 * 2
def baseEnd_1820562 : Nat := 415477052138138345112175

theorem tailTrace_1820562 : CollatzResearch.WordTrace tailWord_1820562 prefixEnd_1820562 415477052138138345112175 := by
  unfold tailWord_1820562
  simp only [CollatzResearch.WordTrace]
  refine ⟨16600337807605569020131985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44267567486948184053685293 16600337807605569020131985)
  ·
    refine ⟨12450253355704176765098989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16600337807605569020131985 12450253355704176765098989)
    ·
      refine ⟨4668845008389066286912121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12450253355704176765098989 4668845008389066286912121)
      ·
        refine ⟨3501633756291799715184091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4668845008389066286912121 3501633756291799715184091)
        ·
          refine ⟨5252450634437699572776137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3501633756291799715184091 5252450634437699572776137)
          ·
            refine ⟨3939337975828274679582103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5252450634437699572776137 3939337975828274679582103)
            ·
              refine ⟨5909006963742412019373155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3939337975828274679582103 5909006963742412019373155)
              ·
                refine ⟨8863510445613618029059733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5909006963742412019373155 8863510445613618029059733)
                ·
                  refine ⟨415477052138138345112175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8863510445613618029059733 415477052138138345112175)
                  ·
                    rfl

theorem cell21_1820562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1820562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820562 prefixEnd_1820562 := by exact prefixLift 1820562
  have htrace : WordTrace (prefixWord ++ tailWord_1820562) baseStart_1820562 baseEnd_1820562 := by
    simpa [prefixWord, tailWord_1820562, baseEnd_1820562] using wordTrace_append hprefix tailTrace_1820562
  have hstable : (prefixWord ++ tailWord_1820562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820562).length < 2 ^ (prefixWord ++ tailWord_1820562).sum := by decide
  have hdescent : baseEnd_1820562 < baseStart_1820562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820593 : List Nat := [1, 2, 2, 4, 2, 3, 2, 5]
def baseStart_1820593 : Nat := 118140960795 + 1820593 * 2 ^ 59
def prefixEnd_1820593 : Nat := 4983230072969 + 3 ^ 40 * 1820593 * 2
def baseEnd_1820593 : Nat := 138494708920163060031815

theorem tailTrace_1820593 : CollatzResearch.WordTrace tailWord_1820593 prefixEnd_1820593 138494708920163060031815 := by
  unfold tailWord_1820593
  simp only [CollatzResearch.WordTrace]
  refine ⟨66402481893309968374906433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44268321262206645583270955 66402481893309968374906433)
  ·
    refine ⟨49801861419982476281179825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66402481893309968374906433 49801861419982476281179825)
    ·
      refine ⟨37351396064986857210884869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49801861419982476281179825 37351396064986857210884869)
      ·
        refine ⟨7003386762185035727040913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37351396064986857210884869 7003386762185035727040913)
        ·
          refine ⟨5252540071638776795280685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7003386762185035727040913 5252540071638776795280685)
          ·
            refine ⟨1969702526864541298230257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5252540071638776795280685 1969702526864541298230257)
            ·
              refine ⟨1477276895148405973672693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1969702526864541298230257 1477276895148405973672693)
              ·
                refine ⟨138494708920163060031815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1477276895148405973672693 138494708920163060031815)
                ·
                  rfl

theorem cell21_1820593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 5].length) (baseStart_1820593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820593 prefixEnd_1820593 := by exact prefixLift 1820593
  have htrace : WordTrace (prefixWord ++ tailWord_1820593) baseStart_1820593 baseEnd_1820593 := by
    simpa [prefixWord, tailWord_1820593, baseEnd_1820593] using wordTrace_append hprefix tailTrace_1820593
  have hstable : (prefixWord ++ tailWord_1820593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820593).length < 2 ^ (prefixWord ++ tailWord_1820593).sum := by decide
  have hdescent : baseEnd_1820593 < baseStart_1820593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820683 : List Nat := [1, 1, 1, 1, 6, 1, 3, 4, 3]
def baseStart_1820683 : Nat := 118140960795 + 1820683 * 2 ^ 59
def prefixEnd_1820683 : Nat := 4983230072969 + 3 ^ 40 * 1820683 * 2
def baseEnd_1820683 : Nat := 415504665986669023595261

theorem tailTrace_1820683 : CollatzResearch.WordTrace tailWord_1820683 prefixEnd_1820683 415504665986669023595261 := by
  unfold tailWord_1820683
  simp only [CollatzResearch.WordTrace]
  refine ⟨66405764462983913745682703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44270509641989275830455135 66405764462983913745682703)
  ·
    refine ⟨99608646694475870618524055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66405764462983913745682703 99608646694475870618524055)
    ·
      refine ⟨149412970041713805927786083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99608646694475870618524055 149412970041713805927786083)
      ·
        refine ⟨224119455062570708891679125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149412970041713805927786083 224119455062570708891679125)
        ·
          refine ⟨10505599456058001979297459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 224119455062570708891679125 10505599456058001979297459)
          ·
            refine ⟨15758399184087002968946189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10505599456058001979297459 15758399184087002968946189)
            ·
              refine ⟨5909399694032626113354821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15758399184087002968946189 5909399694032626113354821)
              ·
                refine ⟨1108012442631117396254029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5909399694032626113354821 1108012442631117396254029)
                ·
                  refine ⟨415504665986669023595261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108012442631117396254029 415504665986669023595261)
                  ·
                    rfl

theorem cell21_1820683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 3].length) (baseStart_1820683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820683 prefixEnd_1820683 := by exact prefixLift 1820683
  have htrace : WordTrace (prefixWord ++ tailWord_1820683) baseStart_1820683 baseEnd_1820683 := by
    simpa [prefixWord, tailWord_1820683, baseEnd_1820683] using wordTrace_append hprefix tailTrace_1820683
  have hstable : (prefixWord ++ tailWord_1820683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820683).length < 2 ^ (prefixWord ++ tailWord_1820683).sum := by decide
  have hdescent : baseEnd_1820683 < baseStart_1820683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820818 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 7]
def baseStart_1820818 : Nat := 118140960795 + 1820818 * 2 ^ 59
def prefixEnd_1820818 : Nat := 4983230072969 + 3 ^ 40 * 1820818 * 2
def baseEnd_1820818 : Nat := 415535474825938788844985

theorem tailTrace_1820818 : CollatzResearch.WordTrace tailWord_1820818 prefixEnd_1820818 415535474825938788844985 := by
  unfold tailWord_1820818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16602672079373707950461777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44273792211663221201231405 16602672079373707950461777)
  ·
    refine ⟨12452004059530280962846333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16602672079373707950461777 12452004059530280962846333)
    ·
      refine ⟨4669501522323855361067375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12452004059530280962846333 4669501522323855361067375)
      ·
        refine ⟨7004252283485783041601063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4669501522323855361067375 7004252283485783041601063)
        ·
          refine ⟨10506378425228674562401595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7004252283485783041601063 10506378425228674562401595)
          ·
            refine ⟨15759567637843011843602393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10506378425228674562401595 15759567637843011843602393)
            ·
              refine ⟨11819675728382258882701795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15759567637843011843602393 11819675728382258882701795)
              ·
                refine ⟨17729513592573388324052693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11819675728382258882701795 17729513592573388324052693)
                ·
                  refine ⟨415535474825938788844985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17729513592573388324052693 415535474825938788844985)
                  ·
                    rfl

theorem cell21_1820818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_1820818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820818 prefixEnd_1820818 := by exact prefixLift 1820818
  have htrace : WordTrace (prefixWord ++ tailWord_1820818) baseStart_1820818 baseEnd_1820818 := by
    simpa [prefixWord, tailWord_1820818, baseEnd_1820818] using wordTrace_append hprefix tailTrace_1820818
  have hstable : (prefixWord ++ tailWord_1820818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820818).length < 2 ^ (prefixWord ++ tailWord_1820818).sum := by decide
  have hdescent : baseEnd_1820818 < baseStart_1820818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820908 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_1820908 : Nat := 118140960795 + 1820908 * 2 ^ 59
def prefixEnd_1820908 : Nat := 4983230072969 + 3 ^ 40 * 1820908 * 2
def baseEnd_1820908 : Nat := 415556014052118632344801

theorem tailTrace_1820908 : CollatzResearch.WordTrace tailWord_1820908 prefixEnd_1820908 415556014052118632344801 := by
  unfold tailWord_1820908
  simp only [CollatzResearch.WordTrace]
  refine ⟨33206985443584388586311689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44275980591445851448415585 33206985443584388586311689)
  ·
    refine ⟨24905239082688291439733767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33206985443584388586311689 24905239082688291439733767)
    ·
      refine ⟨37357858624032437159600651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24905239082688291439733767 37357858624032437159600651)
      ·
        refine ⟨56036787936048655739400977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37357858624032437159600651 56036787936048655739400977)
        ·
          refine ⟨42027590952036491804550733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56036787936048655739400977 42027590952036491804550733)
          ·
            refine ⟨15760346607013684426706525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42027590952036491804550733 15760346607013684426706525)
            ·
              refine ⟨5910129977630131660014947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15760346607013684426706525 5910129977630131660014947)
              ·
                refine ⟨8865194966445197490022421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5910129977630131660014947 8865194966445197490022421)
                ·
                  refine ⟨415556014052118632344801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8865194966445197490022421 415556014052118632344801)
                  ·
                    rfl

theorem cell21_1820908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_1820908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820908 prefixEnd_1820908 := by exact prefixLift 1820908
  have htrace : WordTrace (prefixWord ++ tailWord_1820908) baseStart_1820908 baseEnd_1820908 := by
    simpa [prefixWord, tailWord_1820908, baseEnd_1820908] using wordTrace_append hprefix tailTrace_1820908
  have hstable : (prefixWord ++ tailWord_1820908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820908).length < 2 ^ (prefixWord ++ tailWord_1820908).sum := by decide
  have hdescent : baseEnd_1820908 < baseStart_1820908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820911 : List Nat := [1, 1, 2, 1, 6, 1, 2, 4, 3]
def baseStart_1820911 : Nat := 118140960795 + 1820911 * 2 ^ 59
def prefixEnd_1820911 : Nat := 4983230072969 + 3 ^ 40 * 1820911 * 2
def baseEnd_1820911 : Nat := 415556698692991293794795

theorem tailTrace_1820911 : CollatzResearch.WordTrace tailWord_1820911 prefixEnd_1820911 415556698692991293794795 := by
  unfold tailWord_1820911
  simp only [CollatzResearch.WordTrace]
  refine ⟨66414080306157908684982587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44276053537438605789988391 66414080306157908684982587)
  ·
    refine ⟨99621120459236863027473881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66414080306157908684982587 99621120459236863027473881)
    ·
      refine ⟨74715840344427647270605411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99621120459236863027473881 74715840344427647270605411)
      ·
        refine ⟨112073760516641470905908117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74715840344427647270605411 112073760516641470905908117)
        ·
          refine ⟨5253457524217568948714443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112073760516641470905908117 5253457524217568948714443)
          ·
            refine ⟨7880186286326353423071665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253457524217568948714443 7880186286326353423071665)
            ·
              refine ⟨5910139714744765067303749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7880186286326353423071665 5910139714744765067303749)
              ·
                refine ⟨1108151196514643450119453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5910139714744765067303749 1108151196514643450119453)
                ·
                  refine ⟨415556698692991293794795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108151196514643450119453 415556698692991293794795)
                  ·
                    rfl

theorem cell21_1820911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 3].length) (baseStart_1820911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820911 prefixEnd_1820911 := by exact prefixLift 1820911
  have htrace : WordTrace (prefixWord ++ tailWord_1820911) baseStart_1820911 baseEnd_1820911 := by
    simpa [prefixWord, tailWord_1820911, baseEnd_1820911] using wordTrace_append hprefix tailTrace_1820911
  have hstable : (prefixWord ++ tailWord_1820911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820911).length < 2 ^ (prefixWord ++ tailWord_1820911).sum := by decide
  have hdescent : baseEnd_1820911 < baseStart_1820911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1820973 : List Nat := [1, 5, 3, 1, 2, 1, 2, 6]
def baseStart_1820973 : Nat := 118140960795 + 1820973 * 2 ^ 59
def prefixEnd_1820973 : Nat := 4983230072969 + 3 ^ 40 * 1820973 * 2
def baseEnd_1820973 : Nat := 138523615979230987920445

theorem tailTrace_1820973 : CollatzResearch.WordTrace tailWord_1820973 prefixEnd_1820973 138523615979230987920445 := by
  unfold tailWord_1820973
  simp only [CollatzResearch.WordTrace]
  refine ⟨66416341631933293273739573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44277561087955528849159715 66416341631933293273739573)
  ·
    refine ⟨6226532027993746244413085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66416341631933293273739573 6226532027993746244413085)
    ·
      refine ⟨2334949510497654841654907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6226532027993746244413085 2334949510497654841654907)
      ·
        refine ⟨3502424265746482262482361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2334949510497654841654907 3502424265746482262482361)
        ·
          refine ⟨2626818199309861696861771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3502424265746482262482361 2626818199309861696861771)
          ·
            refine ⟨3940227298964792545292657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626818199309861696861771 3940227298964792545292657)
            ·
              refine ⟨2955170474223594408969493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3940227298964792545292657 2955170474223594408969493)
              ·
                refine ⟨138523615979230987920445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2955170474223594408969493 138523615979230987920445)
                ·
                  rfl

theorem cell21_1820973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 6].length) (baseStart_1820973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1820973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1820973 prefixEnd_1820973 := by exact prefixLift 1820973
  have htrace : WordTrace (prefixWord ++ tailWord_1820973) baseStart_1820973 baseEnd_1820973 := by
    simpa [prefixWord, tailWord_1820973, baseEnd_1820973] using wordTrace_append hprefix tailTrace_1820973
  have hstable : (prefixWord ++ tailWord_1820973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1820973).length < 2 ^ (prefixWord ++ tailWord_1820973).sum := by decide
  have hdescent : baseEnd_1820973 < baseStart_1820973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1820973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821032 : List Nat := [2, 1, 4, 2, 2, 3, 1, 6]
def baseStart_1821032 : Nat := 118140960795 + 1821032 * 2 ^ 59
def prefixEnd_1821032 : Nat := 4983230072969 + 3 ^ 40 * 1821032 * 2
def baseEnd_1821032 : Nat := 138528104180507324092627

theorem tailTrace_1821032 : CollatzResearch.WordTrace tailWord_1821032 prefixEnd_1821032 138528104180507324092627 := by
  unfold tailWord_1821032
  simp only [CollatzResearch.WordTrace]
  refine ⟨33209246769359773175068675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44278995692479697566758233 33209246769359773175068675)
  ·
    refine ⟨49813870154039659762603013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33209246769359773175068675 49813870154039659762603013)
    ·
      refine ⟨9340100653882436205488065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49813870154039659762603013 9340100653882436205488065)
      ·
        refine ⟨7005075490411827154116049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9340100653882436205488065 7005075490411827154116049)
        ·
          refine ⟨5253806617808870365587037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7005075490411827154116049 5253806617808870365587037)
          ·
            refine ⟨1970177481678326387095139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5253806617808870365587037 1970177481678326387095139)
            ·
              refine ⟨2955266222517489580642709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970177481678326387095139 2955266222517489580642709)
              ·
                refine ⟨138528104180507324092627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2955266222517489580642709 138528104180507324092627)
                ·
                  rfl

theorem cell21_1821032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_1821032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821032 prefixEnd_1821032 := by exact prefixLift 1821032
  have htrace : WordTrace (prefixWord ++ tailWord_1821032) baseStart_1821032 baseEnd_1821032 := by
    simpa [prefixWord, tailWord_1821032, baseEnd_1821032] using wordTrace_append hprefix tailTrace_1821032
  have hstable : (prefixWord ++ tailWord_1821032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821032).length < 2 ^ (prefixWord ++ tailWord_1821032).sum := by decide
  have hdescent : baseEnd_1821032 < baseStart_1821032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821060 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1821060 : Nat := 118140960795 + 1821060 * 2 ^ 59
def prefixEnd_1821060 : Nat := 4983230072969 + 3 ^ 40 * 1821060 * 2
def baseEnd_1821060 : Nat := 415590702523000145811157

theorem tailTrace_1821060 : CollatzResearch.WordTrace tailWord_1821060 prefixEnd_1821060 415590702523000145811157 := by
  unfold tailWord_1821060
  simp only [CollatzResearch.WordTrace]
  refine ⟨33209757391309053566078317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44279676521745404754771089 33209757391309053566078317)
  ·
    refine ⟨12453659021740895087279369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33209757391309053566078317 12453659021740895087279369)
    ·
      refine ⟨9340244266305671315459527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12453659021740895087279369 9340244266305671315459527)
      ·
        refine ⟨14010366399458506973189291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9340244266305671315459527 14010366399458506973189291)
        ·
          refine ⟨21015549599187760459783937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14010366399458506973189291 21015549599187760459783937)
          ·
            refine ⟨15761662199390820344837953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21015549599187760459783937 15761662199390820344837953)
            ·
              refine ⟨11821246649543115258628465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15761662199390820344837953 11821246649543115258628465)
              ·
                refine ⟨8865934987157336443971349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11821246649543115258628465 8865934987157336443971349)
                ·
                  refine ⟨415590702523000145811157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8865934987157336443971349 415590702523000145811157)
                  ·
                    rfl

theorem cell21_1821060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1821060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821060 prefixEnd_1821060 := by exact prefixLift 1821060
  have htrace : WordTrace (prefixWord ++ tailWord_1821060) baseStart_1821060 baseEnd_1821060 := by
    simpa [prefixWord, tailWord_1821060, baseEnd_1821060] using wordTrace_append hprefix tailTrace_1821060
  have hstable : (prefixWord ++ tailWord_1821060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821060).length < 2 ^ (prefixWord ++ tailWord_1821060).sum := by decide
  have hdescent : baseEnd_1821060 < baseStart_1821060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821063 : List Nat := [1, 1, 4, 2, 2, 1, 4, 3, 3]
def baseStart_1821063 : Nat := 118140960795 + 1821063 * 2 ^ 59
def prefixEnd_1821063 : Nat := 4983230072969 + 3 ^ 40 * 1821063 * 2
def baseEnd_1821063 : Nat := 415591387163872807261151

theorem tailTrace_1821063 : CollatzResearch.WordTrace tailWord_1821063 prefixEnd_1821063 415591387163872807261151 := by
  unfold tailWord_1821063
  simp only [CollatzResearch.WordTrace]
  refine ⟨66419624201607238644515843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44279749467738159096343895 66419624201607238644515843)
  ·
    refine ⟨99629436302410857966773765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66419624201607238644515843 99629436302410857966773765)
    ·
      refine ⟨18680519306702035868770081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99629436302410857966773765 18680519306702035868770081)
      ·
        refine ⟨14010389480026526901577561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18680519306702035868770081 14010389480026526901577561)
        ·
          refine ⟨10507792110019895176183171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14010389480026526901577561 10507792110019895176183171)
          ·
            refine ⟨15761688165029842764274757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10507792110019895176183171 15761688165029842764274757)
            ·
              refine ⟨2955316530943095518301517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15761688165029842764274757 2955316530943095518301517)
              ·
                refine ⟨1108243699103660819363069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2955316530943095518301517 1108243699103660819363069)
                ·
                  refine ⟨415591387163872807261151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108243699103660819363069 415591387163872807261151)
                  ·
                    rfl

theorem cell21_1821063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 3].length) (baseStart_1821063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821063 prefixEnd_1821063 := by exact prefixLift 1821063
  have htrace : WordTrace (prefixWord ++ tailWord_1821063) baseStart_1821063 baseEnd_1821063 := by
    simpa [prefixWord, tailWord_1821063, baseEnd_1821063] using wordTrace_append hprefix tailTrace_1821063
  have hstable : (prefixWord ++ tailWord_1821063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821063).length < 2 ^ (prefixWord ++ tailWord_1821063).sum := by decide
  have hdescent : baseEnd_1821063 < baseStart_1821063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821190 : List Nat := [6, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1821190 : Nat := 118140960795 + 1821190 * 2 ^ 59
def prefixEnd_1821190 : Nat := 4983230072969 + 3 ^ 40 * 1821190 * 2
def baseEnd_1821190 : Nat := 415620370294148808644225

theorem tailTrace_1821190 : CollatzResearch.WordTrace tailWord_1821190 prefixEnd_1821190 415620370294148808644225 := by
  unfold tailWord_1821190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075758008504598104199657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44282837514764759556259349 2075758008504598104199657)
  ·
    refine ⟨1556818506378448578149743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2075758008504598104199657 1556818506378448578149743)
    ·
      refine ⟨2335227759567672867224615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1556818506378448578149743 2335227759567672867224615)
      ·
        refine ⟨3502841639351509300836923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2335227759567672867224615 3502841639351509300836923)
        ·
          refine ⟨5254262459027263951255385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502841639351509300836923 5254262459027263951255385)
          ·
            refine ⟨3940696844270447963441539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5254262459027263951255385 3940696844270447963441539)
            ·
              refine ⟨5911045266405671945162309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940696844270447963441539 5911045266405671945162309)
              ·
                refine ⟨1108320987451063489717933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5911045266405671945162309 1108320987451063489717933)
                ·
                  refine ⟨415620370294148808644225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108320987451063489717933 415620370294148808644225)
                  ·
                    rfl

theorem cell21_1821190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1821190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821190 prefixEnd_1821190 := by exact prefixLift 1821190
  have htrace : WordTrace (prefixWord ++ tailWord_1821190) baseStart_1821190 baseEnd_1821190 := by
    simpa [prefixWord, tailWord_1821190, baseEnd_1821190] using wordTrace_append hprefix tailTrace_1821190
  have hstable : (prefixWord ++ tailWord_1821190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821190).length < 2 ^ (prefixWord ++ tailWord_1821190).sum := by decide
  have hdescent : baseEnd_1821190 < baseStart_1821190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821246 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1821246 : Nat := 118140960795 + 1821246 * 2 ^ 59
def prefixEnd_1821246 : Nat := 4983230072969 + 3 ^ 40 * 1821246 * 2
def baseEnd_1821246 : Nat := 415633150257105155710777

theorem tailTrace_1821246 : CollatzResearch.WordTrace tailWord_1821246 prefixEnd_1821246 415633150257105155710777 := by
  unfold tailWord_1821246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8303287344993032612303449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44284199173296173932285061 8303287344993032612303449)
  ·
    refine ⟨6227465508744774459227587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8303287344993032612303449 6227465508744774459227587)
    ·
      refine ⟨9341198263117161688841381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6227465508744774459227587 9341198263117161688841381)
      ·
        refine ⟨1751474674334467816657759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9341198263117161688841381 1751474674334467816657759)
        ·
          refine ⟨2627212011501701724986639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751474674334467816657759 2627212011501701724986639)
          ·
            refine ⟨3940818017252552587479959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627212011501701724986639 3940818017252552587479959)
            ·
              refine ⟨5911227025878828881219939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3940818017252552587479959 5911227025878828881219939)
              ·
                refine ⟨8866840538818243321829909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5911227025878828881219939 8866840538818243321829909)
                ·
                  refine ⟨415633150257105155710777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8866840538818243321829909 415633150257105155710777)
                  ·
                    rfl

theorem cell21_1821246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1821246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821246 prefixEnd_1821246 := by exact prefixLift 1821246
  have htrace : WordTrace (prefixWord ++ tailWord_1821246) baseStart_1821246 baseEnd_1821246 := by
    simpa [prefixWord, tailWord_1821246, baseEnd_1821246] using wordTrace_append hprefix tailTrace_1821246
  have hstable : (prefixWord ++ tailWord_1821246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821246).length < 2 ^ (prefixWord ++ tailWord_1821246).sum := by decide
  have hdescent : baseEnd_1821246 < baseStart_1821246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821314 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1821314 : Nat := 118140960795 + 1821314 * 2 ^ 59
def prefixEnd_1821314 : Nat := 4983230072969 + 3 ^ 40 * 1821314 * 2
def baseEnd_1821314 : Nat := 415648668783552148577305

theorem tailTrace_1821314 : CollatzResearch.WordTrace tailWord_1821314 prefixEnd_1821314 415648668783552148577305 := by
  unfold tailWord_1821314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16607194730924477127975749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44285852615798605674601997 16607194730924477127975749)
  ·
    refine ⟨3113849012048339461495453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16607194730924477127975749 3113849012048339461495453)
    ·
      refine ⟨1167693379518127298060795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3113849012048339461495453 1167693379518127298060795)
      ·
        refine ⟨1751540069277190947091193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167693379518127298060795 1751540069277190947091193)
        ·
          refine ⟨1313655051957893210318395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1751540069277190947091193 1313655051957893210318395)
          ·
            refine ⟨1970482577936839815477593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313655051957893210318395 1970482577936839815477593)
            ·
              refine ⟨1477861933452629861608195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1970482577936839815477593 1477861933452629861608195)
              ·
                refine ⟨2216792900178944792412293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477861933452629861608195 2216792900178944792412293)
                ·
                  refine ⟨415648668783552148577305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2216792900178944792412293 415648668783552148577305)
                  ·
                    rfl

theorem cell21_1821314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1821314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821314 prefixEnd_1821314 := by exact prefixLift 1821314
  have htrace : WordTrace (prefixWord ++ tailWord_1821314) baseStart_1821314 baseEnd_1821314 := by
    simpa [prefixWord, tailWord_1821314, baseEnd_1821314] using wordTrace_append hprefix tailTrace_1821314
  have hstable : (prefixWord ++ tailWord_1821314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821314).length < 2 ^ (prefixWord ++ tailWord_1821314).sum := by decide
  have hdescent : baseEnd_1821314 < baseStart_1821314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821347 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 6]
def baseStart_1821347 : Nat := 118140960795 + 1821347 * 2 ^ 59
def prefixEnd_1821347 : Nat := 4983230072969 + 3 ^ 40 * 1821347 * 2
def baseEnd_1821347 : Nat := 415656199833151424527237

theorem tailTrace_1821347 : CollatzResearch.WordTrace tailWord_1821347 prefixEnd_1821347 415656199833151424527237 := by
  unfold tailWord_1821347
  simp only [CollatzResearch.WordTrace]
  refine ⟨66429982532578355147854295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44286655021718903431902863 66429982532578355147854295)
  ·
    refine ⟨99644973798867532721781443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66429982532578355147854295 99644973798867532721781443)
    ·
      refine ⟨149467460698301299082672165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99644973798867532721781443 149467460698301299082672165)
      ·
        refine ⟨28025148880931493578001031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149467460698301299082672165 28025148880931493578001031)
        ·
          refine ⟨42037723321397240367001547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28025148880931493578001031 42037723321397240367001547)
          ·
            refine ⟨63056584982095860550502321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42037723321397240367001547 63056584982095860550502321)
            ·
              refine ⟨47292438736571895412876741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63056584982095860550502321 47292438736571895412876741)
              ·
                refine ⟨8867332263107230389914389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47292438736571895412876741 8867332263107230389914389)
                ·
                  refine ⟨415656199833151424527237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8867332263107230389914389 415656199833151424527237)
                  ·
                    rfl

theorem cell21_1821347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_1821347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821347 prefixEnd_1821347 := by exact prefixLift 1821347
  have htrace : WordTrace (prefixWord ++ tailWord_1821347) baseStart_1821347 baseEnd_1821347 := by
    simpa [prefixWord, tailWord_1821347, baseEnd_1821347] using wordTrace_append hprefix tailTrace_1821347
  have hstable : (prefixWord ++ tailWord_1821347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821347).length < 2 ^ (prefixWord ++ tailWord_1821347).sum := by decide
  have hdescent : baseEnd_1821347 < baseStart_1821347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821367 : List Nat := [1, 1, 3, 1, 6, 1, 1, 4, 3]
def baseStart_1821367 : Nat := 118140960795 + 1821367 * 2 ^ 59
def prefixEnd_1821367 : Nat := 4983230072969 + 3 ^ 40 * 1821367 * 2
def baseEnd_1821367 : Nat := 415660764105635834193863

theorem tailTrace_1821367 : CollatzResearch.WordTrace tailWord_1821367 prefixEnd_1821367 415660764105635834193863 := by
  unfold tailWord_1821367
  simp only [CollatzResearch.WordTrace]
  refine ⟨66430711992505898563582355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44287141328337265709054903 66430711992505898563582355)
  ·
    refine ⟨99646067988758847845373533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66430711992505898563582355 99646067988758847845373533)
    ·
      refine ⟨37367275495784567942015075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99646067988758847845373533 37367275495784567942015075)
      ·
        refine ⟨56050913243676851913022613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37367275495784567942015075 56050913243676851913022613)
        ·
          refine ⟨2627386558297352433422935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56050913243676851913022613 2627386558297352433422935)
          ·
            refine ⟨3941079837446028650134403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627386558297352433422935 3941079837446028650134403)
            ·
              refine ⟨5911619756169042975201605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941079837446028650134403 5911619756169042975201605)
              ·
                refine ⟨1108428704281695557850301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5911619756169042975201605 1108428704281695557850301)
                ·
                  refine ⟨415660764105635834193863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108428704281695557850301 415660764105635834193863)
                  ·
                    rfl

theorem cell21_1821367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 3].length) (baseStart_1821367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821367 prefixEnd_1821367 := by exact prefixLift 1821367
  have htrace : WordTrace (prefixWord ++ tailWord_1821367) baseStart_1821367 baseEnd_1821367 := by
    simpa [prefixWord, tailWord_1821367, baseEnd_1821367] using wordTrace_append hprefix tailTrace_1821367
  have hstable : (prefixWord ++ tailWord_1821367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821367).length < 2 ^ (prefixWord ++ tailWord_1821367).sum := by decide
  have hdescent : baseEnd_1821367 < baseStart_1821367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821426 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1821426 : Nat := 118140960795 + 1821426 * 2 ^ 59
def prefixEnd_1821426 : Nat := 4983230072969 + 3 ^ 40 * 1821426 * 2
def baseEnd_1821426 : Nat := 415674228709464842710409

theorem tailTrace_1821426 : CollatzResearch.WordTrace tailWord_1821426 prefixEnd_1821426 415674228709464842710409 := by
  unfold tailWord_1821426
  simp only [CollatzResearch.WordTrace]
  refine ⟨16608215974823037909995033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44288575932861434426653421 16608215974823037909995033)
  ·
    refine ⟨12456161981117278432496275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16608215974823037909995033 12456161981117278432496275)
    ·
      refine ⟨18684242971675917648744413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12456161981117278432496275 18684242971675917648744413)
      ·
        refine ⟨7006591114378469118279155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18684242971675917648744413 7006591114378469118279155)
        ·
          refine ⟨10509886671567703677418733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7006591114378469118279155 10509886671567703677418733)
          ·
            refine ⟨3941207501837888879032025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10509886671567703677418733 3941207501837888879032025)
            ·
              refine ⟨2955905626378416659274019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941207501837888879032025 2955905626378416659274019)
              ·
                refine ⟨4433858439567624988911029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2955905626378416659274019 4433858439567624988911029)
                ·
                  refine ⟨415674228709464842710409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4433858439567624988911029 415674228709464842710409)
                  ·
                    rfl

theorem cell21_1821426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1821426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821426 prefixEnd_1821426 := by exact prefixLift 1821426
  have htrace : WordTrace (prefixWord ++ tailWord_1821426) baseStart_1821426 baseEnd_1821426 := by
    simpa [prefixWord, tailWord_1821426, baseEnd_1821426] using wordTrace_append hprefix tailTrace_1821426
  have hstable : (prefixWord ++ tailWord_1821426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821426).length < 2 ^ (prefixWord ++ tailWord_1821426).sum := by decide
  have hdescent : baseEnd_1821426 < baseStart_1821426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821561 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 5]
def baseStart_1821561 : Nat := 118140960795 + 1821561 * 2 ^ 59
def prefixEnd_1821561 : Nat := 4983230072969 + 3 ^ 40 * 1821561 * 2
def baseEnd_1821561 : Nat := 415705037548734607960133

theorem tailTrace_1821561 : CollatzResearch.WordTrace tailWord_1821561 prefixEnd_1821561 415705037548734607960133 := by
  unfold tailWord_1821561
  simp only [CollatzResearch.WordTrace]
  refine ⟨66437787753803069696144537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44291858502535379797429691 66437787753803069696144537)
  ·
    refine ⟨49828340815352302272108403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66437787753803069696144537 49828340815352302272108403)
    ·
      refine ⟨74742511223028453408162605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49828340815352302272108403 74742511223028453408162605)
      ·
        refine ⟨28028441708635670028060977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74742511223028453408162605 28028441708635670028060977)
        ·
          refine ⟨21021331281476752521045733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28028441708635670028060977 21021331281476752521045733)
          ·
            refine ⟨3941499615276891097696075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21021331281476752521045733 3941499615276891097696075)
            ·
              refine ⟨5912249422915336646544113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941499615276891097696075 5912249422915336646544113)
              ·
                refine ⟨4434187067186502484908085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912249422915336646544113 4434187067186502484908085)
                ·
                  refine ⟨415705037548734607960133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4434187067186502484908085 415705037548734607960133)
                  ·
                    rfl

theorem cell21_1821561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_1821561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821561 prefixEnd_1821561 := by exact prefixLift 1821561
  have htrace : WordTrace (prefixWord ++ tailWord_1821561) baseStart_1821561 baseEnd_1821561 := by
    simpa [prefixWord, tailWord_1821561, baseEnd_1821561] using wordTrace_append hprefix tailTrace_1821561
  have hstable : (prefixWord ++ tailWord_1821561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821561).length < 2 ^ (prefixWord ++ tailWord_1821561).sum := by decide
  have hdescent : baseEnd_1821561 < baseStart_1821561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821834 : List Nat := [3, 1, 2, 3, 1, 1, 4, 6]
def baseStart_1821834 : Nat := 118140960795 + 1821834 * 2 ^ 59
def prefixEnd_1821834 : Nat := 4983230072969 + 3 ^ 40 * 1821834 * 2
def baseEnd_1821834 : Nat := 138589113289382266636525

theorem tailTrace_1821834 : CollatzResearch.WordTrace tailWord_1821834 prefixEnd_1821834 138589113289382266636525 := by
  unfold tailWord_1821834
  simp only [CollatzResearch.WordTrace]
  refine ⟨16611936220453509330208139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44298496587876024880555037 16611936220453509330208139)
  ·
    refine ⟨24917904330680263995312209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16611936220453509330208139 24917904330680263995312209)
    ·
      refine ⟨18688428248010197996484157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24917904330680263995312209 18688428248010197996484157)
      ·
        refine ⟨7008160593003824248681559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18688428248010197996484157 7008160593003824248681559)
        ·
          refine ⟨10512240889505736373022339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008160593003824248681559 10512240889505736373022339)
          ·
            refine ⟨15768361334258604559533509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512240889505736373022339 15768361334258604559533509)
            ·
              refine ⟨2956567750173488354912533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15768361334258604559533509 2956567750173488354912533)
              ·
                refine ⟨138589113289382266636525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2956567750173488354912533 138589113289382266636525)
                ·
                  rfl

theorem cell21_1821834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_1821834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821834 prefixEnd_1821834 := by exact prefixLift 1821834
  have htrace : WordTrace (prefixWord ++ tailWord_1821834) baseStart_1821834 baseEnd_1821834 := by
    simpa [prefixWord, tailWord_1821834, baseEnd_1821834] using wordTrace_append hprefix tailTrace_1821834
  have hstable : (prefixWord ++ tailWord_1821834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821834).length < 2 ^ (prefixWord ++ tailWord_1821834).sum := by decide
  have hdescent : baseEnd_1821834 < baseStart_1821834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1821969 : List Nat := [1, 2, 2, 1, 1, 4, 3, 7]
def baseStart_1821969 : Nat := 118140960795 + 1821969 * 2 ^ 59
def prefixEnd_1821969 : Nat := 4983230072969 + 3 ^ 40 * 1821969 * 2
def baseEnd_1821969 : Nat := 138599382902472188386433

theorem tailTrace_1821969 : CollatzResearch.WordTrace tailWord_1821969 prefixEnd_1821969 138599382902472188386433 := by
  unfold tailWord_1821969
  simp only [CollatzResearch.WordTrace]
  refine ⟨66452668736324955376996961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44301779157549970251331307 66452668736324955376996961)
  ·
    refine ⟨49839501552243716532747721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66452668736324955376996961 49839501552243716532747721)
    ·
      refine ⟨37379626164182787399560791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49839501552243716532747721 37379626164182787399560791)
      ·
        refine ⟨56069439246274181099341187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37379626164182787399560791 56069439246274181099341187)
        ·
          refine ⟨84104158869411271649011781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56069439246274181099341187 84104158869411271649011781)
          ·
            refine ⟨15769529788014613434189709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84104158869411271649011781 15769529788014613434189709)
            ·
              refine ⟨5913573670505480037821141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15769529788014613434189709 5913573670505480037821141)
              ·
                refine ⟨138599382902472188386433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5913573670505480037821141 138599382902472188386433)
                ·
                  rfl

theorem cell21_1821969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 7].length) (baseStart_1821969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1821969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1821969 prefixEnd_1821969 := by exact prefixLift 1821969
  have htrace : WordTrace (prefixWord ++ tailWord_1821969) baseStart_1821969 baseEnd_1821969 := by
    simpa [prefixWord, tailWord_1821969, baseEnd_1821969] using wordTrace_append hprefix tailTrace_1821969
  have hstable : (prefixWord ++ tailWord_1821969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1821969).length < 2 ^ (prefixWord ++ tailWord_1821969).sum := by decide
  have hdescent : baseEnd_1821969 < baseStart_1821969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1821969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822006 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1822006 : Nat := 118140960795 + 1822006 * 2 ^ 59
def prefixEnd_1822006 : Nat := 4983230072969 + 3 ^ 40 * 1822006 * 2
def baseEnd_1822006 : Nat := 415806592611512723042557

theorem tailTrace_1822006 : CollatzResearch.WordTrace tailWord_1822006 prefixEnd_1822006 415806592611512723042557 := by
  unfold tailWord_1822006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153376139824431918505867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44302678824793940464062581 4153376139824431918505867)
  ·
    refine ⟨6230064209736647877758801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4153376139824431918505867 6230064209736647877758801)
    ·
      refine ⟨4672548157302485908319101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6230064209736647877758801 4672548157302485908319101)
      ·
        refine ⟨1752205558988432215619663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4672548157302485908319101 1752205558988432215619663)
        ·
          refine ⟨2628308338482648323429495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1752205558988432215619663 2628308338482648323429495)
          ·
            refine ⟨3942462507723972485144243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628308338482648323429495 3942462507723972485144243)
            ·
              refine ⟨5913693761585958727716365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942462507723972485144243 5913693761585958727716365)
              ·
                refine ⟨2217635160594734522893637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5913693761585958727716365 2217635160594734522893637)
                ·
                  refine ⟨415806592611512723042557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217635160594734522893637 415806592611512723042557)
                  ·
                    rfl

theorem cell21_1822006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1822006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822006 prefixEnd_1822006 := by exact prefixLift 1822006
  have htrace : WordTrace (prefixWord ++ tailWord_1822006) baseStart_1822006 baseEnd_1822006 := by
    simpa [prefixWord, tailWord_1822006, baseEnd_1822006] using wordTrace_append hprefix tailTrace_1822006
  have hstable : (prefixWord ++ tailWord_1822006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822006).length < 2 ^ (prefixWord ++ tailWord_1822006).sum := by decide
  have hdescent : baseEnd_1822006 < baseStart_1822006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822048 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_1822048 : Nat := 118140960795 + 1822048 * 2 ^ 59
def prefixEnd_1822048 : Nat := 4983230072969 + 3 ^ 40 * 1822048 * 2
def baseEnd_1822048 : Nat := 415816177583729983342471

theorem tailTrace_1822048 : CollatzResearch.WordTrace tailWord_1822048 prefixEnd_1822048 415816177583729983342471 := by
  unfold tailWord_1822048
  simp only [CollatzResearch.WordTrace]
  refine ⟨33227775051519375934561399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44303700068692501246081865 33227775051519375934561399)
  ·
    refine ⟨49841662577279063901842099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33227775051519375934561399 49841662577279063901842099)
    ·
      refine ⟨74762493865918595852763149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49841662577279063901842099 74762493865918595852763149)
      ·
        refine ⟨28035935199719473444786181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74762493865918595852763149 28035935199719473444786181)
        ·
          refine ⟨5256737849947401270897409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28035935199719473444786181 5256737849947401270897409)
          ·
            refine ⟨3942553387460550953173057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5256737849947401270897409 3942553387460550953173057)
            ·
              refine ⟨2956915040595413214879793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3942553387460550953173057 2956915040595413214879793)
              ·
                refine ⟨2217686280446559911159845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2956915040595413214879793 2217686280446559911159845)
                ·
                  refine ⟨415816177583729983342471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217686280446559911159845 415816177583729983342471)
                  ·
                    rfl

theorem cell21_1822048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_1822048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822048 prefixEnd_1822048 := by exact prefixLift 1822048
  have htrace : WordTrace (prefixWord ++ tailWord_1822048) baseStart_1822048 baseEnd_1822048 := by
    simpa [prefixWord, tailWord_1822048, baseEnd_1822048] using wordTrace_append hprefix tailTrace_1822048
  have hstable : (prefixWord ++ tailWord_1822048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822048).length < 2 ^ (prefixWord ++ tailWord_1822048).sum := by decide
  have hdescent : baseEnd_1822048 < baseStart_1822048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822051 : List Nat := [1, 1, 1, 5, 2, 4, 2, 2, 3]
def baseStart_1822051 : Nat := 118140960795 + 1822051 * 2 ^ 59
def prefixEnd_1822051 : Nat := 4983230072969 + 3 ^ 40 * 1822051 * 2
def baseEnd_1822051 : Nat := 415816862224602644792465

theorem tailTrace_1822051 : CollatzResearch.WordTrace tailWord_1822051 prefixEnd_1822051 415816862224602644792465 := by
  unfold tailWord_1822051
  simp only [CollatzResearch.WordTrace]
  refine ⟨66455659522027883381482007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44303773014685255587654671 66455659522027883381482007)
  ·
    refine ⟨99683489283041825072223011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66455659522027883381482007 99683489283041825072223011)
    ·
      refine ⟨149525233924562737608334517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99683489283041825072223011 149525233924562737608334517)
      ·
        refine ⟨14017990680427756650781361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149525233924562737608334517 14017990680427756650781361)
        ·
          refine ⟨10513493010320817488086021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14017990680427756650781361 10513493010320817488086021)
          ·
            refine ⟨1971279939435153279016129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10513493010320817488086021 1971279939435153279016129)
            ·
              refine ⟨1478459954576364959262097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1971279939435153279016129 1478459954576364959262097)
              ·
                refine ⟨1108844965932273719446573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1478459954576364959262097 1108844965932273719446573)
                ·
                  refine ⟨415816862224602644792465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108844965932273719446573 415816862224602644792465)
                  ·
                    rfl

theorem cell21_1822051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 3].length) (baseStart_1822051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822051 prefixEnd_1822051 := by exact prefixLift 1822051
  have htrace : WordTrace (prefixWord ++ tailWord_1822051) baseStart_1822051 baseEnd_1822051 := by
    simpa [prefixWord, tailWord_1822051, baseEnd_1822051] using wordTrace_append hprefix tailTrace_1822051
  have hstable : (prefixWord ++ tailWord_1822051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822051).length < 2 ^ (prefixWord ++ tailWord_1822051).sum := by decide
  have hdescent : baseEnd_1822051 < baseStart_1822051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822076 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1822076 : Nat := 118140960795 + 1822076 * 2 ^ 59
def prefixEnd_1822076 : Nat := 4983230072969 + 3 ^ 40 * 1822076 * 2
def baseEnd_1822076 : Nat := 415822567565208156875747

theorem tailTrace_1822076 : CollatzResearch.WordTrace tailWord_1822076 prefixEnd_1822076 415822567565208156875747 := by
  unfold tailWord_1822076
  simp only [CollatzResearch.WordTrace]
  refine ⟨33228285673468656325571041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44304380897958208434094721 33228285673468656325571041)
  ·
    refine ⟨24921214255101492244178281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33228285673468656325571041 24921214255101492244178281)
    ·
      refine ⟨18690910691326119183133711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24921214255101492244178281 18690910691326119183133711)
      ·
        refine ⟨28036366036989178774700567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18690910691326119183133711 28036366036989178774700567)
        ·
          refine ⟨42054549055483768162050851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28036366036989178774700567 42054549055483768162050851)
          ·
            refine ⟨63081823583225652243076277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42054549055483768162050851 63081823583225652243076277)
            ·
              refine ⟨5913920960927404897788401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63081823583225652243076277 5913920960927404897788401)
              ·
                refine ⟨4435440720695553673341301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5913920960927404897788401 4435440720695553673341301)
                ·
                  refine ⟨415822567565208156875747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4435440720695553673341301 415822567565208156875747)
                  ·
                    rfl

theorem cell21_1822076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1822076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822076 prefixEnd_1822076 := by exact prefixLift 1822076
  have htrace : WordTrace (prefixWord ++ tailWord_1822076) baseStart_1822076 baseEnd_1822076 := by
    simpa [prefixWord, tailWord_1822076, baseEnd_1822076] using wordTrace_append hprefix tailTrace_1822076
  have hstable : (prefixWord ++ tailWord_1822076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822076).length < 2 ^ (prefixWord ++ tailWord_1822076).sum := by decide
  have hdescent : baseEnd_1822076 < baseStart_1822076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822169 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 5]
def baseStart_1822169 : Nat := 118140960795 + 1822169 * 2 ^ 59
def prefixEnd_1822169 : Nat := 4983230072969 + 3 ^ 40 * 1822169 * 2
def baseEnd_1822169 : Nat := 415843791432260661825557

theorem tailTrace_1822169 : CollatzResearch.WordTrace tailWord_1822169 prefixEnd_1822169 415843791432260661825557 := by
  unfold tailWord_1822169
  simp only [CollatzResearch.WordTrace]
  refine ⟨66459963335600389534277561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44306642223733593022851707 66459963335600389534277561)
  ·
    refine ⟨49844972501700292150708171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66459963335600389534277561 49844972501700292150708171)
    ·
      refine ⟨74767458752550438226062257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49844972501700292150708171 74767458752550438226062257)
      ·
        refine ⟨56075594064412828669546693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74767458752550438226062257 56075594064412828669546693)
        ·
          refine ⟨10514173887077405375540005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56075594064412828669546693 10514173887077405375540005)
          ·
            refine ⟨1971407603827013507913751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10514173887077405375540005 1971407603827013507913751)
            ·
              refine ⟨2957111405740520261870627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971407603827013507913751 2957111405740520261870627)
              ·
                refine ⟨4435667108610780392805941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957111405740520261870627 4435667108610780392805941)
                ·
                  refine ⟨415843791432260661825557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4435667108610780392805941 415843791432260661825557)
                  ·
                    rfl

theorem cell21_1822169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 5].length) (baseStart_1822169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822169 prefixEnd_1822169 := by exact prefixLift 1822169
  have htrace : WordTrace (prefixWord ++ tailWord_1822169) baseStart_1822169 baseEnd_1822169 := by
    simpa [prefixWord, tailWord_1822169, baseEnd_1822169] using wordTrace_append hprefix tailTrace_1822169
  have hstable : (prefixWord ++ tailWord_1822169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822169).length < 2 ^ (prefixWord ++ tailWord_1822169).sum := by decide
  have hdescent : baseEnd_1822169 < baseStart_1822169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822211 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 9]
def baseStart_1822211 : Nat := 118140960795 + 1822211 * 2 ^ 59
def prefixEnd_1822211 : Nat := 4983230072969 + 3 ^ 40 * 1822211 * 2
def baseEnd_1822211 : Nat := 415853376404477922125471

theorem tailTrace_1822211 : CollatzResearch.WordTrace tailWord_1822211 prefixEnd_1822211 415853376404477922125471 := by
  unfold tailWord_1822211
  simp only [CollatzResearch.WordTrace]
  refine ⟨66461495201448230707306487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44307663467632153804870991 66461495201448230707306487)
  ·
    refine ⟨99692242802172346060959731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66461495201448230707306487 99692242802172346060959731)
    ·
      refine ⟨149538364203258519091439597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99692242802172346060959731 149538364203258519091439597)
      ·
        refine ⟨56076886576221944659289849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149538364203258519091439597 56076886576221944659289849)
        ·
          refine ⟨42057664932166458494467387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56076886576221944659289849 42057664932166458494467387)
          ·
            refine ⟨63086497398249687741701081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42057664932166458494467387 63086497398249687741701081)
            ·
              refine ⟨47314873048687265806275811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63086497398249687741701081 47314873048687265806275811)
              ·
                refine ⟨70972309573030898709413717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47314873048687265806275811 70972309573030898709413717)
                ·
                  refine ⟨415853376404477922125471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 70972309573030898709413717 415853376404477922125471)
                  ·
                    rfl

theorem cell21_1822211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_1822211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822211 prefixEnd_1822211 := by exact prefixLift 1822211
  have htrace : WordTrace (prefixWord ++ tailWord_1822211) baseStart_1822211 baseEnd_1822211 := by
    simpa [prefixWord, tailWord_1822211, baseEnd_1822211] using wordTrace_append hprefix tailTrace_1822211
  have hstable : (prefixWord ++ tailWord_1822211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822211).length < 2 ^ (prefixWord ++ tailWord_1822211).sum := by decide
  have hdescent : baseEnd_1822211 < baseStart_1822211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822220 : List Nat := [2, 2, 1, 2, 6, 1, 2, 2, 3]
def baseStart_1822220 : Nat := 118140960795 + 1822220 * 2 ^ 59
def prefixEnd_1822220 : Nat := 4983230072969 + 3 ^ 40 * 1822220 * 2
def baseEnd_1822220 : Nat := 415855430327095906475453

theorem tailTrace_1822220 : CollatzResearch.WordTrace tailWord_1822220 prefixEnd_1822220 415855430327095906475453 := by
  unfold tailWord_1822220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33230911729207812622192057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44307882305610416829589409 33230911729207812622192057)
  ·
    refine ⟨24923183796905859466644043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33230911729207812622192057 24923183796905859466644043)
    ·
      refine ⟨37384775695358789199966065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24923183796905859466644043 37384775695358789199966065)
      ·
        refine ⟨28038581771519091899974549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37384775695358789199966065 28038581771519091899974549)
        ·
          refine ⟨1314308520539957432811307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28038581771519091899974549 1314308520539957432811307)
          ·
            refine ⟨1971462780809936149216961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314308520539957432811307 1971462780809936149216961)
            ·
              refine ⟨1478597085607452111912721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1971462780809936149216961 1478597085607452111912721)
              ·
                refine ⟨1108947814205589083934541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1478597085607452111912721 1108947814205589083934541)
                ·
                  refine ⟨415855430327095906475453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108947814205589083934541 415855430327095906475453)
                  ·
                    rfl

theorem cell21_1822220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_1822220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822220 prefixEnd_1822220 := by exact prefixLift 1822220
  have htrace : WordTrace (prefixWord ++ tailWord_1822220) baseStart_1822220 baseEnd_1822220 := by
    simpa [prefixWord, tailWord_1822220, baseEnd_1822220] using wordTrace_append hprefix tailTrace_1822220
  have hstable : (prefixWord ++ tailWord_1822220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822220).length < 2 ^ (prefixWord ++ tailWord_1822220).sum := by decide
  have hdescent : baseEnd_1822220 < baseStart_1822220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822273 : List Nat := [1, 2, 5, 1, 1, 1, 10]
def baseStart_1822273 : Nat := 118140960795 + 1822273 * 2 ^ 59
def prefixEnd_1822273 : Nat := 4983230072969 + 3 ^ 40 * 1822273 * 2
def baseEnd_1822273 : Nat := 46207502849908843565779

theorem tailTrace_1822273 : CollatzResearch.WordTrace tailWord_1822273 prefixEnd_1822273 46207502849908843565779 := by
  unfold tailWord_1822273
  simp only [CollatzResearch.WordTrace]
  refine ⟨66463756527223615296063473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44309171018149076864042315 66463756527223615296063473)
  ·
    refine ⟨49847817395417711472047605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66463756527223615296063473 49847817395417711472047605)
    ·
      refine ⟨4673232880820410450504463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49847817395417711472047605 4673232880820410450504463)
      ·
        refine ⟨7009849321230615675756695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4673232880820410450504463 7009849321230615675756695)
        ·
          refine ⟨10514773981845923513635043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7009849321230615675756695 10514773981845923513635043)
          ·
            refine ⟨15772160972768885270452565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10514773981845923513635043 15772160972768885270452565)
            ·
              refine ⟨46207502849908843565779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15772160972768885270452565 46207502849908843565779)
              ·
                rfl

theorem cell21_1822273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 10].length) (baseStart_1822273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822273 prefixEnd_1822273 := by exact prefixLift 1822273
  have htrace : WordTrace (prefixWord ++ tailWord_1822273) baseStart_1822273 baseEnd_1822273 := by
    simpa [prefixWord, tailWord_1822273, baseEnd_1822273] using wordTrace_append hprefix tailTrace_1822273
  have hstable : (prefixWord ++ tailWord_1822273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822273).length < 2 ^ (prefixWord ++ tailWord_1822273).sum := by decide
  have hdescent : baseEnd_1822273 < baseStart_1822273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822366 : List Nat := [4, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1822366 : Nat := 118140960795 + 1822366 * 2 ^ 59
def prefixEnd_1822366 : Nat := 4983230072969 + 3 ^ 40 * 1822366 * 2
def baseEnd_1822366 : Nat := 138629583172077365680607

theorem tailTrace_1822366 : CollatzResearch.WordTrace tailWord_1822366 prefixEnd_1822366 138629583172077365680607 := by
  unfold tailWord_1822366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308393564485836522399869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44311432343924461452799301 8308393564485836522399869)
  ·
    refine ⟨3115647586682188695899951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8308393564485836522399869 3115647586682188695899951)
    ·
      refine ⟨4673471380023283043849927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3115647586682188695899951 4673471380023283043849927)
      ·
        refine ⟨7010207070034924565774891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4673471380023283043849927 7010207070034924565774891)
        ·
          refine ⟨10515310605052386848662337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7010207070034924565774891 10515310605052386848662337)
          ·
            refine ⟨7886482953789290136496753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10515310605052386848662337 7886482953789290136496753)
            ·
              refine ⟨5914862215341967602372565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7886482953789290136496753 5914862215341967602372565)
              ·
                refine ⟨138629583172077365680607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5914862215341967602372565 138629583172077365680607)
                ·
                  rfl

theorem cell21_1822366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1822366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822366 prefixEnd_1822366 := by exact prefixLift 1822366
  have htrace : WordTrace (prefixWord ++ tailWord_1822366) baseStart_1822366 baseEnd_1822366 := by
    simpa [prefixWord, tailWord_1822366, baseEnd_1822366] using wordTrace_append hprefix tailTrace_1822366
  have hstable : (prefixWord ++ tailWord_1822366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822366).length < 2 ^ (prefixWord ++ tailWord_1822366).sum := by decide
  have hdescent : baseEnd_1822366 < baseStart_1822366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822397 : List Nat := [1, 4, 1, 2, 1, 2, 3, 4, 3]
def baseStart_1822397 : Nat := 118140960795 + 1822397 * 2 ^ 59
def prefixEnd_1822397 : Nat := 4983230072969 + 3 ^ 40 * 1822397 * 2
def baseEnd_1822397 : Nat := 415895824138582932025091

theorem tailTrace_1822397 : CollatzResearch.WordTrace tailWord_1822397 prefixEnd_1822397 415895824138582932025091 := by
  unfold tailWord_1822397
  simp only [CollatzResearch.WordTrace]
  refine ⟨66468279178774384473577445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44312186119182922982384963 66468279178774384473577445)
  ·
    refine ⟨12462802346020197088795771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66468279178774384473577445 12462802346020197088795771)
    ·
      refine ⟨18694203519030295633193657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12462802346020197088795771 18694203519030295633193657)
      ·
        refine ⟨14020652639272721724895243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18694203519030295633193657 14020652639272721724895243)
        ·
          refine ⟨21030978958909082587342865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14020652639272721724895243 21030978958909082587342865)
          ·
            refine ⟨15773234219181811940507149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21030978958909082587342865 15773234219181811940507149)
            ·
              refine ⟨5914962832193179477690181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15773234219181811940507149 5914962832193179477690181)
              ·
                refine ⟨1109055531036221152066909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5914962832193179477690181 1109055531036221152066909)
                ·
                  refine ⟨415895824138582932025091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109055531036221152066909 415895824138582932025091)
                  ·
                    rfl

theorem cell21_1822397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_1822397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822397 prefixEnd_1822397 := by exact prefixLift 1822397
  have htrace : WordTrace (prefixWord ++ tailWord_1822397) baseStart_1822397 baseEnd_1822397 := by
    simpa [prefixWord, tailWord_1822397, baseEnd_1822397] using wordTrace_append hprefix tailTrace_1822397
  have hstable : (prefixWord ++ tailWord_1822397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822397).length < 2 ^ (prefixWord ++ tailWord_1822397).sum := by decide
  have hdescent : baseEnd_1822397 < baseStart_1822397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822490 : List Nat := [3, 1, 1, 3, 2, 4, 1, 3, 3]
def baseStart_1822490 : Nat := 118140960795 + 1822490 * 2 ^ 59
def prefixEnd_1822490 : Nat := 4983230072969 + 3 ^ 40 * 1822490 * 2
def baseEnd_1822490 : Nat := 415917048005635436974901

theorem tailTrace_1822490 : CollatzResearch.WordTrace tailWord_1822490 prefixEnd_1822490 415917048005635436974901 := by
  unfold tailWord_1822490
  simp only [CollatzResearch.WordTrace]
  refine ⟨16617917791859365339178231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44314447444958307571141949 16617917791859365339178231)
  ·
    refine ⟨24926876687789048008767347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16617917791859365339178231 24926876687789048008767347)
    ·
      refine ⟨37390315031683572013151021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24926876687789048008767347 37390315031683572013151021)
      ·
        refine ⟨14021368136881339504931633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37390315031683572013151021 14021368136881339504931633)
        ·
          refine ⟨10516026102661004628698725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14021368136881339504931633 10516026102661004628698725)
          ·
            refine ⟨1971754894248938367881011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10516026102661004628698725 1971754894248938367881011)
            ·
              refine ⟨2957632341373407551821517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971754894248938367881011 2957632341373407551821517)
              ·
                refine ⟨1109112128015027831933069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2957632341373407551821517 1109112128015027831933069)
                ·
                  refine ⟨415917048005635436974901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109112128015027831933069 415917048005635436974901)
                  ·
                    rfl

theorem cell21_1822490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 3].length) (baseStart_1822490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822490 prefixEnd_1822490 := by exact prefixLift 1822490
  have htrace : WordTrace (prefixWord ++ tailWord_1822490) baseStart_1822490 baseEnd_1822490 := by
    simpa [prefixWord, tailWord_1822490, baseEnd_1822490] using wordTrace_append hprefix tailTrace_1822490
  have hstable : (prefixWord ++ tailWord_1822490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822490).length < 2 ^ (prefixWord ++ tailWord_1822490).sum := by decide
  have hdescent : baseEnd_1822490 < baseStart_1822490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822501 : List Nat := [1, 3, 1, 2, 3, 4, 7]
def baseStart_1822501 : Nat := 118140960795 + 1822501 * 2 ^ 59
def prefixEnd_1822501 : Nat := 4983230072969 + 3 ^ 40 * 1822501 * 2
def baseEnd_1822501 : Nat := 46213284261722429143505

theorem tailTrace_1822501 : CollatzResearch.WordTrace tailWord_1822501 prefixEnd_1822501 46213284261722429143505 := by
  unfold tailWord_1822501
  simp only [CollatzResearch.WordTrace]
  refine ⟨66472072370397610235363357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44314714913598406823575571 66472072370397610235363357)
  ·
    refine ⟨24927027138899103838261259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66472072370397610235363357 24927027138899103838261259)
    ·
      refine ⟨37390540708348655757391889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24927027138899103838261259 37390540708348655757391889)
      ·
        refine ⟨28042905531261491818043917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37390540708348655757391889 28042905531261491818043917)
        ·
          refine ⟨10516089574223059431766469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28042905531261491818043917 10516089574223059431766469)
          ·
            refine ⟨1971766795166823643456213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10516089574223059431766469 1971766795166823643456213)
            ·
              refine ⟨46213284261722429143505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1971766795166823643456213 46213284261722429143505)
              ·
                rfl

theorem cell21_1822501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 7].length) (baseStart_1822501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822501 prefixEnd_1822501 := by exact prefixLift 1822501
  have htrace : WordTrace (prefixWord ++ tailWord_1822501) baseStart_1822501 baseEnd_1822501 := by
    simpa [prefixWord, tailWord_1822501, baseEnd_1822501] using wordTrace_append hprefix tailTrace_1822501
  have hstable : (prefixWord ++ tailWord_1822501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822501).length < 2 ^ (prefixWord ++ tailWord_1822501).sum := by decide
  have hdescent : baseEnd_1822501 < baseStart_1822501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822518 : List Nat := [5, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1822518 : Nat := 118140960795 + 1822518 * 2 ^ 59
def prefixEnd_1822518 : Nat := 4983230072969 + 3 ^ 40 * 1822518 * 2
def baseEnd_1822518 : Nat := 138641145995704536836059

theorem tailTrace_1822518 : CollatzResearch.WordTrace tailWord_1822518 prefixEnd_1822518 138641145995704536836059 := by
  unfold tailWord_1822518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4154543275708501383670763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44315128274224014759154805 4154543275708501383670763)
  ·
    refine ⟨6231814913562752075506145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4154543275708501383670763 6231814913562752075506145)
    ·
      refine ⟨4673861185172064056629609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6231814913562752075506145 4673861185172064056629609)
      ·
        refine ⟨3505395888879048042472207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4673861185172064056629609 3505395888879048042472207)
        ·
          refine ⟨5258093833318572063708311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3505395888879048042472207 5258093833318572063708311)
          ·
            refine ⟨7887140749977858095562467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5258093833318572063708311 7887140749977858095562467)
            ·
              refine ⟨11830711124966787143343701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887140749977858095562467 11830711124966787143343701)
              ·
                refine ⟨138641145995704536836059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11830711124966787143343701 138641145995704536836059)
                ·
                  rfl

theorem cell21_1822518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1822518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822518 prefixEnd_1822518 := by exact prefixLift 1822518
  have htrace : WordTrace (prefixWord ++ tailWord_1822518) baseStart_1822518 baseEnd_1822518 := by
    simpa [prefixWord, tailWord_1822518, baseEnd_1822518] using wordTrace_append hprefix tailTrace_1822518
  have hstable : (prefixWord ++ tailWord_1822518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822518).length < 2 ^ (prefixWord ++ tailWord_1822518).sum := by decide
  have hdescent : baseEnd_1822518 < baseStart_1822518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822560 : List Nat := [2, 1, 1, 3, 3, 11]
def baseStart_1822560 : Nat := 118140960795 + 1822560 * 2 ^ 59
def prefixEnd_1822560 : Nat := 4983230072969 + 3 ^ 40 * 1822560 * 2
def baseEnd_1822560 : Nat := 15404926776271513733633

theorem tailTrace_1822560 : CollatzResearch.WordTrace tailWord_1822560 prefixEnd_1822560 15404926776271513733633 := by
  unfold tailWord_1822560
  simp only [CollatzResearch.WordTrace]
  refine ⟨33237112138591931655880567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44316149518122575541174089 33237112138591931655880567)
  ·
    refine ⟨49855668207887897483820851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33237112138591931655880567 49855668207887897483820851)
    ·
      refine ⟨74783502311831846225731277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49855668207887897483820851 74783502311831846225731277)
      ·
        refine ⟨28043813366936942334649229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74783502311831846225731277 28043813366936942334649229)
        ·
          refine ⟨10516430012601353375493461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28043813366936942334649229 10516430012601353375493461)
          ·
            refine ⟨15404926776271513733633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10516430012601353375493461 15404926776271513733633)
            ·
              rfl

theorem cell21_1822560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 11].length) (baseStart_1822560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822560 prefixEnd_1822560 := by exact prefixLift 1822560
  have htrace : WordTrace (prefixWord ++ tailWord_1822560) baseStart_1822560 baseEnd_1822560 := by
    simpa [prefixWord, tailWord_1822560, baseEnd_1822560] using wordTrace_append hprefix tailTrace_1822560
  have hstable : (prefixWord ++ tailWord_1822560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822560).length < 2 ^ (prefixWord ++ tailWord_1822560).sum := by decide
  have hdescent : baseEnd_1822560 < baseStart_1822560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822608 : List Nat := [2, 1, 1, 1, 1, 1, 2, 9, 3]
def baseStart_1822608 : Nat := 118140960795 + 1822608 * 2 ^ 59
def prefixEnd_1822608 : Nat := 4983230072969 + 3 ^ 40 * 1822608 * 2
def baseEnd_1822608 : Nat := 415943977213293454007993

theorem tailTrace_1822608 : CollatzResearch.WordTrace tailWord_1822608 prefixEnd_1822608 415943977213293454007993 := by
  unfold tailWord_1822608
  simp only [CollatzResearch.WordTrace]
  refine ⟨33237987490504983754754239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44317316654006645006338985 33237987490504983754754239)
  ·
    refine ⟨49856981235757475632131359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33237987490504983754754239 49856981235757475632131359)
    ·
      refine ⟨74785471853636213448197039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49856981235757475632131359 74785471853636213448197039)
      ·
        refine ⟨112178207780454320172295559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74785471853636213448197039 112178207780454320172295559)
        ·
          refine ⟨168267311670681480258443339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112178207780454320172295559 168267311670681480258443339)
          ·
            refine ⟨252400967506022220387665009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168267311670681480258443339 252400967506022220387665009)
            ·
              refine ⟨189300725629516665290748757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252400967506022220387665009 189300725629516665290748757)
              ·
                refine ⟨1109183939235449210687981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 189300725629516665290748757 1109183939235449210687981)
                ·
                  refine ⟨415943977213293454007993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109183939235449210687981 415943977213293454007993)
                  ·
                    rfl

theorem cell21_1822608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 3].length) (baseStart_1822608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822608 prefixEnd_1822608 := by exact prefixLift 1822608
  have htrace : WordTrace (prefixWord ++ tailWord_1822608) baseStart_1822608 baseEnd_1822608 := by
    simpa [prefixWord, tailWord_1822608, baseEnd_1822608] using wordTrace_append hprefix tailTrace_1822608
  have hstable : (prefixWord ++ tailWord_1822608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822608).length < 2 ^ (prefixWord ++ tailWord_1822608).sum := by decide
  have hdescent : baseEnd_1822608 < baseStart_1822608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822625 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 5]
def baseStart_1822625 : Nat := 118140960795 + 1822625 * 2 ^ 59
def prefixEnd_1822625 : Nat := 4983230072969 + 3 ^ 40 * 1822625 * 2
def baseEnd_1822625 : Nat := 415947856844905202224625

theorem tailTrace_1822625 : CollatzResearch.WordTrace tailWord_1822625 prefixEnd_1822625 415947856844905202224625 := by
  unfold tailWord_1822625
  simp only [CollatzResearch.WordTrace]
  refine ⟨66476595021948379412877329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44317730014632252941918219 66476595021948379412877329)
  ·
    refine ⟨49857446266461284559657997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66476595021948379412877329 49857446266461284559657997)
    ·
      refine ⟨18696542349922981709871749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49857446266461284559657997 18696542349922981709871749)
      ·
        refine ⟨3505601690610559070600953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18696542349922981709871749 3505601690610559070600953)
        ·
          refine ⟨2629201267957919302950715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3505601690610559070600953 2629201267957919302950715)
          ·
            refine ⟨3943801901936878954426073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629201267957919302950715 3943801901936878954426073)
            ·
              refine ⟨2957851426452659215819555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3943801901936878954426073 2957851426452659215819555)
              ·
                refine ⟨4436777139678988823729333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957851426452659215819555 4436777139678988823729333)
                ·
                  refine ⟨415947856844905202224625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4436777139678988823729333 415947856844905202224625)
                  ·
                    rfl

theorem cell21_1822625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_1822625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822625 prefixEnd_1822625 := by exact prefixLift 1822625
  have htrace : WordTrace (prefixWord ++ tailWord_1822625) baseStart_1822625 baseEnd_1822625 := by
    simpa [prefixWord, tailWord_1822625, baseEnd_1822625] using wordTrace_append hprefix tailTrace_1822625
  have hstable : (prefixWord ++ tailWord_1822625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822625).length < 2 ^ (prefixWord ++ tailWord_1822625).sum := by decide
  have hdescent : baseEnd_1822625 < baseStart_1822625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822639 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 4]
def baseStart_1822639 : Nat := 118140960795 + 1822639 * 2 ^ 59
def prefixEnd_1822639 : Nat := 4983230072969 + 3 ^ 40 * 1822639 * 2
def baseEnd_1822639 : Nat := 415951051835644288991263

theorem tailTrace_1822639 : CollatzResearch.WordTrace tailWord_1822639 prefixEnd_1822639 415951051835644288991263 := by
  unfold tailWord_1822639
  simp only [CollatzResearch.WordTrace]
  refine ⟨66477105643897659803886971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44318070429265106535924647 66477105643897659803886971)
  ·
    refine ⟨99715658465846489705830457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66477105643897659803886971 99715658465846489705830457)
    ·
      refine ⟨74786743849384867279372843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99715658465846489705830457 74786743849384867279372843)
      ·
        refine ⟨112180115774077300919059265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74786743849384867279372843 112180115774077300919059265)
        ·
          refine ⟨84135086830557975689294449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112180115774077300919059265 84135086830557975689294449)
          ·
            refine ⟨63101315122918481766970837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84135086830557975689294449 63101315122918481766970837)
            ·
              refine ⟨1478937073193401916413379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 63101315122918481766970837 1478937073193401916413379)
              ·
                refine ⟨2218405609790102874620069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478937073193401916413379 2218405609790102874620069)
                ·
                  refine ⟨415951051835644288991263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2218405609790102874620069 415951051835644288991263)
                  ·
                    rfl

theorem cell21_1822639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 4].length) (baseStart_1822639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822639 prefixEnd_1822639 := by exact prefixLift 1822639
  have htrace : WordTrace (prefixWord ++ tailWord_1822639) baseStart_1822639 baseEnd_1822639 := by
    simpa [prefixWord, tailWord_1822639, baseEnd_1822639] using wordTrace_append hprefix tailTrace_1822639
  have hstable : (prefixWord ++ tailWord_1822639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822639).length < 2 ^ (prefixWord ++ tailWord_1822639).sum := by decide
  have hdescent : baseEnd_1822639 < baseStart_1822639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822653 : List Nat := [1, 4, 1, 2, 3, 2, 1, 7]
def baseStart_1822653 : Nat := 118140960795 + 1822653 * 2 ^ 59
def prefixEnd_1822653 : Nat := 4983230072969 + 3 ^ 40 * 1822653 * 2
def baseEnd_1822653 : Nat := 138651415608794458585967

theorem tailTrace_1822653 : CollatzResearch.WordTrace tailWord_1822653 prefixEnd_1822653 138651415608794458585967 := by
  unfold tailWord_1822653
  simp only [CollatzResearch.WordTrace]
  refine ⟨66477616265846940194896613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44318410843897960129931075 66477616265846940194896613)
  ·
    refine ⟨12464553049846301286543115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66477616265846940194896613 12464553049846301286543115)
    ·
      refine ⟨18696829574769451929814673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12464553049846301286543115 18696829574769451929814673)
      ·
        refine ⟨14022622181077088947361005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18696829574769451929814673 14022622181077088947361005)
        ·
          refine ⟨5258483317903908355260377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14022622181077088947361005 5258483317903908355260377)
          ·
            refine ⟨3943862488427931266445283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5258483317903908355260377 3943862488427931266445283)
            ·
              refine ⟨5915793732641896899667925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943862488427931266445283 5915793732641896899667925)
              ·
                refine ⟨138651415608794458585967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5915793732641896899667925 138651415608794458585967)
                ·
                  rfl

theorem cell21_1822653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 7].length) (baseStart_1822653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822653 prefixEnd_1822653 := by exact prefixLift 1822653
  have htrace : WordTrace (prefixWord ++ tailWord_1822653) baseStart_1822653 baseEnd_1822653 := by
    simpa [prefixWord, tailWord_1822653, baseEnd_1822653] using wordTrace_append hprefix tailTrace_1822653
  have hstable : (prefixWord ++ tailWord_1822653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822653).length < 2 ^ (prefixWord ++ tailWord_1822653).sum := by decide
  have hdescent : baseEnd_1822653 < baseStart_1822653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822690 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1822690 : Nat := 118140960795 + 1822690 * 2 ^ 59
def prefixEnd_1822690 : Nat := 4983230072969 + 3 ^ 40 * 1822690 * 2
def baseEnd_1822690 : Nat := 415962690730479533641159

theorem tailTrace_1822690 : CollatzResearch.WordTrace tailWord_1822690 prefixEnd_1822690 415962690730479533641159 := by
  unfold tailWord_1822690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16619741441678223878498381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44319310511141930342662349 16619741441678223878498381)
  ·
    refine ⟨6232403040629333954436893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16619741441678223878498381 6232403040629333954436893)
    ·
      refine ⟨2337151140236000232913835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6232403040629333954436893 2337151140236000232913835)
      ·
        refine ⟨3505726710354000349370753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337151140236000232913835 3505726710354000349370753)
        ·
          refine ⟨2629295032765500262028065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3505726710354000349370753 2629295032765500262028065)
          ·
            refine ⟨1971971274574125196521049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2629295032765500262028065 1971971274574125196521049)
            ·
              refine ⟨1478978455930593897390787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1971971274574125196521049 1478978455930593897390787)
              ·
                refine ⟨2218467683895890846086181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478978455930593897390787 2218467683895890846086181)
                ·
                  refine ⟨415962690730479533641159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2218467683895890846086181 415962690730479533641159)
                  ·
                    rfl

theorem cell21_1822690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1822690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822690 prefixEnd_1822690 := by exact prefixLift 1822690
  have htrace : WordTrace (prefixWord ++ tailWord_1822690) baseStart_1822690 baseEnd_1822690 := by
    simpa [prefixWord, tailWord_1822690, baseEnd_1822690] using wordTrace_append hprefix tailTrace_1822690
  have hstable : (prefixWord ++ tailWord_1822690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822690).length < 2 ^ (prefixWord ++ tailWord_1822690).sum := by decide
  have hdescent : baseEnd_1822690 < baseStart_1822690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822712 : List Nat := [2, 1, 2, 1, 1, 3, 4, 7]
def baseStart_1822712 : Nat := 118140960795 + 1822712 * 2 ^ 59
def prefixEnd_1822712 : Nat := 4983230072969 + 3 ^ 40 * 1822712 * 2
def baseEnd_1822712 : Nat := 138655903810070794758149

theorem tailTrace_1822712 : CollatzResearch.WordTrace tailWord_1822712 prefixEnd_1822712 138655903810070794758149 := by
  unfold tailWord_1822712
  simp only [CollatzResearch.WordTrace]
  refine ⟨33239884086316596635647195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44319845448422128847529593 33239884086316596635647195)
  ·
    refine ⟨49859826129474894953470793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33239884086316596635647195 49859826129474894953470793)
    ·
      refine ⟨37394869597106171215103095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49859826129474894953470793 37394869597106171215103095)
      ·
        refine ⟨56092304395659256822654643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37394869597106171215103095 56092304395659256822654643)
        ·
          refine ⟨84138456593488885233981965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56092304395659256822654643 84138456593488885233981965)
          ·
            refine ⟨31551921222558331962743237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84138456593488885233981965 31551921222558331962743237)
            ·
              refine ⟨5915985229229687243014357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31551921222558331962743237 5915985229229687243014357)
              ·
                refine ⟨138655903810070794758149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5915985229229687243014357 138655903810070794758149)
                ·
                  rfl

theorem cell21_1822712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_1822712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822712 prefixEnd_1822712 := by exact prefixLift 1822712
  have htrace : WordTrace (prefixWord ++ tailWord_1822712) baseStart_1822712 baseEnd_1822712 := by
    simpa [prefixWord, tailWord_1822712, baseEnd_1822712] using wordTrace_append hprefix tailTrace_1822712
  have hstable : (prefixWord ++ tailWord_1822712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822712).length < 2 ^ (prefixWord ++ tailWord_1822712).sum := by decide
  have hdescent : baseEnd_1822712 < baseStart_1822712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822819 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 5]
def baseStart_1822819 : Nat := 118140960795 + 1822819 * 2 ^ 59
def prefixEnd_1822819 : Nat := 4983230072969 + 3 ^ 40 * 1822819 * 2
def baseEnd_1822819 : Nat := 415992130288003975990895

theorem tailTrace_1822819 : CollatzResearch.WordTrace tailWord_1822819 prefixEnd_1822819 415992130288003975990895 := by
  unfold tailWord_1822819
  simp only [CollatzResearch.WordTrace]
  refine ⟨66483670783245550545439511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44322447188830367030293007 66483670783245550545439511)
  ·
    refine ⟨99725506174868325818159267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66483670783245550545439511 99725506174868325818159267)
    ·
      refine ⟨149588259262302488727238901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99725506174868325818159267 149588259262302488727238901)
      ·
        refine ⟨14023899305840858318178647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149588259262302488727238901 14023899305840858318178647)
        ·
          refine ⟨21035848958761287477267971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14023899305840858318178647 21035848958761287477267971)
          ·
            refine ⟨31553773438141931215901957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21035848958761287477267971 31553773438141931215901957)
            ·
              refine ⟨5916332519651612102981617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31553773438141931215901957 5916332519651612102981617)
              ·
                refine ⟨4437249389738709077236213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916332519651612102981617 4437249389738709077236213)
                ·
                  refine ⟨415992130288003975990895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4437249389738709077236213 415992130288003975990895)
                  ·
                    rfl

theorem cell21_1822819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_1822819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822819 prefixEnd_1822819 := by exact prefixLift 1822819
  have htrace : WordTrace (prefixWord ++ tailWord_1822819) baseStart_1822819 baseEnd_1822819 := by
    simpa [prefixWord, tailWord_1822819, baseEnd_1822819] using wordTrace_append hprefix tailTrace_1822819
  have hstable : (prefixWord ++ tailWord_1822819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822819).length < 2 ^ (prefixWord ++ tailWord_1822819).sum := by decide
  have hdescent : baseEnd_1822819 < baseStart_1822819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822833 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 8]
def baseStart_1822833 : Nat := 118140960795 + 1822833 * 2 ^ 59
def prefixEnd_1822833 : Nat := 4983230072969 + 3 ^ 40 * 1822833 * 2
def baseEnd_1822833 : Nat := 415995325278743062757533

theorem tailTrace_1822833 : CollatzResearch.WordTrace tailWord_1822833 prefixEnd_1822833 415995325278743062757533 := by
  unfold tailWord_1822833
  simp only [CollatzResearch.WordTrace]
  refine ⟨66484181405194830936449153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44322787603463220624299435 66484181405194830936449153)
  ·
    refine ⟨49863136053896123202336865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66484181405194830936449153 49863136053896123202336865)
    ·
      refine ⟨37397352040422092401752649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49863136053896123202336865 37397352040422092401752649)
      ·
        refine ⟨28048014030316569301314487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37397352040422092401752649 28048014030316569301314487)
        ·
          refine ⟨42072021045474853951971731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28048014030316569301314487 42072021045474853951971731)
          ·
            refine ⟨63108031568212280927957597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42072021045474853951971731 63108031568212280927957597)
            ·
              refine ⟨23665511838079605347984099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63108031568212280927957597 23665511838079605347984099)
              ·
                refine ⟨35498267757119408021976149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23665511838079605347984099 35498267757119408021976149)
                ·
                  refine ⟨415995325278743062757533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35498267757119408021976149 415995325278743062757533)
                  ·
                    rfl

theorem cell21_1822833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_1822833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822833 prefixEnd_1822833 := by exact prefixLift 1822833
  have htrace : WordTrace (prefixWord ++ tailWord_1822833) baseStart_1822833 baseEnd_1822833 := by
    simpa [prefixWord, tailWord_1822833, baseEnd_1822833] using wordTrace_append hprefix tailTrace_1822833
  have hstable : (prefixWord ++ tailWord_1822833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822833).length < 2 ^ (prefixWord ++ tailWord_1822833).sum := by decide
  have hdescent : baseEnd_1822833 < baseStart_1822833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822864 : List Nat := [2, 1, 1, 1, 1, 1, 8, 6]
def baseStart_1822864 : Nat := 118140960795 + 1822864 * 2 ^ 59
def prefixEnd_1822864 : Nat := 4983230072969 + 3 ^ 40 * 1822864 * 2
def baseEnd_1822864 : Nat := 138667466633697965913601

theorem tailTrace_1822864 : CollatzResearch.WordTrace tailWord_1822864 prefixEnd_1822864 138667466633697965913601 := by
  unfold tailWord_1822864
  simp only [CollatzResearch.WordTrace]
  refine ⟨33242656034041261615413823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44323541378721682153885097 33242656034041261615413823)
  ·
    refine ⟨49863984051061892423120735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33242656034041261615413823 49863984051061892423120735)
    ·
      refine ⟨74795976076592838634681103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49863984051061892423120735 74795976076592838634681103)
      ·
        refine ⟨112193964114889257952021655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74795976076592838634681103 112193964114889257952021655)
        ·
          refine ⟨168290946172333886928032483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112193964114889257952021655 168290946172333886928032483)
          ·
            refine ⟨252436419258500830392048725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168290946172333886928032483 252436419258500830392048725)
            ·
              refine ⟨2958239288185556606156821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 252436419258500830392048725 2958239288185556606156821)
              ·
                refine ⟨138667466633697965913601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2958239288185556606156821 138667466633697965913601)
                ·
                  rfl

theorem cell21_1822864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_1822864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822864 prefixEnd_1822864 := by exact prefixLift 1822864
  have htrace : WordTrace (prefixWord ++ tailWord_1822864) baseStart_1822864 baseEnd_1822864 := by
    simpa [prefixWord, tailWord_1822864, baseEnd_1822864] using wordTrace_append hprefix tailTrace_1822864
  have hstable : (prefixWord ++ tailWord_1822864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822864).length < 2 ^ (prefixWord ++ tailWord_1822864).sum := by decide
  have hdescent : baseEnd_1822864 < baseStart_1822864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1822957 : List Nat := [1, 5, 1, 2, 3, 1, 8]
def baseStart_1822957 : Nat := 118140960795 + 1822957 * 2 ^ 59
def prefixEnd_1822957 : Nat := 4983230072969 + 3 ^ 40 * 1822957 * 2
def baseEnd_1822957 : Nat := 46224847085349600298957

theorem tailTrace_1822957 : CollatzResearch.WordTrace tailWord_1822957 prefixEnd_1822957 46224847085349600298957 := by
  unfold tailWord_1822957
  simp only [CollatzResearch.WordTrace]
  refine ⟨66488704056745600113963125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44325802704497066742642083 66488704056745600113963125)
  ·
    refine ⟨6233316005319900010684043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66488704056745600113963125 6233316005319900010684043)
    ·
      refine ⟨9349974007979850016026065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6233316005319900010684043 9349974007979850016026065)
      ·
        refine ⟨7012480505984887512019549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9349974007979850016026065 7012480505984887512019549)
        ·
          refine ⟨2629680189744332817007331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7012480505984887512019549 2629680189744332817007331)
          ·
            refine ⟨3944520284616499225510997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629680189744332817007331 3944520284616499225510997)
            ·
              refine ⟨46224847085349600298957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3944520284616499225510997 46224847085349600298957)
              ·
                rfl

theorem cell21_1822957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 8].length) (baseStart_1822957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1822957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1822957 prefixEnd_1822957 := by exact prefixLift 1822957
  have htrace : WordTrace (prefixWord ++ tailWord_1822957) baseStart_1822957 baseEnd_1822957 := by
    simpa [prefixWord, tailWord_1822957, baseEnd_1822957] using wordTrace_append hprefix tailTrace_1822957
  have hstable : (prefixWord ++ tailWord_1822957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1822957).length < 2 ^ (prefixWord ++ tailWord_1822957).sum := by decide
  have hdescent : baseEnd_1822957 < baseStart_1822957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1822957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823022 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1823022 : Nat := 118140960795 + 1823022 * 2 ^ 59
def prefixEnd_1823022 : Nat := 4983230072969 + 3 ^ 40 * 1823022 * 2
def baseEnd_1823022 : Nat := 416038457653720734107147

theorem tailTrace_1823022 : CollatzResearch.WordTrace tailWord_1823022 prefixEnd_1823022 416038457653720734107147 := by
  unfold tailWord_1823022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8311384350188764526884915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44327383201006744143386213 8311384350188764526884915)
  ·
    refine ⟨12467076525283146790327373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8311384350188764526884915 12467076525283146790327373)
    ·
      refine ⟨4675153696981180046372765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12467076525283146790327373 4675153696981180046372765)
      ·
        refine ⟨1753182636367942517389787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4675153696981180046372765 1753182636367942517389787)
        ·
          refine ⟨2629773954551913776084681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753182636367942517389787 2629773954551913776084681)
          ·
            refine ⟨1972330465913935332063511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2629773954551913776084681 1972330465913935332063511)
            ·
              refine ⟨2958495698870902998095267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972330465913935332063511 2958495698870902998095267)
              ·
                refine ⟨4437743548306354497142901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958495698870902998095267 4437743548306354497142901)
                ·
                  refine ⟨416038457653720734107147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4437743548306354497142901 416038457653720734107147)
                  ·
                    rfl

theorem cell21_1823022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1823022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823022 prefixEnd_1823022 := by exact prefixLift 1823022
  have htrace : WordTrace (prefixWord ++ tailWord_1823022) baseStart_1823022 baseEnd_1823022 := by
    simpa [prefixWord, tailWord_1823022, baseEnd_1823022] using wordTrace_append hprefix tailTrace_1823022
  have hstable : (prefixWord ++ tailWord_1823022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823022).length < 2 ^ (prefixWord ++ tailWord_1823022).sum := by decide
  have hdescent : baseEnd_1823022 < baseStart_1823022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823033 : List Nat := [1, 2, 1, 6, 1, 2, 2, 6]
def baseStart_1823033 : Nat := 118140960795 + 1823033 * 2 ^ 59
def prefixEnd_1823033 : Nat := 4983230072969 + 3 ^ 40 * 1823033 * 2
def baseEnd_1823033 : Nat := 138680322667862386474597

theorem tailTrace_1823033 : CollatzResearch.WordTrace tailWord_1823033 prefixEnd_1823033 138680322667862386474597 := by
  unfold tailWord_1823033
  simp only [CollatzResearch.WordTrace]
  refine ⟨66491476004470265093729753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44327650669646843395819835 66491476004470265093729753)
  ·
    refine ⟨49868607003352698820297315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66491476004470265093729753 49868607003352698820297315)
    ·
      refine ⟨74802910505029048230445973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49868607003352698820297315 74802910505029048230445973)
      ·
        refine ⟨3506386429923236635802155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74802910505029048230445973 3506386429923236635802155)
        ·
          refine ⟨5259579644884854953703233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3506386429923236635802155 5259579644884854953703233)
          ·
            refine ⟨3944684733663641215277425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5259579644884854953703233 3944684733663641215277425)
            ·
              refine ⟨2958513550247730911458069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3944684733663641215277425 2958513550247730911458069)
              ·
                refine ⟨138680322667862386474597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2958513550247730911458069 138680322667862386474597)
                ·
                  rfl

theorem cell21_1823033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 6].length) (baseStart_1823033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823033 prefixEnd_1823033 := by exact prefixLift 1823033
  have htrace : WordTrace (prefixWord ++ tailWord_1823033) baseStart_1823033 baseEnd_1823033 := by
    simpa [prefixWord, tailWord_1823033, baseEnd_1823033] using wordTrace_append hprefix tailTrace_1823033
  have hstable : (prefixWord ++ tailWord_1823033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823033).length < 2 ^ (prefixWord ++ tailWord_1823033).sum := by decide
  have hdescent : baseEnd_1823033 < baseStart_1823033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823140 : List Nat := [2, 3, 1, 2, 1, 1, 4, 4, 3]
def baseStart_1823140 : Nat := 118140960795 + 1823140 * 2 ^ 59
def prefixEnd_1823140 : Nat := 4983230072969 + 3 ^ 40 * 1823140 * 2
def baseEnd_1823140 : Nat := 416065386861378751140239

theorem tailTrace_1823140 : CollatzResearch.WordTrace tailWord_1823140 prefixEnd_1823140 416065386861378751140239 := by
  unfold tailWord_1823140
  simp only [CollatzResearch.WordTrace]
  refine ⟨33247689307541311183937437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44330252410055081578583249 33247689307541311183937437)
  ·
    refine ⟨12467883490327991693976539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33247689307541311183937437 12467883490327991693976539)
    ·
      refine ⟨18701825235491987540964809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12467883490327991693976539 18701825235491987540964809)
      ·
        refine ⟨14026368926618990655723607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18701825235491987540964809 14026368926618990655723607)
        ·
          refine ⟨21039553389928485983585411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14026368926618990655723607 21039553389928485983585411)
          ·
            refine ⟨31559330084892728975378117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21039553389928485983585411 31559330084892728975378117)
            ·
              refine ⟨5917374390917386682883397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31559330084892728975378117 5917374390917386682883397)
              ·
                refine ⟨1109507698297010003040637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5917374390917386682883397 1109507698297010003040637)
                ·
                  refine ⟨416065386861378751140239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109507698297010003040637 416065386861378751140239)
                  ·
                    rfl

theorem cell21_1823140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_1823140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823140 prefixEnd_1823140 := by exact prefixLift 1823140
  have htrace : WordTrace (prefixWord ++ tailWord_1823140) baseStart_1823140 baseEnd_1823140 := by
    simpa [prefixWord, tailWord_1823140, baseEnd_1823140] using wordTrace_append hprefix tailTrace_1823140
  have hstable : (prefixWord ++ tailWord_1823140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823140).length < 2 ^ (prefixWord ++ tailWord_1823140).sum := by decide
  have hdescent : baseEnd_1823140 < baseStart_1823140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823146 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_1823146 : Nat := 118140960795 + 1823146 * 2 ^ 59
def prefixEnd_1823146 : Nat := 4983230072969 + 3 ^ 40 * 1823146 * 2
def baseEnd_1823146 : Nat := 416066756143124074040227

theorem tailTrace_1823146 : CollatzResearch.WordTrace tailWord_1823146 prefixEnd_1823146 416066756143124074040227 := by
  unfold tailWord_1823146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16623899363265221348148323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44330398302040590261728861 16623899363265221348148323)
  ·
    refine ⟨24935849044897832022222485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16623899363265221348148323 24935849044897832022222485)
    ·
      refine ⟨1168867923979585876041679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24935849044897832022222485 1168867923979585876041679)
      ·
        refine ⟨1753301885969378814062519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168867923979585876041679 1753301885969378814062519)
        ·
          refine ⟨2629952828954068221093779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753301885969378814062519 2629952828954068221093779)
          ·
            refine ⟨3944929243431102331640669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629952828954068221093779 3944929243431102331640669)
            ·
              refine ⟨1479348466286663374365251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3944929243431102331640669 1479348466286663374365251)
              ·
                refine ⟨2219022699429995061547877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479348466286663374365251 2219022699429995061547877)
                ·
                  refine ⟨416066756143124074040227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219022699429995061547877 416066756143124074040227)
                  ·
                    rfl

theorem cell21_1823146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_1823146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823146 prefixEnd_1823146 := by exact prefixLift 1823146
  have htrace : WordTrace (prefixWord ++ tailWord_1823146) baseStart_1823146 baseEnd_1823146 := by
    simpa [prefixWord, tailWord_1823146, baseEnd_1823146] using wordTrace_append hprefix tailTrace_1823146
  have hstable : (prefixWord ++ tailWord_1823146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823146).length < 2 ^ (prefixWord ++ tailWord_1823146).sum := by decide
  have hdescent : baseEnd_1823146 < baseStart_1823146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823199 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 5]
def baseStart_1823199 : Nat := 118140960795 + 1823199 * 2 ^ 59
def prefixEnd_1823199 : Nat := 4983230072969 + 3 ^ 40 * 1823199 * 2
def baseEnd_1823199 : Nat := 416078851465207759656785

theorem tailTrace_1823199 : CollatzResearch.WordTrace tailWord_1823199 prefixEnd_1823199 416078851465207759656785 := by
  unfold tailWord_1823199
  simp only [CollatzResearch.WordTrace]
  refine ⟨66497530521868875444272651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44331687014579250296181767 66497530521868875444272651)
  ·
    refine ⟨99746295782803313166408977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66497530521868875444272651 99746295782803313166408977)
    ·
      refine ⟨74809721837102484874806733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99746295782803313166408977 74809721837102484874806733)
      ·
        refine ⟨28053645688913431828052525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74809721837102484874806733 28053645688913431828052525)
        ·
          refine ⟨10520117133342536935519697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28053645688913431828052525 10520117133342536935519697)
          ·
            refine ⟨7890087850006902701639773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10520117133342536935519697 7890087850006902701639773)
            ·
              refine ⟨2958782943752588513114915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7890087850006902701639773 2958782943752588513114915)
              ·
                refine ⟨4438174415628882769672373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958782943752588513114915 4438174415628882769672373)
                ·
                  refine ⟨416078851465207759656785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4438174415628882769672373 416078851465207759656785)
                  ·
                    rfl

theorem cell21_1823199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 5].length) (baseStart_1823199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823199 prefixEnd_1823199 := by exact prefixLift 1823199
  have htrace : WordTrace (prefixWord ++ tailWord_1823199) baseStart_1823199 baseEnd_1823199 := by
    simpa [prefixWord, tailWord_1823199, baseEnd_1823199] using wordTrace_append hprefix tailTrace_1823199
  have hstable : (prefixWord ++ tailWord_1823199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823199).length < 2 ^ (prefixWord ++ tailWord_1823199).sum := by decide
  have hdescent : baseEnd_1823199 < baseStart_1823199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823205 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 4]
def baseStart_1823205 : Nat := 118140960795 + 1823205 * 2 ^ 59
def prefixEnd_1823205 : Nat := 4983230072969 + 3 ^ 40 * 1823205 * 2
def baseEnd_1823205 : Nat := 416080220746953082556773

theorem tailTrace_1823205 : CollatzResearch.WordTrace tailWord_1823205 prefixEnd_1823205 416080220746953082556773 := by
  unfold tailWord_1823205
  simp only [CollatzResearch.WordTrace]
  refine ⟨66497749359847138468991069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44331832906564758979327379 66497749359847138468991069)
  ·
    refine ⟨24936656009942676925871651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66497749359847138468991069 24936656009942676925871651)
    ·
      refine ⟨37404984014914015388807477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24936656009942676925871651 37404984014914015388807477)
      ·
        refine ⟨3506717251398188942700701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37404984014914015388807477 3506717251398188942700701)
        ·
          refine ⟨1315018969274320853512763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3506717251398188942700701 1315018969274320853512763)
          ·
            refine ⟨1972528453911481280269145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315018969274320853512763 1972528453911481280269145)
            ·
              refine ⟨1479396340433610960201859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972528453911481280269145 1479396340433610960201859)
              ·
                refine ⟨2219094510650416440302789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479396340433610960201859 2219094510650416440302789)
                ·
                  refine ⟨416080220746953082556773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219094510650416440302789 416080220746953082556773)
                  ·
                    rfl

theorem cell21_1823205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_1823205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823205 prefixEnd_1823205 := by exact prefixLift 1823205
  have htrace : WordTrace (prefixWord ++ tailWord_1823205) baseStart_1823205 baseEnd_1823205 := by
    simpa [prefixWord, tailWord_1823205, baseEnd_1823205] using wordTrace_append hprefix tailTrace_1823205
  have hstable : (prefixWord ++ tailWord_1823205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823205).length < 2 ^ (prefixWord ++ tailWord_1823205).sum := by decide
  have hdescent : baseEnd_1823205 < baseStart_1823205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823261 : List Nat := [1, 4, 2, 2, 1, 4, 1, 6]
def baseStart_1823261 : Nat := 118140960795 + 1823261 * 2 ^ 59
def prefixEnd_1823261 : Nat := 4983230072969 + 3 ^ 40 * 1823261 * 2
def baseEnd_1823261 : Nat := 138697666903303143207775

theorem tailTrace_1823261 : CollatzResearch.WordTrace tailWord_1823261 prefixEnd_1823261 138697666903303143207775 := by
  unfold tailWord_1823261
  simp only [CollatzResearch.WordTrace]
  refine ⟨66499791847644260033029637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44333194565096173355353091 66499791847644260033029637)
  ·
    refine ⟨12468710971433298756193057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66499791847644260033029637 12468710971433298756193057)
    ·
      refine ⟨9351533228574974067144793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12468710971433298756193057 9351533228574974067144793)
      ·
        refine ⟨7013649921431230550358595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9351533228574974067144793 7013649921431230550358595)
        ·
          refine ⟨10520474882146845825537893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7013649921431230550358595 10520474882146845825537893)
          ·
            refine ⟨1972589040402533592288355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10520474882146845825537893 1972589040402533592288355)
            ·
              refine ⟨2958883560603800388432533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972589040402533592288355 2958883560603800388432533)
              ·
                refine ⟨138697666903303143207775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2958883560603800388432533 138697666903303143207775)
                ·
                  rfl

theorem cell21_1823261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 6].length) (baseStart_1823261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823261 prefixEnd_1823261 := by exact prefixLift 1823261
  have htrace : WordTrace (prefixWord ++ tailWord_1823261) baseStart_1823261 baseEnd_1823261 := by
    simpa [prefixWord, tailWord_1823261, baseEnd_1823261] using wordTrace_append hprefix tailTrace_1823261
  have hstable : (prefixWord ++ tailWord_1823261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823261).length < 2 ^ (prefixWord ++ tailWord_1823261).sum := by decide
  have hdescent : baseEnd_1823261 < baseStart_1823261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823278 : List Nat := [4, 1, 3, 1, 3, 1, 3, 5]
def baseStart_1823278 : Nat := 118140960795 + 1823278 * 2 ^ 59
def prefixEnd_1823278 : Nat := 4983230072969 + 3 ^ 40 * 1823278 * 2
def baseEnd_1823278 : Nat := 138698960113840392613319

theorem tailTrace_1823278 : CollatzResearch.WordTrace tailWord_1823278 prefixEnd_1823278 138698960113840392613319 := by
  unfold tailWord_1823278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312551486072833992049811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44333607925721781290932325 8312551486072833992049811)
  ·
    refine ⟨12468827229109250988074717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312551486072833992049811 12468827229109250988074717)
    ·
      refine ⟨4675810210915969120528019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12468827229109250988074717 4675810210915969120528019)
      ·
        refine ⟨7013715316373953680792029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4675810210915969120528019 7013715316373953680792029)
        ·
          refine ⟨2630143243640232630297011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7013715316373953680792029 2630143243640232630297011)
          ·
            refine ⟨3945214865460348945445517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630143243640232630297011 3945214865460348945445517)
            ·
              refine ⟨1479455574547630854542069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3945214865460348945445517 1479455574547630854542069)
              ·
                refine ⟨138698960113840392613319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1479455574547630854542069 138698960113840392613319)
                ·
                  rfl

theorem cell21_1823278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_1823278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823278 prefixEnd_1823278 := by exact prefixLift 1823278
  have htrace : WordTrace (prefixWord ++ tailWord_1823278) baseStart_1823278 baseEnd_1823278 := by
    simpa [prefixWord, tailWord_1823278, baseEnd_1823278] using wordTrace_append hprefix tailTrace_1823278
  have hstable : (prefixWord ++ tailWord_1823278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823278).length < 2 ^ (prefixWord ++ tailWord_1823278).sum := by decide
  have hdescent : baseEnd_1823278 < baseStart_1823278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823289 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 6]
def baseStart_1823289 : Nat := 118140960795 + 1823289 * 2 ^ 59
def prefixEnd_1823289 : Nat := 4983230072969 + 3 ^ 40 * 1823289 * 2
def baseEnd_1823289 : Nat := 416099390691387603156601

theorem tailTrace_1823289 : CollatzResearch.WordTrace tailWord_1823289 prefixEnd_1823289 416099390691387603156601 := by
  unfold tailWord_1823289
  simp only [CollatzResearch.WordTrace]
  refine ⟨66500813091542820815048921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44333875394361880543365947 66500813091542820815048921)
  ·
    refine ⟨49875609818657115611286691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66500813091542820815048921 49875609818657115611286691)
    ·
      refine ⟨74813414727985673416930037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49875609818657115611286691 74813414727985673416930037)
      ·
        refine ⟨7013757630748656882837191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74813414727985673416930037 7013757630748656882837191)
        ·
          refine ⟨10520636446122985324255787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7013757630748656882837191 10520636446122985324255787)
          ·
            refine ⟨15780954669184477986383681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10520636446122985324255787 15780954669184477986383681)
            ·
              refine ⟨11835716001888358489787761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15780954669184477986383681 11835716001888358489787761)
              ·
                refine ⟨8876787001416268867340821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11835716001888358489787761 8876787001416268867340821)
                ·
                  refine ⟨416099390691387603156601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8876787001416268867340821 416099390691387603156601)
                  ·
                    rfl

theorem cell21_1823289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_1823289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823289 prefixEnd_1823289 := by exact prefixLift 1823289
  have htrace : WordTrace (prefixWord ++ tailWord_1823289) baseStart_1823289 baseEnd_1823289 := by
    simpa [prefixWord, tailWord_1823289, baseEnd_1823289] using wordTrace_append hprefix tailTrace_1823289
  have hstable : (prefixWord ++ tailWord_1823289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823289).length < 2 ^ (prefixWord ++ tailWord_1823289).sum := by decide
  have hdescent : baseEnd_1823289 < baseStart_1823289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823292 : List Nat := [2, 2, 2, 2, 3, 1, 1, 5, 3]
def baseStart_1823292 : Nat := 118140960795 + 1823292 * 2 ^ 59
def prefixEnd_1823292 : Nat := 4983230072969 + 3 ^ 40 * 1823292 * 2
def baseEnd_1823292 : Nat := 416100075332260264606595

theorem tailTrace_1823292 : CollatzResearch.WordTrace tailWord_1823292 prefixEnd_1823292 416100075332260264606595 := by
  unfold tailWord_1823292
  simp only [CollatzResearch.WordTrace]
  refine ⟨33250461255265976163704065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44333948340354634884938753 33250461255265976163704065)
  ·
    refine ⟨24937845941449482122778049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33250461255265976163704065 24937845941449482122778049)
    ·
      refine ⟨18703384456087111592083537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24937845941449482122778049 18703384456087111592083537)
      ·
        refine ⟨14027538342065333694062653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18703384456087111592083537 14027538342065333694062653)
        ·
          refine ⟨5260326878274500135273495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14027538342065333694062653 5260326878274500135273495)
          ·
            refine ⟨7890490317411750202910243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260326878274500135273495 7890490317411750202910243)
            ·
              refine ⟨11835735476117625304365365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7890490317411750202910243 11835735476117625304365365)
              ·
                refine ⟨1109600200886027372284253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11835735476117625304365365 1109600200886027372284253)
                ·
                  refine ⟨416100075332260264606595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109600200886027372284253 416100075332260264606595)
                  ·
                    rfl

theorem cell21_1823292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 3].length) (baseStart_1823292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823292 prefixEnd_1823292 := by exact prefixLift 1823292
  have htrace : WordTrace (prefixWord ++ tailWord_1823292) baseStart_1823292 baseEnd_1823292 := by
    simpa [prefixWord, tailWord_1823292, baseEnd_1823292] using wordTrace_append hprefix tailTrace_1823292
  have hstable : (prefixWord ++ tailWord_1823292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823292).length < 2 ^ (prefixWord ++ tailWord_1823292).sum := by decide
  have hdescent : baseEnd_1823292 < baseStart_1823292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823306 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_1823306 : Nat := 118140960795 + 1823306 * 2 ^ 59
def prefixEnd_1823306 : Nat := 4983230072969 + 3 ^ 40 * 1823306 * 2
def baseEnd_1823306 : Nat := 416103270322999351373233

theorem tailTrace_1823306 : CollatzResearch.WordTrace tailWord_1823306 prefixEnd_1823306 416103270322999351373233 := by
  unfold tailWord_1823306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16625358283120308179604443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44334288754987488478945181 16625358283120308179604443)
  ·
    refine ⟨24938037424680462269406665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16625358283120308179604443 24938037424680462269406665)
    ·
      refine ⟨18703528068510346702054999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24938037424680462269406665 18703528068510346702054999)
      ·
        refine ⟨28055292102765520053082499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18703528068510346702054999 28055292102765520053082499)
        ·
          refine ⟨42082938154148280079623749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28055292102765520053082499 42082938154148280079623749)
          ·
            refine ⟨7890550903902802514929453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42082938154148280079623749 7890550903902802514929453)
            ·
              refine ⟨2958956588963550943098545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7890550903902802514929453 2958956588963550943098545)
              ·
                refine ⟨2219217441722663207323909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2958956588963550943098545 2219217441722663207323909)
                ·
                  refine ⟨416103270322999351373233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219217441722663207323909 416103270322999351373233)
                  ·
                    rfl

theorem cell21_1823306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_1823306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823306 prefixEnd_1823306 := by exact prefixLift 1823306
  have htrace : WordTrace (prefixWord ++ tailWord_1823306) baseStart_1823306 baseEnd_1823306 := by
    simpa [prefixWord, tailWord_1823306, baseEnd_1823306] using wordTrace_append hprefix tailTrace_1823306
  have hstable : (prefixWord ++ tailWord_1823306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823306).length < 2 ^ (prefixWord ++ tailWord_1823306).sum := by decide
  have hdescent : baseEnd_1823306 < baseStart_1823306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823309 : List Nat := [1, 6, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1823309 : Nat := 118140960795 + 1823309 * 2 ^ 59
def prefixEnd_1823309 : Nat := 4983230072969 + 3 ^ 40 * 1823309 * 2
def baseEnd_1823309 : Nat := 416103954963872012823227

theorem tailTrace_1823309 : CollatzResearch.WordTrace tailWord_1823309 prefixEnd_1823309 416103954963872012823227 := by
  unfold tailWord_1823309
  simp only [CollatzResearch.WordTrace]
  refine ⟨66501542551470364230776981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44334361700980242820517987 66501542551470364230776981)
  ·
    refine ⟨3117259807100173323317671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66501542551470364230776981 3117259807100173323317671)
    ·
      refine ⟨4675889710650259984976507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3117259807100173323317671 4675889710650259984976507)
      ·
        refine ⟨7013834565975389977464761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4675889710650259984976507 7013834565975389977464761)
        ·
          refine ⟨5260375924481542483098571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7013834565975389977464761 5260375924481542483098571)
          ·
            refine ⟨7890563886722313724647857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260375924481542483098571 7890563886722313724647857)
            ·
              refine ⟨5917922915041735293485893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7890563886722313724647857 5917922915041735293485893)
              ·
                refine ⟨1109610546570325367528605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5917922915041735293485893 1109610546570325367528605)
                ·
                  refine ⟨416103954963872012823227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109610546570325367528605 416103954963872012823227)
                  ·
                    rfl

theorem cell21_1823309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1823309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823309 prefixEnd_1823309 := by exact prefixLift 1823309
  have htrace : WordTrace (prefixWord ++ tailWord_1823309) baseStart_1823309 baseEnd_1823309 := by
    simpa [prefixWord, tailWord_1823309, baseEnd_1823309] using wordTrace_append hprefix tailTrace_1823309
  have hstable : (prefixWord ++ tailWord_1823309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823309).length < 2 ^ (prefixWord ++ tailWord_1823309).sum := by decide
  have hdescent : baseEnd_1823309 < baseStart_1823309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823365 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 6]
def baseStart_1823365 : Nat := 118140960795 + 1823365 * 2 ^ 59
def prefixEnd_1823365 : Nat := 4983230072969 + 3 ^ 40 * 1823365 * 2
def baseEnd_1823365 : Nat := 416116734926828359889779

theorem tailTrace_1823365 : CollatzResearch.WordTrace tailWord_1823365 prefixEnd_1823365 416116734926828359889779 := by
  unfold tailWord_1823365
  simp only [CollatzResearch.WordTrace]
  refine ⟨66503585039267485794815549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44335723359511657196543699 66503585039267485794815549)
  ·
    refine ⟨24938844389725307173055831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66503585039267485794815549 24938844389725307173055831)
    ·
      refine ⟨37408266584587960759583747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24938844389725307173055831 37408266584587960759583747)
      ·
        refine ⟨56112399876881941139375621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37408266584587960759583747 56112399876881941139375621)
        ·
          refine ⟨10521074976915363963632929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56112399876881941139375621 10521074976915363963632929)
          ·
            refine ⟨7890806232686522972724697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10521074976915363963632929 7890806232686522972724697)
            ·
              refine ⟨5918104674514892229543523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7890806232686522972724697 5918104674514892229543523)
              ·
                refine ⟨8877157011772338344315285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918104674514892229543523 8877157011772338344315285)
                ·
                  refine ⟨416116734926828359889779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8877157011772338344315285 416116734926828359889779)
                  ·
                    rfl

theorem cell21_1823365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_1823365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823365 prefixEnd_1823365 := by exact prefixLift 1823365
  have htrace : WordTrace (prefixWord ++ tailWord_1823365) baseStart_1823365 baseEnd_1823365 := by
    simpa [prefixWord, tailWord_1823365, baseEnd_1823365] using wordTrace_append hprefix tailTrace_1823365
  have hstable : (prefixWord ++ tailWord_1823365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823365).length < 2 ^ (prefixWord ++ tailWord_1823365).sum := by decide
  have hdescent : baseEnd_1823365 < baseStart_1823365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823441 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 4]
def baseStart_1823441 : Nat := 118140960795 + 1823441 * 2 ^ 59
def prefixEnd_1823441 : Nat := 4983230072969 + 3 ^ 40 * 1823441 * 2
def baseEnd_1823441 : Nat := 416134079162269116622957

theorem tailTrace_1823441 : CollatzResearch.WordTrace tailWord_1823441 prefixEnd_1823441 416134079162269116622957 := by
  unfold tailWord_1823441
  simp only [CollatzResearch.WordTrace]
  refine ⟨66506356986992150774582177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44337571324661433849721451 66506356986992150774582177)
  ·
    refine ⟨49879767740244113080936633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66506356986992150774582177 49879767740244113080936633)
    ·
      refine ⟨37409825805183084810702475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49879767740244113080936633 37409825805183084810702475)
      ·
        refine ⟨56114738707774627216053713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37409825805183084810702475 56114738707774627216053713)
        ·
          refine ⟨42086054030830970412040285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56114738707774627216053713 42086054030830970412040285)
          ·
            refine ⟨15782270261561613904515107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42086054030830970412040285 15782270261561613904515107)
            ·
              refine ⟨23673405392342420856772661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15782270261561613904515107 23673405392342420856772661)
              ·
                refine ⟨2219381755532101955322437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23673405392342420856772661 2219381755532101955322437)
                ·
                  refine ⟨416134079162269116622957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219381755532101955322437 416134079162269116622957)
                  ·
                    rfl

theorem cell21_1823441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_1823441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823441 prefixEnd_1823441 := by exact prefixLift 1823441
  have htrace : WordTrace (prefixWord ++ tailWord_1823441) baseStart_1823441 baseEnd_1823441 := by
    simpa [prefixWord, tailWord_1823441, baseEnd_1823441] using wordTrace_append hprefix tailTrace_1823441
  have hstable : (prefixWord ++ tailWord_1823441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823441).length < 2 ^ (prefixWord ++ tailWord_1823441).sum := by decide
  have hdescent : baseEnd_1823441 < baseStart_1823441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823444 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1823444 : Nat := 118140960795 + 1823444 * 2 ^ 59
def prefixEnd_1823444 : Nat := 4983230072969 + 3 ^ 40 * 1823444 * 2
def baseEnd_1823444 : Nat := 416134763803141778072951

theorem tailTrace_1823444 : CollatzResearch.WordTrace tailWord_1823444 prefixEnd_1823444 416134763803141778072951 := by
  unfold tailWord_1823444
  simp only [CollatzResearch.WordTrace]
  refine ⟨33253233202990641143470693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44337644270654188191294257 33253233202990641143470693)
  ·
    refine ⟨6234981225560745214400755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33253233202990641143470693 6234981225560745214400755)
    ·
      refine ⟨9352471838341117821601133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6234981225560745214400755 9352471838341117821601133)
      ·
        refine ⟨3507176939377919183100425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9352471838341117821601133 3507176939377919183100425)
        ·
          refine ⟨2630382704533439387325319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3507176939377919183100425 2630382704533439387325319)
          ·
            refine ⟨3945574056800159080987979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630382704533439387325319 3945574056800159080987979)
            ·
              refine ⟨5918361085200238621481969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945574056800159080987979 5918361085200238621481969)
              ·
                refine ⟨4438770813900178966111477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5918361085200238621481969 4438770813900178966111477)
                ·
                  refine ⟨416134763803141778072951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4438770813900178966111477 416134763803141778072951)
                  ·
                    rfl

theorem cell21_1823444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1823444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823444 prefixEnd_1823444 := by exact prefixLift 1823444
  have htrace : WordTrace (prefixWord ++ tailWord_1823444) baseStart_1823444 baseEnd_1823444 := by
    simpa [prefixWord, tailWord_1823444, baseEnd_1823444] using wordTrace_append hprefix tailTrace_1823444
  have hstable : (prefixWord ++ tailWord_1823444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823444).length < 2 ^ (prefixWord ++ tailWord_1823444).sum := by decide
  have hdescent : baseEnd_1823444 < baseStart_1823444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823520 : List Nat := [2, 1, 1, 5, 1, 2, 3, 3, 3]
def baseStart_1823520 : Nat := 118140960795 + 1823520 * 2 ^ 59
def prefixEnd_1823520 : Nat := 4983230072969 + 3 ^ 40 * 1823520 * 2
def baseEnd_1823520 : Nat := 416152108038582534806129

theorem tailTrace_1823520 : CollatzResearch.WordTrace tailWord_1823520 prefixEnd_1823520 416152108038582534806129 := by
  unfold tailWord_1823520
  simp only [CollatzResearch.WordTrace]
  refine ⟨33254619176852973633354007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44339492235803964844472009 33254619176852973633354007)
  ·
    refine ⟨49881928765279460450031011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33254619176852973633354007 49881928765279460450031011)
    ·
      refine ⟨74822893147919190675046517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49881928765279460450031011 74822893147919190675046517)
      ·
        refine ⟨7014646232617424125785611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74822893147919190675046517 7014646232617424125785611)
        ·
          refine ⟨10521969348926136188678417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014646232617424125785611 10521969348926136188678417)
          ·
            refine ⟨7891477011694602141508813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10521969348926136188678417 7891477011694602141508813)
            ·
              refine ⟨2959303879385475803065805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7891477011694602141508813 2959303879385475803065805)
              ·
                refine ⟨1109738954769553426149677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2959303879385475803065805 1109738954769553426149677)
                ·
                  refine ⟨416152108038582534806129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109738954769553426149677 416152108038582534806129)
                  ·
                    rfl

theorem cell21_1823520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_1823520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823520 prefixEnd_1823520 := by exact prefixLift 1823520
  have htrace : WordTrace (prefixWord ++ tailWord_1823520) baseStart_1823520 baseEnd_1823520 := by
    simpa [prefixWord, tailWord_1823520, baseEnd_1823520] using wordTrace_append hprefix tailTrace_1823520
  have hstable : (prefixWord ++ tailWord_1823520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823520).length < 2 ^ (prefixWord ++ tailWord_1823520).sum := by decide
  have hdescent : baseEnd_1823520 < baseStart_1823520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823534 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1823534 : Nat := 118140960795 + 1823534 * 2 ^ 59
def prefixEnd_1823534 : Nat := 4983230072969 + 3 ^ 40 * 1823534 * 2
def baseEnd_1823534 : Nat := 416155303029321621572767

theorem tailTrace_1823534 : CollatzResearch.WordTrace tailWord_1823534 prefixEnd_1823534 416155303029321621572767 := by
  unfold tailWord_1823534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8313718621956903457214707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44339832650436818438478437 8313718621956903457214707)
  ·
    refine ⟨12470577932935355185822061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8313718621956903457214707 12470577932935355185822061)
    ·
      refine ⟨4676466724850758194683273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12470577932935355185822061 4676466724850758194683273)
      ·
        refine ⟨3507350043638068646012455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4676466724850758194683273 3507350043638068646012455)
        ·
          refine ⟨5261025065457102969018683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3507350043638068646012455 5261025065457102969018683)
          ·
            refine ⟨7891537598185654453528025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261025065457102969018683 7891537598185654453528025)
            ·
              refine ⟨5918653198639240840146019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7891537598185654453528025 5918653198639240840146019)
              ·
                refine ⟨8877979797958861260219029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918653198639240840146019 8877979797958861260219029)
                ·
                  refine ⟨416155303029321621572767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8877979797958861260219029 416155303029321621572767)
                  ·
                    rfl

theorem cell21_1823534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1823534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823534 prefixEnd_1823534 := by exact prefixLift 1823534
  have htrace : WordTrace (prefixWord ++ tailWord_1823534) baseStart_1823534 baseEnd_1823534 := by
    simpa [prefixWord, tailWord_1823534, baseEnd_1823534] using wordTrace_append hprefix tailTrace_1823534
  have hstable : (prefixWord ++ tailWord_1823534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823534).length < 2 ^ (prefixWord ++ tailWord_1823534).sum := by decide
  have hdescent : baseEnd_1823534 < baseStart_1823534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823551 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 4]
def baseStart_1823551 : Nat := 118140960795 + 1823551 * 2 ^ 59
def prefixEnd_1823551 : Nat := 4983230072969 + 3 ^ 40 * 1823551 * 2
def baseEnd_1823551 : Nat := 416159182660933369789399

theorem tailTrace_1823551 : CollatzResearch.WordTrace tailWord_1823551 prefixEnd_1823551 416159182660933369789399 := by
  unfold tailWord_1823551
  simp only [CollatzResearch.WordTrace]
  refine ⟨66510369016593639561086507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44340246011062426374057671 66510369016593639561086507)
  ·
    refine ⟨99765553524890459341629761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66510369016593639561086507 99765553524890459341629761)
    ·
      refine ⟨74824165143667844506222321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99765553524890459341629761 74824165143667844506222321)
      ·
        refine ⟨56118123857750883379666741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74824165143667844506222321 56118123857750883379666741)
        ·
          refine ⟨5261074111664145316843757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56118123857750883379666741 5261074111664145316843757)
          ·
            refine ⟨1972902791874054493816409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5261074111664145316843757 1972902791874054493816409)
            ·
              refine ⟨1479677093905540870362307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972902791874054493816409 1479677093905540870362307)
              ·
                refine ⟨2219515640858311305543461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479677093905540870362307 2219515640858311305543461)
                ·
                  refine ⟨416159182660933369789399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219515640858311305543461 416159182660933369789399)
                  ·
                    rfl

theorem cell21_1823551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 4].length) (baseStart_1823551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823551 prefixEnd_1823551 := by exact prefixLift 1823551
  have htrace : WordTrace (prefixWord ++ tailWord_1823551) baseStart_1823551 baseEnd_1823551 := by
    simpa [prefixWord, tailWord_1823551, baseEnd_1823551] using wordTrace_append hprefix tailTrace_1823551
  have hstable : (prefixWord ++ tailWord_1823551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823551).length < 2 ^ (prefixWord ++ tailWord_1823551).sum := by decide
  have hdescent : baseEnd_1823551 < baseStart_1823551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823576 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_1823576 : Nat := 118140960795 + 1823576 * 2 ^ 59
def prefixEnd_1823576 : Nat := 4983230072969 + 3 ^ 40 * 1823576 * 2
def baseEnd_1823576 : Nat := 416164888001538881872681

theorem tailTrace_1823576 : CollatzResearch.WordTrace tailWord_1823576 prefixEnd_1823576 416164888001538881872681 := by
  unfold tailWord_1823576
  simp only [CollatzResearch.WordTrace]
  refine ⟨33255640420751534415373291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44340853894335379220497721 33255640420751534415373291)
  ·
    refine ⟨49883460631127301623059937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33255640420751534415373291 49883460631127301623059937)
    ·
      refine ⟨37412595473345476217294953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49883460631127301623059937 37412595473345476217294953)
      ·
        refine ⟨28059446605009107162971215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37412595473345476217294953 28059446605009107162971215)
        ·
          refine ⟨42089169907513660744456823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28059446605009107162971215 42089169907513660744456823)
          ·
            refine ⟨63133754861270491116685235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42089169907513660744456823 63133754861270491116685235)
            ·
              refine ⟨94700632291905736675027853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63133754861270491116685235 94700632291905736675027853)
              ·
                refine ⟨35512737109464651253135445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94700632291905736675027853 35512737109464651253135445)
                ·
                  refine ⟨416164888001538881872681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35512737109464651253135445 416164888001538881872681)
                  ·
                    rfl

theorem cell21_1823576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_1823576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823576 prefixEnd_1823576 := by exact prefixLift 1823576
  have htrace : WordTrace (prefixWord ++ tailWord_1823576) baseStart_1823576 baseEnd_1823576 := by
    simpa [prefixWord, tailWord_1823576, baseEnd_1823576] using wordTrace_append hprefix tailTrace_1823576
  have hstable : (prefixWord ++ tailWord_1823576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823576).length < 2 ^ (prefixWord ++ tailWord_1823576).sum := by decide
  have hdescent : baseEnd_1823576 < baseStart_1823576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823644 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 4]
def baseStart_1823644 : Nat := 118140960795 + 1823644 * 2 ^ 59
def prefixEnd_1823644 : Nat := 4983230072969 + 3 ^ 40 * 1823644 * 2
def baseEnd_1823644 : Nat := 416180406527985874739209

theorem tailTrace_1823644 : CollatzResearch.WordTrace tailWord_1823644 prefixEnd_1823644 416180406527985874739209 := by
  unfold tailWord_1823644
  simp only [CollatzResearch.WordTrace]
  refine ⟨33256880502628358222110993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44342507336837810962814657 33256880502628358222110993)
  ·
    refine ⟨24942660376971268666583245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33256880502628358222110993 24942660376971268666583245)
    ·
      refine ⟨9353497641364225749968717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24942660376971268666583245 9353497641364225749968717)
      ·
        refine ⟨3507561615511584656238269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9353497641364225749968717 3507561615511584656238269)
        ·
          refine ⟨1315335605816844246089351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3507561615511584656238269 1315335605816844246089351)
          ·
            refine ⟨1973003408725266369134027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315335605816844246089351 1973003408725266369134027)
            ·
              refine ⟨2959505113087899553701041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973003408725266369134027 2959505113087899553701041)
              ·
                refine ⟨2219628834815924665275781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2959505113087899553701041 2219628834815924665275781)
                ·
                  refine ⟨416180406527985874739209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219628834815924665275781 416180406527985874739209)
                  ·
                    rfl

theorem cell21_1823644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_1823644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823644 prefixEnd_1823644 := by exact prefixLift 1823644
  have htrace : WordTrace (prefixWord ++ tailWord_1823644) baseStart_1823644 baseEnd_1823644 := by
    simpa [prefixWord, tailWord_1823644, baseEnd_1823644] using wordTrace_append hprefix tailTrace_1823644
  have hstable : (prefixWord ++ tailWord_1823644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823644).length < 2 ^ (prefixWord ++ tailWord_1823644).sum := by decide
  have hdescent : baseEnd_1823644 < baseStart_1823644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823700 : List Nat := [2, 4, 1, 2, 1, 4, 7]
def baseStart_1823700 : Nat := 118140960795 + 1823700 * 2 ^ 59
def prefixEnd_1823700 : Nat := 4983230072969 + 3 ^ 40 * 1823700 * 2
def baseEnd_1823700 : Nat := 46243687387882469089529

theorem tailTrace_1823700 : CollatzResearch.WordTrace tailWord_1823700 prefixEnd_1823700 46243687387882469089529 := by
  unfold tailWord_1823700
  simp only [CollatzResearch.WordTrace]
  refine ⟨33257901746526919004130277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44343868995369225338840369 33257901746526919004130277)
  ·
    refine ⟨6235856577473797313274427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33257901746526919004130277 6235856577473797313274427)
    ·
      refine ⟨9353784866210695969911641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6235856577473797313274427 9353784866210695969911641)
      ·
        refine ⟨7015338649658021977433731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9353784866210695969911641 7015338649658021977433731)
        ·
          refine ⟨10523007974487032966150597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7015338649658021977433731 10523007974487032966150597)
          ·
            refine ⟨1973063995216318681153237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10523007974487032966150597 1973063995216318681153237)
            ·
              refine ⟨46243687387882469089529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1973063995216318681153237 46243687387882469089529)
              ·
                rfl

theorem cell21_1823700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 7].length) (baseStart_1823700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823700 prefixEnd_1823700 := by exact prefixLift 1823700
  have htrace : WordTrace (prefixWord ++ tailWord_1823700) baseStart_1823700 baseEnd_1823700 := by
    simpa [prefixWord, tailWord_1823700, baseEnd_1823700] using wordTrace_append hprefix tailTrace_1823700
  have hstable : (prefixWord ++ tailWord_1823700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823700).length < 2 ^ (prefixWord ++ tailWord_1823700).sum := by decide
  have hdescent : baseEnd_1823700 < baseStart_1823700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823717 : List Nat := [1, 3, 1, 6, 1, 1, 2, 6]
def baseStart_1823717 : Nat := 118140960795 + 1823717 * 2 ^ 59
def prefixEnd_1823717 : Nat := 4983230072969 + 3 ^ 40 * 1823717 * 2
def baseEnd_1823717 : Nat := 138732355374184656674131

theorem tailTrace_1823717 : CollatzResearch.WordTrace tailWord_1823717 prefixEnd_1823717 138732355374184656674131 := by
  unfold tailWord_1823717
  simp only [CollatzResearch.WordTrace]
  refine ⟨66516423533992249911629405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44344282355994833274419603 66516423533992249911629405)
  ·
    refine ⟨24943658825247093716861027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66516423533992249911629405 24943658825247093716861027)
    ·
      refine ⟨37415488237870640575291541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24943658825247093716861027 37415488237870640575291541)
      ·
        refine ⟨1753851011150186276966791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37415488237870640575291541 1753851011150186276966791)
        ·
          refine ⟨2630776516725279415450187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753851011150186276966791 2630776516725279415450187)
          ·
            refine ⟨3946164775087919123175281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630776516725279415450187 3946164775087919123175281)
            ·
              refine ⟨2959623581315939342381461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946164775087919123175281 2959623581315939342381461)
              ·
                refine ⟨138732355374184656674131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2959623581315939342381461 138732355374184656674131)
                ·
                  rfl

theorem cell21_1823717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 6].length) (baseStart_1823717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823717 prefixEnd_1823717 := by exact prefixLift 1823717
  have htrace : WordTrace (prefixWord ++ tailWord_1823717) baseStart_1823717 baseEnd_1823717 := by
    simpa [prefixWord, tailWord_1823717, baseEnd_1823717] using wordTrace_append hprefix tailTrace_1823717
  have hstable : (prefixWord ++ tailWord_1823717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823717).length < 2 ^ (prefixWord ++ tailWord_1823717).sum := by decide
  have hdescent : baseEnd_1823717 < baseStart_1823717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1823765 : List Nat := [1, 3, 2, 1, 4, 3, 2, 2, 3]
def baseStart_1823765 : Nat := 118140960795 + 1823765 * 2 ^ 59
def prefixEnd_1823765 : Nat := 4983230072969 + 3 ^ 40 * 1823765 * 2
def baseEnd_1823765 : Nat := 416208020376516553222295

theorem tailTrace_1823765 : CollatzResearch.WordTrace tailWord_1823765 prefixEnd_1823765 416208020376516553222295 := by
  unfold tailWord_1823765
  simp only [CollatzResearch.WordTrace]
  refine ⟨66518174237818354109376749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44345449491878902739584499 66518174237818354109376749)
  ·
    refine ⟨24944315339181882791016281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66518174237818354109376749 24944315339181882791016281)
    ·
      refine ⟨18708236504386412093262211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24944315339181882791016281 18708236504386412093262211)
      ·
        refine ⟨28062354756579618139893317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18708236504386412093262211 28062354756579618139893317)
        ·
          refine ⟨5261691516858678401229997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28062354756579618139893317 5261691516858678401229997)
          ·
            refine ⟨1973134318822004400461249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5261691516858678401229997 1973134318822004400461249)
            ·
              refine ⟨1479850739116503300345937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973134318822004400461249 1479850739116503300345937)
              ·
                refine ⟨1109888054337377475259453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1479850739116503300345937 1109888054337377475259453)
                ·
                  refine ⟨416208020376516553222295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109888054337377475259453 416208020376516553222295)
                  ·
                    rfl

theorem cell21_1823765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_1823765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1823765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1823765 prefixEnd_1823765 := by exact prefixLift 1823765
  have htrace : WordTrace (prefixWord ++ tailWord_1823765) baseStart_1823765 baseEnd_1823765 := by
    simpa [prefixWord, tailWord_1823765, baseEnd_1823765] using wordTrace_append hprefix tailTrace_1823765
  have hstable : (prefixWord ++ tailWord_1823765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1823765).length < 2 ^ (prefixWord ++ tailWord_1823765).sum := by decide
  have hdescent : baseEnd_1823765 < baseStart_1823765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1823765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824035 : List Nat := [1, 1, 1, 4, 2, 3, 3, 3, 3]
def baseStart_1824035 : Nat := 118140960795 + 1824035 * 2 ^ 59
def prefixEnd_1824035 : Nat := 4983230072969 + 3 ^ 40 * 1824035 * 2
def baseEnd_1824035 : Nat := 416269638055056083721743

theorem tailTrace_1824035 : CollatzResearch.WordTrace tailWord_1824035 prefixEnd_1824035 416269638055056083721743 := by
  unfold tailWord_1824035
  simp only [CollatzResearch.WordTrace]
  refine ⟨66528021946840190221705559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44352014631226793481137039 66528021946840190221705559)
  ·
    refine ⟨99792032920260285332558339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66528021946840190221705559 99792032920260285332558339)
    ·
      refine ⟨149688049380390427998837509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99792032920260285332558339 149688049380390427998837509)
      ·
        refine ⟨28066509258823205249782033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149688049380390427998837509 28066509258823205249782033)
        ·
          refine ⟨21049881944117403937336525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28066509258823205249782033 21049881944117403937336525)
          ·
            refine ⟨7893705729044026476501197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21049881944117403937336525 7893705729044026476501197)
            ·
              refine ⟨2960139648391509928687949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7893705729044026476501197 2960139648391509928687949)
              ·
                refine ⟨1110052368146816223257981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2960139648391509928687949 1110052368146816223257981)
                ·
                  refine ⟨416269638055056083721743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110052368146816223257981 416269638055056083721743)
                  ·
                    rfl

theorem cell21_1824035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 3].length) (baseStart_1824035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824035 prefixEnd_1824035 := by exact prefixLift 1824035
  have htrace : WordTrace (prefixWord ++ tailWord_1824035) baseStart_1824035 baseEnd_1824035 := by
    simpa [prefixWord, tailWord_1824035, baseEnd_1824035] using wordTrace_append hprefix tailTrace_1824035
  have hstable : (prefixWord ++ tailWord_1824035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824035).length < 2 ^ (prefixWord ++ tailWord_1824035).sum := by decide
  have hdescent : baseEnd_1824035 < baseStart_1824035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824063 : List Nat := [1, 1, 2, 2, 4, 3, 2, 6]
def baseStart_1824063 : Nat := 118140960795 + 1824063 * 2 ^ 59
def prefixEnd_1824063 : Nat := 4983230072969 + 3 ^ 40 * 1824063 * 2
def baseEnd_1824063 : Nat := 138758676012178085751673

theorem tailTrace_1824063 : CollatzResearch.WordTrace tailWord_1824063 prefixEnd_1824063 138758676012178085751673 := by
  unfold tailWord_1824063
  simp only [CollatzResearch.WordTrace]
  refine ⟨66529043190738751003724843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44352695460492500669149895 66529043190738751003724843)
  ·
    refine ⟨99793564786108126505587265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66529043190738751003724843 99793564786108126505587265)
    ·
      refine ⟨74845173589581094879190449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99793564786108126505587265 74845173589581094879190449)
      ·
        refine ⟨56133880192185821159392837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74845173589581094879190449 56133880192185821159392837)
        ·
          refine ⟨10525102536034841467386157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56133880192185821159392837 10525102536034841467386157)
          ·
            refine ⟨3946913451013065550269809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10525102536034841467386157 3946913451013065550269809)
            ·
              refine ⟨2960185088259799162702357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946913451013065550269809 2960185088259799162702357)
              ·
                refine ⟨138758676012178085751673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2960185088259799162702357 138758676012178085751673)
                ·
                  rfl

theorem cell21_1824063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 6].length) (baseStart_1824063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824063 prefixEnd_1824063 := by exact prefixLift 1824063
  have htrace : WordTrace (prefixWord ++ tailWord_1824063) baseStart_1824063 baseEnd_1824063 := by
    simpa [prefixWord, tailWord_1824063, baseEnd_1824063] using wordTrace_append hprefix tailTrace_1824063
  have hstable : (prefixWord ++ tailWord_1824063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824063).length < 2 ^ (prefixWord ++ tailWord_1824063).sum := by decide
  have hdescent : baseEnd_1824063 < baseStart_1824063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824139 : List Nat := [1, 1, 1, 1, 4, 3, 5, 5]
def baseStart_1824139 : Nat := 118140960795 + 1824139 * 2 ^ 59
def prefixEnd_1824139 : Nat := 4983230072969 + 3 ^ 40 * 1824139 * 2
def baseEnd_1824139 : Nat := 138764457423991671329399

theorem tailTrace_1824139 : CollatzResearch.WordTrace tailWord_1824139 prefixEnd_1824139 138764457423991671329399 := by
  unfold tailWord_1824139
  simp only [CollatzResearch.WordTrace]
  refine ⟨66531815138463415983491471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44354543425642277322327647 66531815138463415983491471)
  ·
    refine ⟨99797722707695123975237207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66531815138463415983491471 99797722707695123975237207)
    ·
      refine ⟨149696584061542685962855811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99797722707695123975237207 149696584061542685962855811)
      ·
        refine ⟨224544876092314028944283717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149696584061542685962855811 224544876092314028944283717)
        ·
          refine ⟨42102164267308880427053197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224544876092314028944283717 42102164267308880427053197)
          ·
            refine ⟨15788311600240830160144949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42102164267308880427053197 15788311600240830160144949)
            ·
              refine ⟨1480154212522577827513589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15788311600240830160144949 1480154212522577827513589)
              ·
                refine ⟨138764457423991671329399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1480154212522577827513589 138764457423991671329399)
                ·
                  rfl

theorem cell21_1824139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 5].length) (baseStart_1824139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824139 prefixEnd_1824139 := by exact prefixLift 1824139
  have htrace : WordTrace (prefixWord ++ tailWord_1824139) baseStart_1824139 baseEnd_1824139 := by
    simpa [prefixWord, tailWord_1824139, baseEnd_1824139] using wordTrace_append hprefix tailTrace_1824139
  have hstable : (prefixWord ++ tailWord_1824139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824139).length < 2 ^ (prefixWord ++ tailWord_1824139).sum := by decide
  have hdescent : baseEnd_1824139 < baseStart_1824139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824156 : List Nat := [2, 2, 3, 4, 1, 1, 8]
def baseStart_1824156 : Nat := 118140960795 + 1824156 * 2 ^ 59
def prefixEnd_1824156 : Nat := 4983230072969 + 3 ^ 40 * 1824156 * 2
def baseEnd_1824156 : Nat := 46255250211509640244981

theorem tailTrace_1824156 : CollatzResearch.WordTrace tailWord_1824156 prefixEnd_1824156 46255250211509640244981 := by
  unfold tailWord_1824156
  simp only [CollatzResearch.WordTrace]
  refine ⟨33266217589700913943430161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44354956786267885257906881 33266217589700913943430161)
  ·
    refine ⟨24949663192275685457572621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33266217589700913943430161 24949663192275685457572621)
    ·
      refine ⟨9356123697103382046589733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24949663192275685457572621 9356123697103382046589733)
      ·
        refine ⟨1754273193206884133735575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9356123697103382046589733 1754273193206884133735575)
        ·
          refine ⟨2631409789810326200603363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754273193206884133735575 2631409789810326200603363)
          ·
            refine ⟨3947114684715489300905045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631409789810326200603363 3947114684715489300905045)
            ·
              refine ⟨46255250211509640244981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3947114684715489300905045 46255250211509640244981)
              ·
                rfl

theorem cell21_1824156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 8].length) (baseStart_1824156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824156 prefixEnd_1824156 := by exact prefixLift 1824156
  have htrace : WordTrace (prefixWord ++ tailWord_1824156) baseStart_1824156 baseEnd_1824156 := by
    simpa [prefixWord, tailWord_1824156, baseEnd_1824156] using wordTrace_append hprefix tailTrace_1824156
  have hstable : (prefixWord ++ tailWord_1824156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824156).length < 2 ^ (prefixWord ++ tailWord_1824156).sum := by decide
  have hdescent : baseEnd_1824156 < baseStart_1824156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824184 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_1824184 : Nat := 118140960795 + 1824184 * 2 ^ 59
def prefixEnd_1824184 : Nat := 4983230072969 + 3 ^ 40 * 1824184 * 2
def baseEnd_1824184 : Nat := 416303641885064935738105

theorem tailTrace_1824184 : CollatzResearch.WordTrace tailWord_1824184 prefixEnd_1824184 416303641885064935738105 := by
  unfold tailWord_1824184
  simp only [CollatzResearch.WordTrace]
  refine ⟨33266728211650194334439803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44355637615533592445919737 33266728211650194334439803)
  ·
    refine ⟨49900092317475291501659705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33266728211650194334439803 49900092317475291501659705)
    ·
      refine ⟨37425069238106468626244779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49900092317475291501659705 37425069238106468626244779)
      ·
        refine ⟨56137603857159702939367169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37425069238106468626244779 56137603857159702939367169)
        ·
          refine ⟨42103202892869777204525377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56137603857159702939367169 42103202892869777204525377)
          ·
            refine ⟨31577402169652332903394033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42103202892869777204525377 31577402169652332903394033)
            ·
              refine ⟨23683051627239249677545525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31577402169652332903394033 23683051627239249677545525)
              ·
                refine ⟨2220286090053679657269893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23683051627239249677545525 2220286090053679657269893)
                ·
                  refine ⟨416303641885064935738105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2220286090053679657269893 416303641885064935738105)
                  ·
                    rfl

theorem cell21_1824184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_1824184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824184 prefixEnd_1824184 := by exact prefixLift 1824184
  have htrace : WordTrace (prefixWord ++ tailWord_1824184) baseStart_1824184 baseEnd_1824184 := by
    simpa [prefixWord, tailWord_1824184, baseEnd_1824184] using wordTrace_append hprefix tailTrace_1824184
  have hstable : (prefixWord ++ tailWord_1824184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824184).length < 2 ^ (prefixWord ++ tailWord_1824184).sum := by decide
  have hdescent : baseEnd_1824184 < baseStart_1824184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824204 : List Nat := [2, 2, 1, 4, 2, 3, 1, 3, 3]
def baseStart_1824204 : Nat := 118140960795 + 1824204 * 2 ^ 59
def prefixEnd_1824204 : Nat := 4983230072969 + 3 ^ 40 * 1824204 * 2
def baseEnd_1824204 : Nat := 416308206157549345404731

theorem tailTrace_1824204 : CollatzResearch.WordTrace tailWord_1824204 prefixEnd_1824204 416308206157549345404731 := by
  unfold tailWord_1824204
  simp only [CollatzResearch.WordTrace]
  refine ⟨33267092941613966042303833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44356123922151954723071777 33267092941613966042303833)
  ·
    refine ⟨24950319706210474531727875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33267092941613966042303833 24950319706210474531727875)
    ·
      refine ⟨37425479559315711797591813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24950319706210474531727875 37425479559315711797591813)
      ·
        refine ⟨7017277417371695962048465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37425479559315711797591813 7017277417371695962048465)
        ·
          refine ⟨5262958063028771971536349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7017277417371695962048465 5262958063028771971536349)
          ·
            refine ⟨1973609273635789489326131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5262958063028771971536349 1973609273635789489326131)
            ·
              refine ⟨2960413910453684233989197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973609273635789489326131 2960413910453684233989197)
              ·
                refine ⟨1110155216420131587745949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2960413910453684233989197 1110155216420131587745949)
                ·
                  refine ⟨416308206157549345404731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110155216420131587745949 416308206157549345404731)
                  ·
                    rfl

theorem cell21_1824204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_1824204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824204 prefixEnd_1824204 := by exact prefixLift 1824204
  have htrace : WordTrace (prefixWord ++ tailWord_1824204) baseStart_1824204 baseEnd_1824204 := by
    simpa [prefixWord, tailWord_1824204, baseEnd_1824204] using wordTrace_append hprefix tailTrace_1824204
  have hstable : (prefixWord ++ tailWord_1824204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824204).length < 2 ^ (prefixWord ++ tailWord_1824204).sum := by decide
  have hdescent : baseEnd_1824204 < baseStart_1824204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824243 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 8]
def baseStart_1824243 : Nat := 118140960795 + 1824243 * 2 ^ 59
def prefixEnd_1824243 : Nat := 4983230072969 + 3 ^ 40 * 1824243 * 2
def baseEnd_1824243 : Nat := 416317106488893944254651

theorem tailTrace_1824243 : CollatzResearch.WordTrace tailWord_1824243 prefixEnd_1824243 416317106488893944254651 := by
  unfold tailWord_1824243
  simp only [CollatzResearch.WordTrace]
  refine ⟨66535608330086641745277383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44357072220057761163518255 66535608330086641745277383)
  ·
    refine ⟨99803412495129962617916075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66535608330086641745277383 99803412495129962617916075)
    ·
      refine ⟨149705118742694943926874113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99803412495129962617916075 149705118742694943926874113)
      ·
        refine ⟨112278839057021207945155585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149705118742694943926874113 112278839057021207945155585)
        ·
          refine ⟨84209129292765905958866689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112278839057021207945155585 84209129292765905958866689)
          ·
            refine ⟨63156846969574429469150017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84209129292765905958866689 63156846969574429469150017)
            ·
              refine ⟨47367635227180822101862513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63156846969574429469150017 47367635227180822101862513)
              ·
                refine ⟨35525726420385616576396885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47367635227180822101862513 35525726420385616576396885)
                ·
                  refine ⟨416317106488893944254651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35525726420385616576396885 416317106488893944254651)
                  ·
                    rfl

theorem cell21_1824243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_1824243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824243 prefixEnd_1824243 := by exact prefixLift 1824243
  have htrace : WordTrace (prefixWord ++ tailWord_1824243) baseStart_1824243 baseEnd_1824243 := by
    simpa [prefixWord, tailWord_1824243, baseEnd_1824243] using wordTrace_append hprefix tailTrace_1824243
  have hstable : (prefixWord ++ tailWord_1824243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824243).length < 2 ^ (prefixWord ++ tailWord_1824243).sum := by decide
  have hdescent : baseEnd_1824243 < baseStart_1824243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824277 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 4]
def baseStart_1824277 : Nat := 118140960795 + 1824277 * 2 ^ 59
def prefixEnd_1824277 : Nat := 4983230072969 + 3 ^ 40 * 1824277 * 2
def baseEnd_1824277 : Nat := 416324865752117440687915

theorem tailTrace_1824277 : CollatzResearch.WordTrace tailWord_1824277 prefixEnd_1824277 416324865752117440687915 := by
  unfold tailWord_1824277
  simp only [CollatzResearch.WordTrace]
  refine ⟨66536848411963465552015085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44357898941308977034676723 66536848411963465552015085)
  ·
    refine ⟨24951318154486299582005657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66536848411963465552015085 24951318154486299582005657)
    ·
      refine ⟨18713488615864724686504243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24951318154486299582005657 18713488615864724686504243)
      ·
        refine ⟨28070232923797087029756365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18713488615864724686504243 28070232923797087029756365)
        ·
          refine ⟨10526337346423907636158637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28070232923797087029756365 10526337346423907636158637)
          ·
            refine ⟨3947376504908965363559489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10526337346423907636158637 3947376504908965363559489)
            ·
              refine ⟨2960532378681724022669617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3947376504908965363559489 2960532378681724022669617)
              ·
                refine ⟨2220399284011293017002213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2960532378681724022669617 2220399284011293017002213)
                ·
                  refine ⟨416324865752117440687915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2220399284011293017002213 416324865752117440687915)
                  ·
                    rfl

theorem cell21_1824277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_1824277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824277 prefixEnd_1824277 := by exact prefixLift 1824277
  have htrace : WordTrace (prefixWord ++ tailWord_1824277) baseStart_1824277 baseEnd_1824277 := by
    simpa [prefixWord, tailWord_1824277, baseEnd_1824277] using wordTrace_append hprefix tailTrace_1824277
  have hstable : (prefixWord ++ tailWord_1824277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824277).length < 2 ^ (prefixWord ++ tailWord_1824277).sum := by decide
  have hdescent : baseEnd_1824277 < baseStart_1824277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824353 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 4]
def baseStart_1824353 : Nat := 118140960795 + 1824353 * 2 ^ 59
def prefixEnd_1824353 : Nat := 4983230072969 + 3 ^ 40 * 1824353 * 2
def baseEnd_1824353 : Nat := 416342209987558197421093

theorem tailTrace_1824353 : CollatzResearch.WordTrace tailWord_1824353 prefixEnd_1824353 416342209987558197421093 := by
  unfold tailWord_1824353
  simp only [CollatzResearch.WordTrace]
  refine ⟨66539620359688130531781713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44359746906458753687854475 66539620359688130531781713)
  ·
    refine ⟨49904715269766097898836285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66539620359688130531781713 49904715269766097898836285)
    ·
      refine ⟨18714268226162286712063607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49904715269766097898836285 18714268226162286712063607)
      ·
        refine ⟨28071402339243430068095411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18714268226162286712063607 28071402339243430068095411)
        ·
          refine ⟨42107103508865145102143117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28071402339243430068095411 42107103508865145102143117)
          ·
            refine ⟨15790163815824429413303669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42107103508865145102143117 15790163815824429413303669)
            ·
              refine ⟨1480327857733540257497219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15790163815824429413303669 1480327857733540257497219)
              ·
                refine ⟨2220491786600310386245829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480327857733540257497219 2220491786600310386245829)
                ·
                  refine ⟨416342209987558197421093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2220491786600310386245829 416342209987558197421093)
                  ·
                    rfl

theorem cell21_1824353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 4].length) (baseStart_1824353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824353 prefixEnd_1824353 := by exact prefixLift 1824353
  have htrace : WordTrace (prefixWord ++ tailWord_1824353) baseStart_1824353 baseEnd_1824353 := by
    simpa [prefixWord, tailWord_1824353, baseEnd_1824353] using wordTrace_append hprefix tailTrace_1824353
  have hstable : (prefixWord ++ tailWord_1824353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824353).length < 2 ^ (prefixWord ++ tailWord_1824353).sum := by decide
  have hdescent : baseEnd_1824353 < baseStart_1824353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824395 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 6]
def baseStart_1824395 : Nat := 118140960795 + 1824395 * 2 ^ 59
def prefixEnd_1824395 : Nat := 4983230072969 + 3 ^ 40 * 1824395 * 2
def baseEnd_1824395 : Nat := 416351794959775457721007

theorem tailTrace_1824395 : CollatzResearch.WordTrace tailWord_1824395 prefixEnd_1824395 416351794959775457721007 := by
  unfold tailWord_1824395
  simp only [CollatzResearch.WordTrace]
  refine ⟨66541152225535971704810639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44360768150357314469873759 66541152225535971704810639)
  ·
    refine ⟨99811728338303957557215959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66541152225535971704810639 99811728338303957557215959)
    ·
      refine ⟨149717592507455936335823939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99811728338303957557215959 149717592507455936335823939)
      ·
        refine ⟨224576388761183904503735909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149717592507455936335823939 224576388761183904503735909)
        ·
          refine ⟨42108072892721982094450483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224576388761183904503735909 42108072892721982094450483)
          ·
            refine ⟨63162109339082973141675725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42108072892721982094450483 63162109339082973141675725)
            ·
              refine ⟨23685791002156114928128397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63162109339082973141675725 23685791002156114928128397)
              ·
                refine ⟨8882171625808543098048149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23685791002156114928128397 8882171625808543098048149)
                ·
                  refine ⟨416351794959775457721007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8882171625808543098048149 416351794959775457721007)
                  ·
                    rfl

theorem cell21_1824395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_1824395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824395 prefixEnd_1824395 := by exact prefixLift 1824395
  have htrace : WordTrace (prefixWord ++ tailWord_1824395) baseStart_1824395 baseEnd_1824395 := by
    simpa [prefixWord, tailWord_1824395, baseEnd_1824395] using wordTrace_append hprefix tailTrace_1824395
  have hstable : (prefixWord ++ tailWord_1824395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824395).length < 2 ^ (prefixWord ++ tailWord_1824395).sum := by decide
  have hdescent : baseEnd_1824395 < baseStart_1824395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824398 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1824398 : Nat := 118140960795 + 1824398 * 2 ^ 59
def prefixEnd_1824398 : Nat := 4983230072969 + 3 ^ 40 * 1824398 * 2
def baseEnd_1824398 : Nat := 416352479600648119171001

theorem tailTrace_1824398 : CollatzResearch.WordTrace tailWord_1824398 prefixEnd_1824398 416352479600648119171001 := by
  unfold tailWord_1824398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317657705565637902146231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44360841096350068811446565 8317657705565637902146231)
  ·
    refine ⟨12476486558348456853219347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8317657705565637902146231 12476486558348456853219347)
    ·
      refine ⟨18714729837522685279829021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12476486558348456853219347 18714729837522685279829021)
      ·
        refine ⟨7018023689071006979935883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18714729837522685279829021 7018023689071006979935883)
        ·
          refine ⟨10527035533606510469903825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018023689071006979935883 10527035533606510469903825)
          ·
            refine ⟨7895276650204882852427869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10527035533606510469903825 7895276650204882852427869)
            ·
              refine ⟨2960728743826831069660451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7895276650204882852427869 2960728743826831069660451)
              ·
                refine ⟨4441093115740246604490677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960728743826831069660451 4441093115740246604490677)
                ·
                  refine ⟨416352479600648119171001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4441093115740246604490677 416352479600648119171001)
                  ·
                    rfl

theorem cell21_1824398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1824398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824398 prefixEnd_1824398 := by exact prefixLift 1824398
  have htrace : WordTrace (prefixWord ++ tailWord_1824398) baseStart_1824398 baseEnd_1824398 := by
    simpa [prefixWord, tailWord_1824398, baseEnd_1824398] using wordTrace_append hprefix tailTrace_1824398
  have hstable : (prefixWord ++ tailWord_1824398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824398).length < 2 ^ (prefixWord ++ tailWord_1824398).sum := by decide
  have hdescent : baseEnd_1824398 < baseStart_1824398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824404 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 4]
def baseStart_1824404 : Nat := 118140960795 + 1824404 * 2 ^ 59
def prefixEnd_1824404 : Nat := 4983230072969 + 3 ^ 40 * 1824404 * 2
def baseEnd_1824404 : Nat := 416353848882393442070989

theorem tailTrace_1824404 : CollatzResearch.WordTrace tailWord_1824404 prefixEnd_1824404 416353848882393442070989 := by
  unfold tailWord_1824404
  simp only [CollatzResearch.WordTrace]
  refine ⟨33270740241251683120944133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44360986988335577494592177 33270740241251683120944133)
  ·
    refine ⟨6238263795234690585177025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33270740241251683120944133 6238263795234690585177025)
    ·
      refine ⟨4678697846426017938882769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6238263795234690585177025 4678697846426017938882769)
      ·
        refine ⟨3509023384819513454162077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4678697846426017938882769 3509023384819513454162077)
        ·
          refine ⟨1315883769307317545310779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3509023384819513454162077 1315883769307317545310779)
          ·
            refine ⟨1973825653960976317966169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315883769307317545310779 1973825653960976317966169)
            ·
              refine ⟨1480369240470732238474627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973825653960976317966169 1480369240470732238474627)
              ·
                refine ⟨2220553860706098357711941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480369240470732238474627 2220553860706098357711941)
                ·
                  refine ⟨416353848882393442070989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2220553860706098357711941 416353848882393442070989)
                  ·
                    rfl

theorem cell21_1824404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_1824404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824404 prefixEnd_1824404 := by exact prefixLift 1824404
  have htrace : WordTrace (prefixWord ++ tailWord_1824404) baseStart_1824404 baseEnd_1824404 := by
    simpa [prefixWord, tailWord_1824404, baseEnd_1824404] using wordTrace_append hprefix tailTrace_1824404
  have hstable : (prefixWord ++ tailWord_1824404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824404).length < 2 ^ (prefixWord ++ tailWord_1824404).sum := by decide
  have hdescent : baseEnd_1824404 < baseStart_1824404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824460 : List Nat := [2, 2, 1, 5, 2, 2, 1, 6]
def baseStart_1824460 : Nat := 118140960795 + 1824460 * 2 ^ 59
def prefixEnd_1824460 : Nat := 4983230072969 + 3 ^ 40 * 1824460 * 2
def baseEnd_1824460 : Nat := 138788876281783263045847

theorem tailTrace_1824460 : CollatzResearch.WordTrace tailWord_1824460 prefixEnd_1824460 138788876281783263045847 := by
  unfold tailWord_1824460
  simp only [CollatzResearch.WordTrace]
  refine ⟨33271761485150243902963417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44362348646866991870617889 33271761485150243902963417)
  ·
    refine ⟨24953821113862682927222563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33271761485150243902963417 24953821113862682927222563)
    ·
      refine ⟨37430731670794024390833845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24953821113862682927222563 37430731670794024390833845)
      ·
        refine ⟨3509131094136939786640673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37430731670794024390833845 3509131094136939786640673)
        ·
          refine ⟨2631848320602704839980505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3509131094136939786640673 2631848320602704839980505)
          ·
            refine ⟨1973886240452028629985379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631848320602704839980505 1973886240452028629985379)
            ·
              refine ⟨2960829360678042944978069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973886240452028629985379 2960829360678042944978069)
              ·
                refine ⟨138788876281783263045847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2960829360678042944978069 138788876281783263045847)
                ·
                  rfl

theorem cell21_1824460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_1824460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824460 prefixEnd_1824460 := by exact prefixLift 1824460
  have htrace : WordTrace (prefixWord ++ tailWord_1824460) baseStart_1824460 baseEnd_1824460 := by
    simpa [prefixWord, tailWord_1824460, baseEnd_1824460] using wordTrace_append hprefix tailTrace_1824460
  have hstable : (prefixWord ++ tailWord_1824460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824460).length < 2 ^ (prefixWord ++ tailWord_1824460).sum := by decide
  have hdescent : baseEnd_1824460 < baseStart_1824460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824477 : List Nat := [1, 4, 3, 3, 1, 1, 3, 5]
def baseStart_1824477 : Nat := 118140960795 + 1824477 * 2 ^ 59
def prefixEnd_1824477 : Nat := 4983230072969 + 3 ^ 40 * 1824477 * 2
def baseEnd_1824477 : Nat := 138790169492320512451391

theorem tailTrace_1824477 : CollatzResearch.WordTrace tailWord_1824477 prefixEnd_1824477 138790169492320512451391 := by
  unfold tailWord_1824477
  simp only [CollatzResearch.WordTrace]
  refine ⟨66544143011238899709295685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44362762007492599806197123 66544143011238899709295685)
  ·
    refine ⟨12477026814607293695492941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66544143011238899709295685 12477026814607293695492941)
    ·
      refine ⟨4678885055477735135809853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12477026814607293695492941 4678885055477735135809853)
      ·
        refine ⟨1754581895804150675928695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4678885055477735135809853 1754581895804150675928695)
        ·
          refine ⟨2631872843706226013893043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754581895804150675928695 2631872843706226013893043)
          ·
            refine ⟨3947809265559339020839565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631872843706226013893043 3947809265559339020839565)
            ·
              refine ⟨1480428474584752132814837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3947809265559339020839565 1480428474584752132814837)
              ·
                refine ⟨138790169492320512451391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1480428474584752132814837 138790169492320512451391)
                ·
                  rfl

theorem cell21_1824477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 5].length) (baseStart_1824477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824477 prefixEnd_1824477 := by exact prefixLift 1824477
  have htrace : WordTrace (prefixWord ++ tailWord_1824477) baseStart_1824477 baseEnd_1824477 := by
    simpa [prefixWord, tailWord_1824477, baseEnd_1824477] using wordTrace_append hprefix tailTrace_1824477
  have hstable : (prefixWord ++ tailWord_1824477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824477).length < 2 ^ (prefixWord ++ tailWord_1824477).sum := by decide
  have hdescent : baseEnd_1824477 < baseStart_1824477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824533 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 5]
def baseStart_1824533 : Nat := 118140960795 + 1824533 * 2 ^ 59
def prefixEnd_1824533 : Nat := 4983230072969 + 3 ^ 40 * 1824533 * 2
def baseEnd_1824533 : Nat := 416383288439917884420725

theorem tailTrace_1824533 : CollatzResearch.WordTrace tailWord_1824533 prefixEnd_1824533 416383288439917884420725 := by
  unfold tailWord_1824533
  simp only [CollatzResearch.WordTrace]
  refine ⟨66546185499036021273334253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44364123666024014182222835 66546185499036021273334253)
  ·
    refine ⟨24954819562138507977500345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66546185499036021273334253 24954819562138507977500345)
    ·
      refine ⟨18716114671603880983125259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24954819562138507977500345 18716114671603880983125259)
      ·
        refine ⟨28074172007405821474687889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18716114671603880983125259 28074172007405821474687889)
        ·
          refine ⟨21055629005554366106015917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28074172007405821474687889 21055629005554366106015917)
          ·
            refine ⟨7895860877082887289755969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21055629005554366106015917 7895860877082887289755969)
            ·
              refine ⟨5921895657812165467316977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7895860877082887289755969 5921895657812165467316977)
              ·
                refine ⟨4441421743359124100487733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5921895657812165467316977 4441421743359124100487733)
                ·
                  refine ⟨416383288439917884420725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4441421743359124100487733 416383288439917884420725)
                  ·
                    rfl

theorem cell21_1824533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_1824533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824533 prefixEnd_1824533 := by exact prefixLift 1824533
  have htrace : WordTrace (prefixWord ++ tailWord_1824533) baseStart_1824533 baseEnd_1824533 := by
    simpa [prefixWord, tailWord_1824533, baseEnd_1824533] using wordTrace_append hprefix tailTrace_1824533
  have hstable : (prefixWord ++ tailWord_1824533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824533).length < 2 ^ (prefixWord ++ tailWord_1824533).sum := by decide
  have hdescent : baseEnd_1824533 < baseStart_1824533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824542 : List Nat := [4, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1824542 : Nat := 118140960795 + 1824542 * 2 ^ 59
def prefixEnd_1824542 : Nat := 4983230072969 + 3 ^ 40 * 1824542 * 2
def baseEnd_1824542 : Nat := 416385342362535868770707

theorem tailTrace_1824542 : CollatzResearch.WordTrace tailWord_1824542 prefixEnd_1824542 416385342362535868770707 := by
  unfold tailWord_1824542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8318314219500426976301485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44364342504002277206941253 8318314219500426976301485)
  ·
    refine ⟨3119367832312660116113057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8318314219500426976301485 3119367832312660116113057)
    ·
      refine ⟨2339525874234495087084793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3119367832312660116113057 2339525874234495087084793)
      ·
        refine ⟨1754644405675871315313595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2339525874234495087084793 1754644405675871315313595)
        ·
          refine ⟨2631966608513806972970393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754644405675871315313595 2631966608513806972970393)
          ·
            refine ⟨1973974956385355229727795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631966608513806972970393 1973974956385355229727795)
            ·
              refine ⟨2960962434578032844591693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973974956385355229727795 2960962434578032844591693)
              ·
                refine ⟨1110360912966762316721885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2960962434578032844591693 1110360912966762316721885)
                ·
                  refine ⟨416385342362535868770707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110360912966762316721885 416385342362535868770707)
                  ·
                    rfl

theorem cell21_1824542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1824542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824542 prefixEnd_1824542 := by exact prefixLift 1824542
  have htrace : WordTrace (prefixWord ++ tailWord_1824542) baseStart_1824542 baseEnd_1824542 := by
    simpa [prefixWord, tailWord_1824542, baseEnd_1824542] using wordTrace_append hprefix tailTrace_1824542
  have hstable : (prefixWord ++ tailWord_1824542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824542).length < 2 ^ (prefixWord ++ tailWord_1824542).sum := by decide
  have hdescent : baseEnd_1824542 < baseStart_1824542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824547 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 6]
def baseStart_1824547 : Nat := 118140960795 + 1824547 * 2 ^ 59
def prefixEnd_1824547 : Nat := 4983230072969 + 3 ^ 40 * 1824547 * 2
def baseEnd_1824547 : Nat := 416386483430656971187363

theorem tailTrace_1824547 : CollatzResearch.WordTrace tailWord_1824547 prefixEnd_1824547 416386483430656971187363 := by
  unfold tailWord_1824547
  simp only [CollatzResearch.WordTrace]
  refine ⟨66546696120985301664343895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44364464080656867776229263 66546696120985301664343895)
  ·
    refine ⟨99820044181477952496515843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66546696120985301664343895 99820044181477952496515843)
    ·
      refine ⟨149730066272216928744773765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99820044181477952496515843 149730066272216928744773765)
      ·
        refine ⟨28074387426040674139645081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149730066272216928744773765 28074387426040674139645081)
        ·
          refine ⟨21055790569530505604733811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28074387426040674139645081 21055790569530505604733811)
          ·
            refine ⟨31583685854295758407100717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21055790569530505604733811 31583685854295758407100717)
            ·
              refine ⟨11843882195360909402662769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31583685854295758407100717 11843882195360909402662769)
              ·
                refine ⟨8882911646520682051997077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11843882195360909402662769 8882911646520682051997077)
                ·
                  refine ⟨416386483430656971187363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8882911646520682051997077 416386483430656971187363)
                  ·
                    rfl

theorem cell21_1824547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_1824547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824547 prefixEnd_1824547 := by exact prefixLift 1824547
  have htrace : WordTrace (prefixWord ++ tailWord_1824547) baseStart_1824547 baseEnd_1824547 := by
    simpa [prefixWord, tailWord_1824547, baseEnd_1824547] using wordTrace_append hprefix tailTrace_1824547
  have hstable : (prefixWord ++ tailWord_1824547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824547).length < 2 ^ (prefixWord ++ tailWord_1824547).sum := by decide
  have hdescent : baseEnd_1824547 < baseStart_1824547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824592 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_1824592 : Nat := 118140960795 + 1824592 * 2 ^ 59
def prefixEnd_1824592 : Nat := 4983230072969 + 3 ^ 40 * 1824592 * 2
def baseEnd_1824592 : Nat := 416396753043746892937271

theorem tailTrace_1824592 : CollatzResearch.WordTrace tailWord_1824592 prefixEnd_1824592 416396753043746892937271 := by
  unfold tailWord_1824592
  simp only [CollatzResearch.WordTrace]
  refine ⟨33274168702911137174866015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44365558270548182899821353 33274168702911137174866015)
  ·
    refine ⟨49911253054366705762299023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33274168702911137174866015 49911253054366705762299023)
    ·
      refine ⟨74866879581550058643448535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49911253054366705762299023 74866879581550058643448535)
      ·
        refine ⟨112300319372325087965172803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74866879581550058643448535 112300319372325087965172803)
        ·
          refine ⟨168450479058487631947759205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112300319372325087965172803 168450479058487631947759205)
          ·
            refine ⟨31584464823466430990204851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168450479058487631947759205 31584464823466430990204851)
            ·
              refine ⟨47376697235199646485307277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31584464823466430990204851 47376697235199646485307277)
              ·
                refine ⟨17766261463199867431990229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47376697235199646485307277 17766261463199867431990229)
                ·
                  refine ⟨416396753043746892937271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17766261463199867431990229 416396753043746892937271)
                  ·
                    rfl

theorem cell21_1824592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_1824592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824592 prefixEnd_1824592 := by exact prefixLift 1824592
  have htrace : WordTrace (prefixWord ++ tailWord_1824592) baseStart_1824592 baseEnd_1824592 := by
    simpa [prefixWord, tailWord_1824592, baseEnd_1824592] using wordTrace_append hprefix tailTrace_1824592
  have hstable : (prefixWord ++ tailWord_1824592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824592).length < 2 ^ (prefixWord ++ tailWord_1824592).sum := by decide
  have hdescent : baseEnd_1824592 < baseStart_1824592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824618 : List Nat := [3, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_1824618 : Nat := 118140960795 + 1824618 * 2 ^ 59
def prefixEnd_1824618 : Nat := 4983230072969 + 3 ^ 40 * 1824618 * 2
def baseEnd_1824618 : Nat := 416402686597976625503885

theorem tailTrace_1824618 : CollatzResearch.WordTrace tailWord_1824618 prefixEnd_1824618 416402686597976625503885 := by
  unfold tailWord_1824618
  simp only [CollatzResearch.WordTrace]
  refine ⟨16637321425932020197544627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44366190469152053860119005 16637321425932020197544627)
  ·
    refine ⟨24955982138898030296316941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16637321425932020197544627 24955982138898030296316941)
    ·
      refine ⟨9358493302086761361118853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24955982138898030296316941 9358493302086761361118853)
      ·
        refine ⟨1754717494141267755209785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9358493302086761361118853 1754717494141267755209785)
        ·
          refine ⟨1316038120605950816407339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1754717494141267755209785 1316038120605950816407339)
          ·
            refine ⟨1974057180908926224611009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1316038120605950816407339 1974057180908926224611009)
            ·
              refine ⟨1480542885681694668458257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974057180908926224611009 1480542885681694668458257)
              ·
                refine ⟨1110407164261271001343693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480542885681694668458257 1110407164261271001343693)
                ·
                  refine ⟨416402686597976625503885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110407164261271001343693 416402686597976625503885)
                  ·
                    rfl

theorem cell21_1824618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_1824618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824618 prefixEnd_1824618 := by exact prefixLift 1824618
  have htrace : WordTrace (prefixWord ++ tailWord_1824618) baseStart_1824618 baseEnd_1824618 := by
    simpa [prefixWord, tailWord_1824618, baseEnd_1824618] using wordTrace_append hprefix tailTrace_1824618
  have hstable : (prefixWord ++ tailWord_1824618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824618).length < 2 ^ (prefixWord ++ tailWord_1824618).sum := by decide
  have hdescent : baseEnd_1824618 < baseStart_1824618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824674 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1824674 : Nat := 118140960795 + 1824674 * 2 ^ 59
def prefixEnd_1824674 : Nat := 4983230072969 + 3 ^ 40 * 1824674 * 2
def baseEnd_1824674 : Nat := 416415466560932972570437

theorem tailTrace_1824674 : CollatzResearch.WordTrace tailWord_1824674 prefixEnd_1824674 416415466560932972570437 := by
  unfold tailWord_1824674
  simp only [CollatzResearch.WordTrace]
  refine ⟨16637832047881300588554269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44367552127683468236144717 16637832047881300588554269)
  ·
    refine ⟨6239187017955487720707851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16637832047881300588554269 6239187017955487720707851)
    ·
      refine ⟨9358780526933231581061777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6239187017955487720707851 9358780526933231581061777)
      ·
        refine ⟨7019085395199923685796333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9358780526933231581061777 7019085395199923685796333)
        ·
          refine ⟨2632157023199971382173625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7019085395199923685796333 2632157023199971382173625)
          ·
            refine ⟨1974117767399978536630219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632157023199971382173625 1974117767399978536630219)
            ·
              refine ⟨2961176651099967804945329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1974117767399978536630219 2961176651099967804945329)
              ·
                refine ⟨2220882488324975853708997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961176651099967804945329 2220882488324975853708997)
                ·
                  refine ⟨416415466560932972570437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2220882488324975853708997 416415466560932972570437)
                  ·
                    rfl

theorem cell21_1824674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1824674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824674 prefixEnd_1824674 := by exact prefixLift 1824674
  have htrace : WordTrace (prefixWord ++ tailWord_1824674) baseStart_1824674 baseEnd_1824674 := by
    simpa [prefixWord, tailWord_1824674, baseEnd_1824674] using wordTrace_append hprefix tailTrace_1824674
  have hstable : (prefixWord ++ tailWord_1824674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824674).length < 2 ^ (prefixWord ++ tailWord_1824674).sum := by decide
  have hdescent : baseEnd_1824674 < baseStart_1824674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824713 : List Nat := [1, 2, 1, 1, 2, 1, 2, 11]
def baseStart_1824713 : Nat := 118140960795 + 1824713 * 2 ^ 59
def prefixEnd_1824713 : Nat := 4983230072969 + 3 ^ 40 * 1824713 * 2
def baseEnd_1824713 : Nat := 138808122297425857140119

theorem tailTrace_1824713 : CollatzResearch.WordTrace tailWord_1824713 prefixEnd_1824713 138808122297425857140119 := by
  unfold tailWord_1824713
  simp only [CollatzResearch.WordTrace]
  refine ⟨66552750638383912014886793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44368500425589274676591195 66552750638383912014886793)
  ·
    refine ⟨49914562978787934011165095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66552750638383912014886793 49914562978787934011165095)
    ·
      refine ⟨74871844468181901016747643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49914562978787934011165095 74871844468181901016747643)
      ·
        refine ⟨112307766702272851525121465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74871844468181901016747643 112307766702272851525121465)
        ·
          refine ⟨84230825026704638643841099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112307766702272851525121465 84230825026704638643841099)
          ·
            refine ⟨126346237540056957965761649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84230825026704638643841099 126346237540056957965761649)
            ·
              refine ⟨94759678155042718474321237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126346237540056957965761649 94759678155042718474321237)
              ·
                refine ⟨138808122297425857140119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 94759678155042718474321237 138808122297425857140119)
                ·
                  rfl

theorem cell21_1824713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 11].length) (baseStart_1824713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824713 prefixEnd_1824713 := by exact prefixLift 1824713
  have htrace : WordTrace (prefixWord ++ tailWord_1824713) baseStart_1824713 baseEnd_1824713 := by
    simpa [prefixWord, tailWord_1824713, baseEnd_1824713] using wordTrace_append hprefix tailTrace_1824713
  have hstable : (prefixWord ++ tailWord_1824713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824713).length < 2 ^ (prefixWord ++ tailWord_1824713).sum := by decide
  have hdescent : baseEnd_1824713 < baseStart_1824713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824750 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1824750 : Nat := 118140960795 + 1824750 * 2 ^ 59
def prefixEnd_1824750 : Nat := 4983230072969 + 3 ^ 40 * 1824750 * 2
def baseEnd_1824750 : Nat := 416432810796373729303615

theorem tailTrace_1824750 : CollatzResearch.WordTrace tailWord_1824750 prefixEnd_1824750 416432810796373729303615 := by
  unfold tailWord_1824750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8319262517406233416747963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44369400092833244889322469 8319262517406233416747963)
  ·
    refine ⟨12478893776109350125121945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8319262517406233416747963 12478893776109350125121945)
    ·
      refine ⟨9359170332082012593841459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12478893776109350125121945 9359170332082012593841459)
      ·
        refine ⟨14038755498123018890762189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359170332082012593841459 14038755498123018890762189)
        ·
          refine ⟨5264533311796132084035821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14038755498123018890762189 5264533311796132084035821)
          ·
            refine ⟨1974199991923549531513433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5264533311796132084035821 1974199991923549531513433)
            ·
              refine ⟨1480649993942662148635075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974199991923549531513433 1480649993942662148635075)
              ·
                refine ⟨2220974990913993222952613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480649993942662148635075 2220974990913993222952613)
                ·
                  refine ⟨416432810796373729303615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2220974990913993222952613 416432810796373729303615)
                  ·
                    rfl

theorem cell21_1824750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1824750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824750 prefixEnd_1824750 := by exact prefixLift 1824750
  have htrace : WordTrace (prefixWord ++ tailWord_1824750) baseStart_1824750 baseEnd_1824750 := by
    simpa [prefixWord, tailWord_1824750, baseEnd_1824750] using wordTrace_append hprefix tailTrace_1824750
  have hstable : (prefixWord ++ tailWord_1824750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824750).length < 2 ^ (prefixWord ++ tailWord_1824750).sum := by decide
  have hdescent : baseEnd_1824750 < baseStart_1824750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824781 : List Nat := [1, 7, 1, 2, 2, 8]
def baseStart_1824781 : Nat := 118140960795 + 1824781 * 2 ^ 59
def prefixEnd_1824781 : Nat := 4983230072969 + 3 ^ 40 * 1824781 * 2
def baseEnd_1824781 : Nat := 15423699459952761640255

theorem tailTrace_1824781 : CollatzResearch.WordTrace tailWord_1824781 prefixEnd_1824781 15423699459952761640255 := by
  unfold tailWord_1824781
  simp only [CollatzResearch.WordTrace]
  refine ⟨66555230802137559628362197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44370153868091706418908131 66555230802137559628362197)
  ·
    refine ⟨1559888221925099053789739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 66555230802137559628362197 1559888221925099053789739)
    ·
      refine ⟨2339832332887648580684609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559888221925099053789739 2339832332887648580684609)
      ·
        refine ⟨1754874249665736435513457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2339832332887648580684609 1754874249665736435513457)
        ·
          refine ⟨1316155687249302326635093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1754874249665736435513457 1316155687249302326635093)
          ·
            refine ⟨15423699459952761640255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1316155687249302326635093 15423699459952761640255)
            ·
              rfl

theorem cell21_1824781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 8].length) (baseStart_1824781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824781 prefixEnd_1824781 := by exact prefixLift 1824781
  have htrace : WordTrace (prefixWord ++ tailWord_1824781) baseStart_1824781 baseEnd_1824781 := by
    simpa [prefixWord, tailWord_1824781, baseEnd_1824781] using wordTrace_append hprefix tailTrace_1824781
  have hstable : (prefixWord ++ tailWord_1824781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824781).length < 2 ^ (prefixWord ++ tailWord_1824781).sum := by decide
  have hdescent : baseEnd_1824781 < baseStart_1824781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824789 : List Nat := [1, 3, 2, 1, 14]
def baseStart_1824789 : Nat := 118140960795 + 1824789 * 2 ^ 59
def prefixEnd_1824789 : Nat := 4983230072969 + 3 ^ 40 * 1824789 * 2
def baseEnd_1824789 : Nat := 5141255692934794174735

theorem tailTrace_1824789 : CollatzResearch.WordTrace tailWord_1824789 prefixEnd_1824789 5141255692934794174735 := by
  unfold tailWord_1824789
  simp only [CollatzResearch.WordTrace]
  refine ⟨66555522586108576994653421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44370348390739051329768947 66555522586108576994653421)
  ·
    refine ⟨24958320969790716372995033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66555522586108576994653421 24958320969790716372995033)
    ·
      refine ⟨18718740727343037279746275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24958320969790716372995033 18718740727343037279746275)
      ·
        refine ⟨28078111091014555919619413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18718740727343037279746275 28078111091014555919619413)
        ·
          refine ⟨5141255692934794174735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 28078111091014555919619413 5141255692934794174735)
          ·
            rfl

theorem cell21_1824789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 14].length) (baseStart_1824789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824789 prefixEnd_1824789 := by exact prefixLift 1824789
  have htrace : WordTrace (prefixWord ++ tailWord_1824789) baseStart_1824789 baseEnd_1824789 := by
    simpa [prefixWord, tailWord_1824789, baseEnd_1824789] using wordTrace_append hprefix tailTrace_1824789
  have hstable : (prefixWord ++ tailWord_1824789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824789).length < 2 ^ (prefixWord ++ tailWord_1824789).sum := by decide
  have hdescent : baseEnd_1824789 < baseStart_1824789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824792 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_1824792 : Nat := 118140960795 + 1824792 * 2 ^ 59
def prefixEnd_1824792 : Nat := 4983230072969 + 3 ^ 40 * 1824792 * 2
def baseEnd_1824792 : Nat := 416442395768590989603529

theorem tailTrace_1824792 : CollatzResearch.WordTrace tailWord_1824792 prefixEnd_1824792 416442395768590989603529 := by
  unfold tailWord_1824792
  simp only [CollatzResearch.WordTrace]
  refine ⟨33277816002548854253506315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44370421336731805671341753 33277816002548854253506315)
  ·
    refine ⟨49916724003823281380259473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33277816002548854253506315 49916724003823281380259473)
    ·
      refine ⟨37437543002867461035194605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49916724003823281380259473 37437543002867461035194605)
      ·
        refine ⟨14039078626075297888197977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37437543002867461035194605 14039078626075297888197977)
        ·
          refine ⟨10529308969556473416148483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14039078626075297888197977 10529308969556473416148483)
          ·
            refine ⟨15793963454334710124222725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10529308969556473416148483 15793963454334710124222725)
            ·
              refine ⟨2961368147687758148291761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15793963454334710124222725 2961368147687758148291761)
              ·
                refine ⟨2221026110765818611218821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961368147687758148291761 2221026110765818611218821)
                ·
                  refine ⟨416442395768590989603529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221026110765818611218821 416442395768590989603529)
                  ·
                    rfl

theorem cell21_1824792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_1824792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824792 prefixEnd_1824792 := by exact prefixLift 1824792
  have htrace : WordTrace (prefixWord ++ tailWord_1824792) baseStart_1824792 baseEnd_1824792 := by
    simpa [prefixWord, tailWord_1824792, baseEnd_1824792] using wordTrace_append hprefix tailTrace_1824792
  have hstable : (prefixWord ++ tailWord_1824792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824792).length < 2 ^ (prefixWord ++ tailWord_1824792).sum := by decide
  have hdescent : baseEnd_1824792 < baseStart_1824792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824865 : List Nat := [1, 2, 3, 1, 1, 2, 1, 10]
def baseStart_1824865 : Nat := 118140960795 + 1824865 * 2 ^ 59
def prefixEnd_1824865 : Nat := 4983230072969 + 3 ^ 40 * 1824865 * 2
def baseEnd_1824865 : Nat := 138819685121053028295571

theorem tailTrace_1824865 : CollatzResearch.WordTrace tailWord_1824865 prefixEnd_1824865 138819685121053028295571 := by
  unfold tailWord_1824865
  simp only [CollatzResearch.WordTrace]
  refine ⟨66558294533833241974420049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44372196355888827982946699 66558294533833241974420049)
  ·
    refine ⟨49918720900374931480815037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66558294533833241974420049 49918720900374931480815037)
    ·
      refine ⟨18719520337640599305305639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49918720900374931480815037 18719520337640599305305639)
      ·
        refine ⟨28079280506460898957958459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18719520337640599305305639 28079280506460898957958459)
        ·
          refine ⟨42118920759691348436937689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28079280506460898957958459 42118920759691348436937689)
          ·
            refine ⟨31589190569768511327703267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42118920759691348436937689 31589190569768511327703267)
            ·
              refine ⟨47383785854652766991554901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31589190569768511327703267 47383785854652766991554901)
              ·
                refine ⟨138819685121053028295571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47383785854652766991554901 138819685121053028295571)
                ·
                  rfl

theorem cell21_1824865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 10].length) (baseStart_1824865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824865 prefixEnd_1824865 := by exact prefixLift 1824865
  have htrace : WordTrace (prefixWord ++ tailWord_1824865) baseStart_1824865 baseEnd_1824865 := by
    simpa [prefixWord, tailWord_1824865, baseEnd_1824865] using wordTrace_append hprefix tailTrace_1824865
  have hstable : (prefixWord ++ tailWord_1824865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824865).length < 2 ^ (prefixWord ++ tailWord_1824865).sum := by decide
  have hdescent : baseEnd_1824865 < baseStart_1824865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824882 : List Nat := [3, 2, 1, 2, 2, 3, 1, 7]
def baseStart_1824882 : Nat := 118140960795 + 1824882 * 2 ^ 59
def prefixEnd_1824882 : Nat := 4983230072969 + 3 ^ 40 * 1824882 * 2
def baseEnd_1824882 : Nat := 138820978331590277701115

theorem tailTrace_1824882 : CollatzResearch.WordTrace tailWord_1824882 prefixEnd_1824882 138820978331590277701115 := by
  unfold tailWord_1824882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16639728643692913469447225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44372609716514435918525933 16639728643692913469447225)
  ·
    refine ⟨12479796482769685102085419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16639728643692913469447225 12479796482769685102085419)
    ·
      refine ⟨18719694724154527653128129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12479796482769685102085419 18719694724154527653128129)
      ·
        refine ⟨14039771043115895739846097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18719694724154527653128129 14039771043115895739846097)
        ·
          refine ⟨10529828282336921804884573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14039771043115895739846097 10529828282336921804884573)
          ·
            refine ⟨3948685605876345676831715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10529828282336921804884573 3948685605876345676831715)
            ·
              refine ⟨5923028408814518515247573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948685605876345676831715 5923028408814518515247573)
              ·
                refine ⟨138820978331590277701115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5923028408814518515247573 138820978331590277701115)
                ·
                  rfl

theorem cell21_1824882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_1824882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824882 prefixEnd_1824882 := by exact prefixLift 1824882
  have htrace : WordTrace (prefixWord ++ tailWord_1824882) baseStart_1824882 baseEnd_1824882 := by
    simpa [prefixWord, tailWord_1824882, baseEnd_1824882] using wordTrace_append hprefix tailTrace_1824882
  have hstable : (prefixWord ++ tailWord_1824882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824882).length < 2 ^ (prefixWord ++ tailWord_1824882).sum := by decide
  have hdescent : baseEnd_1824882 < baseStart_1824882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824916 : List Nat := [2, 4, 2, 3, 1, 1, 2, 6]
def baseStart_1824916 : Nat := 118140960795 + 1824916 * 2 ^ 59
def prefixEnd_1824916 : Nat := 4983230072969 + 3 ^ 40 * 1824916 * 2
def baseEnd_1824916 : Nat := 138823564752664776512203

theorem tailTrace_1824916 : CollatzResearch.WordTrace tailWord_1824916 prefixEnd_1824916 138823564752664776512203 := by
  unfold tailWord_1824916
  simp only [CollatzResearch.WordTrace]
  refine ⟨33280077328324238842263301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44373436437765651789684401 33280077328324238842263301)
  ·
    refine ⟨6240014499060794782924369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33280077328324238842263301 6240014499060794782924369)
    ·
      refine ⟨4680010874295596087193277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6240014499060794782924369 4680010874295596087193277)
      ·
        refine ⟨1755004077860848532697479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4680010874295596087193277 1755004077860848532697479)
        ·
          refine ⟨2632506116791272799046219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755004077860848532697479 2632506116791272799046219)
          ·
            refine ⟨3948759175186909198569329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632506116791272799046219 3948759175186909198569329)
            ·
              refine ⟨2961569381390181898926997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3948759175186909198569329 2961569381390181898926997)
              ·
                refine ⟨138823564752664776512203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2961569381390181898926997 138823564752664776512203)
                ·
                  rfl

theorem cell21_1824916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_1824916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824916 prefixEnd_1824916 := by exact prefixLift 1824916
  have htrace : WordTrace (prefixWord ++ tailWord_1824916) baseStart_1824916 baseEnd_1824916 := by
    simpa [prefixWord, tailWord_1824916, baseEnd_1824916] using wordTrace_append hprefix tailTrace_1824916
  have hstable : (prefixWord ++ tailWord_1824916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824916).length < 2 ^ (prefixWord ++ tailWord_1824916).sum := by decide
  have hdescent : baseEnd_1824916 < baseStart_1824916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824958 : List Nat := [4, 2, 1, 1, 4, 9]
def baseStart_1824958 : Nat := 118140960795 + 1824958 * 2 ^ 59
def prefixEnd_1824958 : Nat := 4983230072969 + 3 ^ 40 * 1824958 * 2
def baseEnd_1824958 : Nat := 15425195527044873697649

theorem tailTrace_1824958 : CollatzResearch.WordTrace tailWord_1824958 prefixEnd_1824958 15425195527044873697649 := by
  unfold tailWord_1824958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8320210815312039857194441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44374457681664212571703685 8320210815312039857194441)
  ·
    refine ⟨6240158111484029892895831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8320210815312039857194441 6240158111484029892895831)
    ·
      refine ⟨9360237167226044839343747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240158111484029892895831 9360237167226044839343747)
      ·
        refine ⟨14040355750839067259015621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9360237167226044839343747 14040355750839067259015621)
        ·
          refine ⟨2632566703282325111065429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14040355750839067259015621 2632566703282325111065429)
          ·
            refine ⟨15425195527044873697649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2632566703282325111065429 15425195527044873697649)
            ·
              rfl

theorem cell21_1824958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 9].length) (baseStart_1824958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824958 prefixEnd_1824958 := by exact prefixLift 1824958
  have htrace : WordTrace (prefixWord ++ tailWord_1824958) baseStart_1824958 baseEnd_1824958 := by
    simpa [prefixWord, tailWord_1824958, baseEnd_1824958] using wordTrace_append hprefix tailTrace_1824958
  have hstable : (prefixWord ++ tailWord_1824958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824958).length < 2 ^ (prefixWord ++ tailWord_1824958).sum := by decide
  have hdescent : baseEnd_1824958 < baseStart_1824958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824964 : List Nat := [2, 3, 3, 1, 2, 3, 2, 2, 3]
def baseStart_1824964 : Nat := 118140960795 + 1824964 * 2 ^ 59
def prefixEnd_1824964 : Nat := 4983230072969 + 3 ^ 40 * 1824964 * 2
def baseEnd_1824964 : Nat := 416481648511956912736511

theorem tailTrace_1824964 : CollatzResearch.WordTrace tailWord_1824964 prefixEnd_1824964 416481648511956912736511 := by
  unfold tailWord_1824964
  simp only [CollatzResearch.WordTrace]
  refine ⟨33280952680237290941136973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44374603573649721254849297 33280952680237290941136973)
  ·
    refine ⟨12480357255088984102926365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33280952680237290941136973 12480357255088984102926365)
    ·
      refine ⟨4680133970658369038597387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12480357255088984102926365 4680133970658369038597387)
      ·
        refine ⟨7020200955987553557896081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680133970658369038597387 7020200955987553557896081)
        ·
          refine ⟨5265150716990665168422061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7020200955987553557896081 5265150716990665168422061)
          ·
            refine ⟨1974431518871499438158273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5265150716990665168422061 1974431518871499438158273)
            ·
              refine ⟨1480823639153624578618705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974431518871499438158273 1480823639153624578618705)
              ·
                refine ⟨1110617729365218433964029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480823639153624578618705 1110617729365218433964029)
                ·
                  refine ⟨416481648511956912736511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110617729365218433964029 416481648511956912736511)
                  ·
                    rfl

theorem cell21_1824964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_1824964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824964 prefixEnd_1824964 := by exact prefixLift 1824964
  have htrace : WordTrace (prefixWord ++ tailWord_1824964) baseStart_1824964 baseEnd_1824964 := by
    simpa [prefixWord, tailWord_1824964, baseEnd_1824964] using wordTrace_append hprefix tailTrace_1824964
  have hstable : (prefixWord ++ tailWord_1824964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824964).length < 2 ^ (prefixWord ++ tailWord_1824964).sum := by decide
  have hdescent : baseEnd_1824964 < baseStart_1824964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1824989 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1824989 : Nat := 118140960795 + 1824989 * 2 ^ 59
def prefixEnd_1824989 : Nat := 4983230072969 + 3 ^ 40 * 1824989 * 2
def baseEnd_1824989 : Nat := 416487353852562424819793

theorem tailTrace_1824989 : CollatzResearch.WordTrace tailWord_1824989 prefixEnd_1824989 416487353852562424819793 := by
  unfold tailWord_1824989
  simp only [CollatzResearch.WordTrace]
  refine ⟨66562817185384011151934021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44375211456922674101289347 66562817185384011151934021)
  ·
    refine ⟨12480528222259502090987629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66562817185384011151934021 12480528222259502090987629)
    ·
      refine ⟨4680198083347313284120361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12480528222259502090987629 4680198083347313284120361)
      ·
        refine ⟨3510148562510484963090271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4680198083347313284120361 3510148562510484963090271)
        ·
          refine ⟨5265222843765727444635407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3510148562510484963090271 5265222843765727444635407)
          ·
            refine ⟨7897834265648591166953111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265222843765727444635407 7897834265648591166953111)
            ·
              refine ⟨11846751398472886750429667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897834265648591166953111 11846751398472886750429667)
              ·
                refine ⟨17770127097709330125644501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11846751398472886750429667 17770127097709330125644501)
                ·
                  refine ⟨416487353852562424819793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17770127097709330125644501 416487353852562424819793)
                  ·
                    rfl

theorem cell21_1824989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1824989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1824989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1824989 prefixEnd_1824989 := by exact prefixLift 1824989
  have htrace : WordTrace (prefixWord ++ tailWord_1824989) baseStart_1824989 baseEnd_1824989 := by
    simpa [prefixWord, tailWord_1824989, baseEnd_1824989] using wordTrace_append hprefix tailTrace_1824989
  have hstable : (prefixWord ++ tailWord_1824989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1824989).length < 2 ^ (prefixWord ++ tailWord_1824989).sum := by decide
  have hdescent : baseEnd_1824989 < baseStart_1824989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1824989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825020 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_1825020 : Nat := 118140960795 + 1825020 * 2 ^ 59
def prefixEnd_1825020 : Nat := 4983230072969 + 3 ^ 40 * 1825020 * 2
def baseEnd_1825020 : Nat := 416494428474913259803063

theorem tailTrace_1825020 : CollatzResearch.WordTrace tailWord_1825020 prefixEnd_1825020 416494428474913259803063 := by
  unfold tailWord_1825020
  simp only [CollatzResearch.WordTrace]
  refine ⟨33281973924135851723156257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44375965232181135630875009 33281973924135851723156257)
  ·
    refine ⟨24961480443101888792367193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33281973924135851723156257 24961480443101888792367193)
    ·
      refine ⟨18721110332326416594275395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24961480443101888792367193 18721110332326416594275395)
      ·
        refine ⟨28081665498489624891413093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18721110332326416594275395 28081665498489624891413093)
        ·
          refine ⟨5265312280966804667139955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28081665498489624891413093 5265312280966804667139955)
          ·
            refine ⟨7897968421450207000709933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265312280966804667139955 7897968421450207000709933)
            ·
              refine ⟨2961738158043827625266225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7897968421450207000709933 2961738158043827625266225)
              ·
                refine ⟨2221303618532870718949669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2961738158043827625266225 2221303618532870718949669)
                ·
                  refine ⟨416494428474913259803063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221303618532870718949669 416494428474913259803063)
                  ·
                    rfl

theorem cell21_1825020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_1825020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825020 prefixEnd_1825020 := by exact prefixLift 1825020
  have htrace : WordTrace (prefixWord ++ tailWord_1825020) baseStart_1825020 baseEnd_1825020 := by
    simpa [prefixWord, tailWord_1825020, baseEnd_1825020] using wordTrace_append hprefix tailTrace_1825020
  have hstable : (prefixWord ++ tailWord_1825020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825020).length < 2 ^ (prefixWord ++ tailWord_1825020).sum := by decide
  have hdescent : baseEnd_1825020 < baseStart_1825020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825048 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_1825048 : Nat := 118140960795 + 1825048 * 2 ^ 59
def prefixEnd_1825048 : Nat := 4983230072969 + 3 ^ 40 * 1825048 * 2
def baseEnd_1825048 : Nat := 416500818456391433336339

theorem tailTrace_1825048 : CollatzResearch.WordTrace tailWord_1825048 prefixEnd_1825048 416500818456391433336339 := by
  unfold tailWord_1825048
  simp only [CollatzResearch.WordTrace]
  refine ⟨33282484546085132114165899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44376646061446842818887865 33282484546085132114165899)
  ·
    refine ⟨49923726819127698171248849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33282484546085132114165899 49923726819127698171248849)
    ·
      refine ⟨37442795114345773628436637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49923726819127698171248849 37442795114345773628436637)
      ·
        refine ⟨14041048167879665110663739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37442795114345773628436637 14041048167879665110663739)
        ·
          refine ⟨21061572251819497665995609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14041048167879665110663739 21061572251819497665995609)
          ·
            refine ⟨15796179188864623249496707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21061572251819497665995609 15796179188864623249496707)
            ·
              refine ⟨23694268783296934874245061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15796179188864623249496707 23694268783296934874245061)
              ·
                refine ⟨4442675396868175288920949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23694268783296934874245061 4442675396868175288920949)
                ·
                  refine ⟨416500818456391433336339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4442675396868175288920949 416500818456391433336339)
                  ·
                    rfl

theorem cell21_1825048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_1825048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825048 prefixEnd_1825048 := by exact prefixLift 1825048
  have htrace : WordTrace (prefixWord ++ tailWord_1825048) baseStart_1825048 baseEnd_1825048 := by
    simpa [prefixWord, tailWord_1825048, baseEnd_1825048] using wordTrace_append hprefix tailTrace_1825048
  have hstable : (prefixWord ++ tailWord_1825048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825048).length < 2 ^ (prefixWord ++ tailWord_1825048).sum := by decide
  have hdescent : baseEnd_1825048 < baseStart_1825048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825096 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_1825096 : Nat := 118140960795 + 1825096 * 2 ^ 59
def prefixEnd_1825096 : Nat := 4983230072969 + 3 ^ 40 * 1825096 * 2
def baseEnd_1825096 : Nat := 416511772710354016536241

theorem tailTrace_1825096 : CollatzResearch.WordTrace tailWord_1825096 prefixEnd_1825096 416511772710354016536241 := by
  unfold tailWord_1825096
  simp only [CollatzResearch.WordTrace]
  refine ⟨33283359897998184213039571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44377813197330912284052761 33283359897998184213039571)
  ·
    refine ⟨49925039846997276319559357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33283359897998184213039571 49925039846997276319559357)
    ·
      refine ⟨18721889942623978619834759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49925039846997276319559357 18721889942623978619834759)
      ·
        refine ⟨28082834913935967929752139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18721889942623978619834759 28082834913935967929752139)
        ·
          refine ⟨42124252370903951894628209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28082834913935967929752139 42124252370903951894628209)
          ·
            refine ⟨31593189278177963920971157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42124252370903951894628209 31593189278177963920971157)
            ·
              refine ⟨1480930747414592058795523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31593189278177963920971157 1480930747414592058795523)
              ·
                refine ⟨2221396121121888088193285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1480930747414592058795523 2221396121121888088193285)
                ·
                  refine ⟨416511772710354016536241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221396121121888088193285 416511772710354016536241)
                  ·
                    rfl

theorem cell21_1825096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_1825096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825096 prefixEnd_1825096 := by exact prefixLift 1825096
  have htrace : WordTrace (prefixWord ++ tailWord_1825096) baseStart_1825096 baseEnd_1825096 := by
    simpa [prefixWord, tailWord_1825096, baseEnd_1825096] using wordTrace_append hprefix tailTrace_1825096
  have hstable : (prefixWord ++ tailWord_1825096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825096).length < 2 ^ (prefixWord ++ tailWord_1825096).sum := by decide
  have hdescent : baseEnd_1825096 < baseStart_1825096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825220 : List Nat := [2, 3, 3, 2, 2, 2, 2, 5]
def baseStart_1825220 : Nat := 118140960795 + 1825220 * 2 ^ 59
def prefixEnd_1825220 : Nat := 4983230072969 + 3 ^ 40 * 1825220 * 2
def baseEnd_1825220 : Nat := 138846690399919118823107

theorem tailTrace_1825220 : CollatzResearch.WordTrace tailWord_1825220 prefixEnd_1825220 138846690399919118823107 := by
  unfold tailWord_1825220
  simp only [CollatzResearch.WordTrace]
  refine ⟨33285621223773568801796557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44380828298364758402395409 33285621223773568801796557)
  ·
    refine ⟨12482107958915088300673709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33285621223773568801796557 12482107958915088300673709)
    ·
      refine ⟨4680790484593158112752641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12482107958915088300673709 4680790484593158112752641)
      ·
        refine ⟨3510592863444868584564481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4680790484593158112752641 3510592863444868584564481)
        ·
          refine ⟨2632944647583651438423361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3510592863444868584564481 2632944647583651438423361)
          ·
            refine ⟨1974708485687738578817521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2632944647583651438423361 1974708485687738578817521)
            ·
              refine ⟨1481031364265803934113141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974708485687738578817521 1481031364265803934113141)
              ·
                refine ⟨138846690399919118823107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1481031364265803934113141 138846690399919118823107)
                ·
                  rfl

theorem cell21_1825220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 5].length) (baseStart_1825220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825220 prefixEnd_1825220 := by exact prefixLift 1825220
  have htrace : WordTrace (prefixWord ++ tailWord_1825220) baseStart_1825220 baseEnd_1825220 := by
    simpa [prefixWord, tailWord_1825220, baseEnd_1825220] using wordTrace_append hprefix tailTrace_1825220
  have hstable : (prefixWord ++ tailWord_1825220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825220).length < 2 ^ (prefixWord ++ tailWord_1825220).sum := by decide
  have hdescent : baseEnd_1825220 < baseStart_1825220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825251 : List Nat := [1, 1, 1, 6, 3, 1, 3, 2, 3]
def baseStart_1825251 : Nat := 118140960795 + 1825251 * 2 ^ 59
def prefixEnd_1825251 : Nat := 4983230072969 + 3 ^ 40 * 1825251 * 2
def baseEnd_1825251 : Nat := 416547145822108191452591

theorem tailTrace_1825251 : CollatzResearch.WordTrace tailWord_1825251 prefixEnd_1825251 416547145822108191452591 := by
  unfold tailWord_1825251
  simp only [CollatzResearch.WordTrace]
  refine ⟨66572373110434829897971607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44381582073623219931981071 66572373110434829897971607)
  ·
    refine ⟨99858559665652244846957411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66572373110434829897971607 99858559665652244846957411)
    ·
      refine ⟨149787839498478367270436117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99858559665652244846957411 149787839498478367270436117)
      ·
        refine ⟨7021304976491173465801693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149787839498478367270436117 7021304976491173465801693)
        ·
          refine ⟨2632989366184190049675635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7021304976491173465801693 2632989366184190049675635)
          ·
            refine ⟨3949484049276285074513453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632989366184190049675635 3949484049276285074513453)
            ·
              refine ⟨1481056518478606902942545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3949484049276285074513453 1481056518478606902942545)
              ·
                refine ⟨1110792388858955177206909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481056518478606902942545 1110792388858955177206909)
                ·
                  refine ⟨416547145822108191452591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110792388858955177206909 416547145822108191452591)
                  ·
                    rfl

theorem cell21_1825251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 3].length) (baseStart_1825251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825251 prefixEnd_1825251 := by exact prefixLift 1825251
  have htrace : WordTrace (prefixWord ++ tailWord_1825251) baseStart_1825251 baseEnd_1825251 := by
    simpa [prefixWord, tailWord_1825251, baseEnd_1825251] using wordTrace_append hprefix tailTrace_1825251
  have hstable : (prefixWord ++ tailWord_1825251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825251).length < 2 ^ (prefixWord ++ tailWord_1825251).sum := by decide
  have hdescent : baseEnd_1825251 < baseStart_1825251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825262 : List Nat := [4, 1, 2, 1, 2, 3, 2, 6]
def baseStart_1825262 : Nat := 118140960795 + 1825262 * 2 ^ 59
def prefixEnd_1825262 : Nat := 4983230072969 + 3 ^ 40 * 1825262 * 2
def baseEnd_1825262 : Nat := 138849885390658205589745

theorem tailTrace_1825262 : CollatzResearch.WordTrace tailWord_1825262 prefixEnd_1825262 138849885390658205589745 := by
  unfold tailWord_1825262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8321596789174372347077755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44381849542263319184414693 8321596789174372347077755)
  ·
    refine ⟨12482395183761558520616633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8321596789174372347077755 12482395183761558520616633)
    ·
      refine ⟨9361796387821168890462475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12482395183761558520616633 9361796387821168890462475)
      ·
        refine ⟨14042694581731753335693713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9361796387821168890462475 14042694581731753335693713)
        ·
          refine ⟨10532020936298815001770285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14042694581731753335693713 10532020936298815001770285)
          ·
            refine ⟨3949507851112055625663857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10532020936298815001770285 3949507851112055625663857)
            ·
              refine ⟨2962130888334041719247893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949507851112055625663857 2962130888334041719247893)
              ·
                refine ⟨138849885390658205589745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2962130888334041719247893 138849885390658205589745)
                ·
                  rfl

theorem cell21_1825262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_1825262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825262 prefixEnd_1825262 := by exact prefixLift 1825262
  have htrace : WordTrace (prefixWord ++ tailWord_1825262) baseStart_1825262 baseEnd_1825262 := by
    simpa [prefixWord, tailWord_1825262, baseEnd_1825262] using wordTrace_append hprefix tailTrace_1825262
  have hstable : (prefixWord ++ tailWord_1825262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825262).length < 2 ^ (prefixWord ++ tailWord_1825262).sum := by decide
  have hdescent : baseEnd_1825262 < baseStart_1825262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825338 : List Nat := [3, 1, 1, 1, 3, 4, 3, 5]
def baseStart_1825338 : Nat := 118140960795 + 1825338 * 2 ^ 59
def prefixEnd_1825338 : Nat := 4983230072969 + 3 ^ 40 * 1825338 * 2
def baseEnd_1825338 : Nat := 138855666802471791167471

theorem tailTrace_1825338 : CollatzResearch.WordTrace tailWord_1825338 prefixEnd_1825338 138855666802471791167471 := by
  unfold tailWord_1825338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16643886565279910939097167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44383697507413095837592445 16643886565279910939097167)
  ·
    refine ⟨24965829847919866408645751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16643886565279910939097167 24965829847919866408645751)
    ·
      refine ⟨37448744771879799612968627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24965829847919866408645751 37448744771879799612968627)
      ·
        refine ⟨56173117157819699419452941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37448744771879799612968627 56173117157819699419452941)
        ·
          refine ⟨21064918934182387282294853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56173117157819699419452941 21064918934182387282294853)
          ·
            refine ⟨3949672300159197615430285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21064918934182387282294853 3949672300159197615430285)
            ·
              refine ⟨1481127112559699105786357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3949672300159197615430285 1481127112559699105786357)
              ·
                refine ⟨138855666802471791167471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1481127112559699105786357 138855666802471791167471)
                ·
                  rfl

theorem cell21_1825338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_1825338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825338 prefixEnd_1825338 := by exact prefixLift 1825338
  have htrace : WordTrace (prefixWord ++ tailWord_1825338) baseStart_1825338 baseEnd_1825338 := by
    simpa [prefixWord, tailWord_1825338, baseEnd_1825338] using wordTrace_append hprefix tailTrace_1825338
  have hstable : (prefixWord ++ tailWord_1825338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825338).length < 2 ^ (prefixWord ++ tailWord_1825338).sum := by decide
  have hdescent : baseEnd_1825338 < baseStart_1825338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825411 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 7]
def baseStart_1825411 : Nat := 118140960795 + 1825411 * 2 ^ 59
def prefixEnd_1825411 : Nat := 4983230072969 + 3 ^ 40 * 1825411 * 2
def baseEnd_1825411 : Nat := 416583660001983468785597

theorem tailTrace_1825411 : CollatzResearch.WordTrace tailWord_1825411 prefixEnd_1825411 416583660001983468785597 := by
  unfold tailWord_1825411
  simp only [CollatzResearch.WordTrace]
  refine ⟨66578208789855177223796087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44385472526570118149197391 66578208789855177223796087)
  ·
    refine ⟨99867313184782765835694131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66578208789855177223796087 99867313184782765835694131)
    ·
      refine ⟨149800969777174148753541197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99867313184782765835694131 149800969777174148753541197)
      ·
        refine ⟨56175363666440305782577949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149800969777174148753541197 56175363666440305782577949)
        ·
          refine ⟨21065761374915114668466731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56175363666440305782577949 21065761374915114668466731)
          ·
            refine ⟨31598642062372672002700097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21065761374915114668466731 31598642062372672002700097)
            ·
              refine ⟨23698981546779504002025073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31598642062372672002700097 23698981546779504002025073)
              ·
                refine ⟨17774236160084628001518805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23698981546779504002025073 17774236160084628001518805)
                ·
                  refine ⟨416583660001983468785597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17774236160084628001518805 416583660001983468785597)
                  ·
                    rfl

theorem cell21_1825411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_1825411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825411 prefixEnd_1825411 := by exact prefixLift 1825411
  have htrace : WordTrace (prefixWord ++ tailWord_1825411) baseStart_1825411 baseEnd_1825411 := by
    simpa [prefixWord, tailWord_1825411, baseEnd_1825411] using wordTrace_append hprefix tailTrace_1825411
  have hstable : (prefixWord ++ tailWord_1825411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825411).length < 2 ^ (prefixWord ++ tailWord_1825411).sum := by decide
  have hdescent : baseEnd_1825411 < baseStart_1825411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825434 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 4]
def baseStart_1825434 : Nat := 118140960795 + 1825434 * 2 ^ 59
def prefixEnd_1825434 : Nat := 4983230072969 + 3 ^ 40 * 1825434 * 2
def baseEnd_1825434 : Nat := 416588908915340539902217

theorem tailTrace_1825434 : CollatzResearch.WordTrace tailWord_1825434 prefixEnd_1825434 416588908915340539902217 := by
  unfold tailWord_1825434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16644761917192963037970839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44386031779181234767922237 16644761917192963037970839)
  ·
    refine ⟨24967142875789444556956259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16644761917192963037970839 24967142875789444556956259)
    ·
      refine ⟨37450714313684166835434389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24967142875789444556956259 37450714313684166835434389)
      ·
        refine ⟨1755502233453945320410987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37450714313684166835434389 1755502233453945320410987)
        ·
          refine ⟨2633253350180917980616481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755502233453945320410987 2633253350180917980616481)
          ·
            refine ⟨1974940012635688485462361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2633253350180917980616481 1974940012635688485462361)
            ·
              refine ⟨1481205009476766364096771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1974940012635688485462361 1481205009476766364096771)
              ·
                refine ⟨2221807514215149546145157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481205009476766364096771 2221807514215149546145157)
                ·
                  refine ⟨416588908915340539902217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221807514215149546145157 416588908915340539902217)
                  ·
                    rfl

theorem cell21_1825434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_1825434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825434 prefixEnd_1825434 := by exact prefixLift 1825434
  have htrace : WordTrace (prefixWord ++ tailWord_1825434) baseStart_1825434 baseEnd_1825434 := by
    simpa [prefixWord, tailWord_1825434, baseEnd_1825434] using wordTrace_append hprefix tailTrace_1825434
  have hstable : (prefixWord ++ tailWord_1825434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825434).length < 2 ^ (prefixWord ++ tailWord_1825434).sum := by decide
  have hdescent : baseEnd_1825434 < baseStart_1825434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825476 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1825476 : Nat := 118140960795 + 1825476 * 2 ^ 59
def prefixEnd_1825476 : Nat := 4983230072969 + 3 ^ 40 * 1825476 * 2
def baseEnd_1825476 : Nat := 416598493887557800202131

theorem tailTrace_1825476 : CollatzResearch.WordTrace tailWord_1825476 prefixEnd_1825476 416598493887557800202131 := by
  unfold tailWord_1825476
  simp only [CollatzResearch.WordTrace]
  refine ⟨33290289767309846662456141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44387053023079795549941521 33290289767309846662456141)
  ·
    refine ⟨12483858662741192498421053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33290289767309846662456141 12483858662741192498421053)
    ·
      refine ⟨4681446998527947186907895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12483858662741192498421053 4681446998527947186907895)
      ·
        refine ⟨7022170497791920780361843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681446998527947186907895 7022170497791920780361843)
        ·
          refine ⟨10533255746687881170542765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022170497791920780361843 10533255746687881170542765)
          ·
            refine ⟨3949970905007955438953537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10533255746687881170542765 3949970905007955438953537)
            ·
              refine ⟨2962478178755966579215153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949970905007955438953537 2962478178755966579215153)
              ·
                refine ⟨2221858634066974934411365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962478178755966579215153 2221858634066974934411365)
                ·
                  refine ⟨416598493887557800202131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2221858634066974934411365 416598493887557800202131)
                  ·
                    rfl

theorem cell21_1825476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1825476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825476 prefixEnd_1825476 := by exact prefixLift 1825476
  have htrace : WordTrace (prefixWord ++ tailWord_1825476) baseStart_1825476 baseEnd_1825476 := by
    simpa [prefixWord, tailWord_1825476, baseEnd_1825476] using wordTrace_append hprefix tailTrace_1825476
  have hstable : (prefixWord ++ tailWord_1825476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825476).length < 2 ^ (prefixWord ++ tailWord_1825476).sum := by decide
  have hdescent : baseEnd_1825476 < baseStart_1825476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825521 : List Nat := [1, 2, 2, 2, 2, 2, 4, 3, 3]
def baseStart_1825521 : Nat := 118140960795 + 1825521 * 2 ^ 59
def prefixEnd_1825521 : Nat := 4983230072969 + 3 ^ 40 * 1825521 * 2
def baseEnd_1825521 : Nat := 416608763500647721952039

theorem tailTrace_1825521 : CollatzResearch.WordTrace tailWord_1825521 prefixEnd_1825521 416608763500647721952039 := by
  unfold tailWord_1825521
  simp only [CollatzResearch.WordTrace]
  refine ⟨66582220819456666010300417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44388147212971110673533611 66582220819456666010300417)
  ·
    refine ⟨49936665614592499507725313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66582220819456666010300417 49936665614592499507725313)
    ·
      refine ⟨37452499210944374630793985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49936665614592499507725313 37452499210944374630793985)
      ·
        refine ⟨28089374408208280973095489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37452499210944374630793985 28089374408208280973095489)
        ·
          refine ⟨21067030806156210729821617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28089374408208280973095489 21067030806156210729821617)
          ·
            refine ⟨15800273104617158047366213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21067030806156210729821617 15800273104617158047366213)
            ·
              refine ⟨2962551207115717133881165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15800273104617158047366213 2962551207115717133881165)
              ·
                refine ⟨1110956702668393925205437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962551207115717133881165 1110956702668393925205437)
                ·
                  refine ⟨416608763500647721952039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110956702668393925205437 416608763500647721952039)
                  ·
                    rfl

theorem cell21_1825521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 3].length) (baseStart_1825521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825521 prefixEnd_1825521 := by exact prefixLift 1825521
  have htrace : WordTrace (prefixWord ++ tailWord_1825521) baseStart_1825521 baseEnd_1825521 := by
    simpa [prefixWord, tailWord_1825521, baseEnd_1825521] using wordTrace_append hprefix tailTrace_1825521
  have hstable : (prefixWord ++ tailWord_1825521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825521).length < 2 ^ (prefixWord ++ tailWord_1825521).sum := by decide
  have hdescent : baseEnd_1825521 < baseStart_1825521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825538 : List Nat := [3, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1825538 : Nat := 118140960795 + 1825538 * 2 ^ 59
def prefixEnd_1825538 : Nat := 4983230072969 + 3 ^ 40 * 1825538 * 2
def baseEnd_1825538 : Nat := 416612643132259470168671

theorem tailTrace_1825538 : CollatzResearch.WordTrace tailWord_1825538 prefixEnd_1825538 416612643132259470168671 := by
  unfold tailWord_1825538
  simp only [CollatzResearch.WordTrace]
  refine ⟨16645710215098769478417317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44388560573596718609112845 16645710215098769478417317)
  ·
    refine ⟨3121070665331019277203247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16645710215098769478417317 3121070665331019277203247)
    ·
      refine ⟨4681605997996528915804871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3121070665331019277203247 4681605997996528915804871)
      ·
        refine ⟨7022408996994793373707307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4681605997996528915804871 7022408996994793373707307)
        ·
          refine ⟨10533613495492190060560961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7022408996994793373707307 10533613495492190060560961)
          ·
            refine ⟨7900210121619142545420721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10533613495492190060560961 7900210121619142545420721)
            ·
              refine ⟨5925157591214356909065541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7900210121619142545420721 5925157591214356909065541)
              ·
                refine ⟨1110967048352691920449789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5925157591214356909065541 1110967048352691920449789)
                ·
                  refine ⟨416612643132259470168671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110967048352691920449789 416612643132259470168671)
                  ·
                    rfl

theorem cell21_1825538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1825538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825538 prefixEnd_1825538 := by exact prefixLift 1825538
  have htrace : WordTrace (prefixWord ++ tailWord_1825538) baseStart_1825538 baseEnd_1825538 := by
    simpa [prefixWord, tailWord_1825538, baseEnd_1825538] using wordTrace_append hprefix tailTrace_1825538
  have hstable : (prefixWord ++ tailWord_1825538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825538).length < 2 ^ (prefixWord ++ tailWord_1825538).sum := by decide
  have hdescent : baseEnd_1825538 < baseStart_1825538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825690 : List Nat := [3, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_1825690 : Nat := 118140960795 + 1825690 * 2 ^ 59
def prefixEnd_1825690 : Nat := 4983230072969 + 3 ^ 40 * 1825690 * 2
def baseEnd_1825690 : Nat := 416647331603140983635027

theorem tailTrace_1825690 : CollatzResearch.WordTrace tailWord_1825690 prefixEnd_1825690 416647331603140983635027 := by
  unfold tailWord_1825690
  simp only [CollatzResearch.WordTrace]
  refine ⟨16647096188961101968300631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44392256503896271915468349 16647096188961101968300631)
  ·
    refine ⟨24970644283441652952450947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16647096188961101968300631 24970644283441652952450947)
    ·
      refine ⟨37455966425162479428676421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24970644283441652952450947 37455966425162479428676421)
      ·
        refine ⟨7022993704717964892876829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37455966425162479428676421 7022993704717964892876829)
        ·
          refine ⟨2633622639269236834828811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7022993704717964892876829 2633622639269236834828811)
          ·
            refine ⟨3950433958903855252243217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633622639269236834828811 3950433958903855252243217)
            ·
              refine ⟨2962825469177891439182413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950433958903855252243217 2962825469177891439182413)
              ·
                refine ⟨1111059550941709289693405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962825469177891439182413 1111059550941709289693405)
                ·
                  refine ⟨416647331603140983635027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111059550941709289693405 416647331603140983635027)
                  ·
                    rfl

theorem cell21_1825690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_1825690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825690 prefixEnd_1825690 := by exact prefixLift 1825690
  have htrace : WordTrace (prefixWord ++ tailWord_1825690) baseStart_1825690 baseEnd_1825690 := by
    simpa [prefixWord, tailWord_1825690, baseEnd_1825690] using wordTrace_append hprefix tailTrace_1825690
  have hstable : (prefixWord ++ tailWord_1825690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825690).length < 2 ^ (prefixWord ++ tailWord_1825690).sum := by decide
  have hdescent : baseEnd_1825690 < baseStart_1825690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825741 : List Nat := [1, 6, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1825741 : Nat := 118140960795 + 1825741 * 2 ^ 59
def prefixEnd_1825741 : Nat := 4983230072969 + 3 ^ 40 * 1825741 * 2
def baseEnd_1825741 : Nat := 416658970497976228284923

theorem tailTrace_1825741 : CollatzResearch.WordTrace tailWord_1825741 prefixEnd_1825741 416658970497976228284923 := by
  unfold tailWord_1825741
  simp only [CollatzResearch.WordTrace]
  refine ⟨66590244878659643583309077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44393496585773095722206051 66590244878659643583309077)
  ·
    refine ⟨3121417728687170792967613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66590244878659643583309077 3121417728687170792967613)
    ·
      refine ⟨1170531648257689047362855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3121417728687170792967613 1170531648257689047362855)
      ·
        refine ⟨1755797472386533571044283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170531648257689047362855 1755797472386533571044283)
        ·
          refine ⟨2633696208579800356566425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1755797472386533571044283 2633696208579800356566425)
          ·
            refine ⟨1975272156434850267424819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2633696208579800356566425 1975272156434850267424819)
            ·
              refine ⟨2962908234652275401137229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1975272156434850267424819 2962908234652275401137229)
              ·
                refine ⟨1111090587994603275426461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2962908234652275401137229 1111090587994603275426461)
                ·
                  refine ⟨416658970497976228284923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111090587994603275426461 416658970497976228284923)
                  ·
                    rfl

theorem cell21_1825741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1825741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825741 prefixEnd_1825741 := by exact prefixLift 1825741
  have htrace : WordTrace (prefixWord ++ tailWord_1825741) baseStart_1825741 baseEnd_1825741 := by
    simpa [prefixWord, tailWord_1825741, baseEnd_1825741] using wordTrace_append hprefix tailTrace_1825741
  have hstable : (prefixWord ++ tailWord_1825741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825741).length < 2 ^ (prefixWord ++ tailWord_1825741).sum := by decide
  have hdescent : baseEnd_1825741 < baseStart_1825741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825777 : List Nat := [1, 2, 2, 2, 4, 2, 2, 6]
def baseStart_1825777 : Nat := 118140960795 + 1825777 * 2 ^ 59
def prefixEnd_1825777 : Nat := 4983230072969 + 3 ^ 40 * 1825777 * 2
def baseEnd_1825777 : Nat := 138889062062816055228283

theorem tailTrace_1825777 : CollatzResearch.WordTrace tailWord_1825777 prefixEnd_1825777 138889062062816055228283 := by
  unfold tailWord_1825777
  simp only [CollatzResearch.WordTrace]
  refine ⟨66591557906529221731619585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44394371937686147821079723 66591557906529221731619585)
  ·
    refine ⟨49943668429896916298714689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66591557906529221731619585 49943668429896916298714689)
    ·
      refine ⟨37457751322422687224036017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49943668429896916298714689 37457751322422687224036017)
      ·
        refine ⟨28093313491817015418027013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37457751322422687224036017 28093313491817015418027013)
        ·
          refine ⟨5267496279715690390880065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28093313491817015418027013 5267496279715690390880065)
          ·
            refine ⟨3950622209786767793160049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5267496279715690390880065 3950622209786767793160049)
            ·
              refine ⟨2962966657340075844870037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950622209786767793160049 2962966657340075844870037)
              ·
                refine ⟨138889062062816055228283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2962966657340075844870037 138889062062816055228283)
                ·
                  rfl

theorem cell21_1825777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 6].length) (baseStart_1825777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825777 prefixEnd_1825777 := by exact prefixLift 1825777
  have htrace : WordTrace (prefixWord ++ tailWord_1825777) baseStart_1825777 baseEnd_1825777 := by
    simpa [prefixWord, tailWord_1825777, baseEnd_1825777] using wordTrace_append hprefix tailTrace_1825777
  have hstable : (prefixWord ++ tailWord_1825777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825777).length < 2 ^ (prefixWord ++ tailWord_1825777).sum := by decide
  have hdescent : baseEnd_1825777 < baseStart_1825777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825825 : List Nat := [1, 2, 3, 2, 3, 2, 1, 4, 3]
def baseStart_1825825 : Nat := 118140960795 + 1825825 * 2 ^ 59
def prefixEnd_1825825 : Nat := 4983230072969 + 3 ^ 40 * 1825825 * 2
def baseEnd_1825825 : Nat := 416678140442410748884751

theorem tailTrace_1825825 : CollatzResearch.WordTrace tailWord_1825825 prefixEnd_1825825 416678140442410748884751 := by
  unfold tailWord_1825825
  simp only [CollatzResearch.WordTrace]
  refine ⟨66593308610355325929366929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44395539073570217286244619 66593308610355325929366929)
  ·
    refine ⟨49944981457766494447025197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66593308610355325929366929 49944981457766494447025197)
    ·
      refine ⟨18729368046662435417634449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49944981457766494447025197 18729368046662435417634449)
      ·
        refine ⟨14047026034996826563225837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18729368046662435417634449 14047026034996826563225837)
        ·
          refine ⟨5267634763123809961209689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14047026034996826563225837 5267634763123809961209689)
          ·
            refine ⟨3950726072342857470907267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5267634763123809961209689 3950726072342857470907267)
            ·
              refine ⟨5926089108514286206360901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3950726072342857470907267 5926089108514286206360901)
              ·
                refine ⟨1111141707846428663692669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5926089108514286206360901 1111141707846428663692669)
                ·
                  refine ⟨416678140442410748884751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111141707846428663692669 416678140442410748884751)
                  ·
                    rfl

theorem cell21_1825825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 3].length) (baseStart_1825825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825825 prefixEnd_1825825 := by exact prefixLift 1825825
  have htrace : WordTrace (prefixWord ++ tailWord_1825825) baseStart_1825825 baseEnd_1825825 := by
    simpa [prefixWord, tailWord_1825825, baseEnd_1825825] using wordTrace_append hprefix tailTrace_1825825
  have hstable : (prefixWord ++ tailWord_1825825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825825).length < 2 ^ (prefixWord ++ tailWord_1825825).sum := by decide
  have hdescent : baseEnd_1825825 < baseStart_1825825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825884 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_1825884 : Nat := 118140960795 + 1825884 * 2 ^ 59
def prefixEnd_1825884 : Nat := 4983230072969 + 3 ^ 40 * 1825884 * 2
def baseEnd_1825884 : Nat := 416691605046239757401297

theorem tailTrace_1825884 : CollatzResearch.WordTrace tailWord_1825884 prefixEnd_1825884 416691605046239757401297 := by
  unfold tailWord_1825884
  simp only [CollatzResearch.WordTrace]
  refine ⟨33297730258570789502882353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44396973678094386003843137 33297730258570789502882353)
  ·
    refine ⟨24973297693928092127161765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33297730258570789502882353 24973297693928092127161765)
    ·
      refine ⟨4682493317611517273842831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24973297693928092127161765 4682493317611517273842831)
      ·
        refine ⟨7023739976417275910764247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682493317611517273842831 7023739976417275910764247)
        ·
          refine ⟨10535609964625913866146371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023739976417275910764247 10535609964625913866146371)
          ·
            refine ⟨15803414946938870799219557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10535609964625913866146371 15803414946938870799219557)
            ·
              refine ⟨2963140302551038274853667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15803414946938870799219557 2963140302551038274853667)
              ·
                refine ⟨4444710453826557412280501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963140302551038274853667 4444710453826557412280501)
                ·
                  refine ⟨416691605046239757401297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4444710453826557412280501 416691605046239757401297)
                  ·
                    rfl

theorem cell21_1825884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_1825884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825884 prefixEnd_1825884 := by exact prefixLift 1825884
  have htrace : WordTrace (prefixWord ++ tailWord_1825884) baseStart_1825884 baseEnd_1825884 := by
    simpa [prefixWord, tailWord_1825884, baseEnd_1825884] using wordTrace_append hprefix tailTrace_1825884
  have hstable : (prefixWord ++ tailWord_1825884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825884).length < 2 ^ (prefixWord ++ tailWord_1825884).sum := by decide
  have hdescent : baseEnd_1825884 < baseStart_1825884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825988 : List Nat := [2, 3, 3, 1, 12]
def baseStart_1825988 : Nat := 118140960795 + 1825988 * 2 ^ 59
def prefixEnd_1825988 : Nat := 4983230072969 + 3 ^ 40 * 1825988 * 2
def baseEnd_1825988 : Nat := 5144633818063687502071

theorem tailTrace_1825988 : CollatzResearch.WordTrace tailWord_1825988 prefixEnd_1825988 5144633818063687502071 := by
  unfold tailWord_1825988
  simp only [CollatzResearch.WordTrace]
  refine ⟨33299626854382402383775309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44399502472509869845033745 33299626854382402383775309)
  ·
    refine ⟨12487360070393400893915741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33299626854382402383775309 12487360070393400893915741)
    ·
      refine ⟨4682760026397525335218403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12487360070393400893915741 4682760026397525335218403)
      ·
        refine ⟨7024140039596288002827605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682760026397525335218403 7024140039596288002827605)
        ·
          refine ⟨5144633818063687502071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7024140039596288002827605 5144633818063687502071)
          ·
            rfl

theorem cell21_1825988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 12].length) (baseStart_1825988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825988 prefixEnd_1825988 := by exact prefixLift 1825988
  have htrace : WordTrace (prefixWord ++ tailWord_1825988) baseStart_1825988 baseEnd_1825988 := by
    simpa [prefixWord, tailWord_1825988, baseEnd_1825988] using wordTrace_append hprefix tailTrace_1825988
  have hstable : (prefixWord ++ tailWord_1825988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825988).length < 2 ^ (prefixWord ++ tailWord_1825988).sum := by decide
  have hdescent : baseEnd_1825988 < baseStart_1825988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1825994 : List Nat := [3, 1, 2, 1, 3, 4, 2, 2, 3]
def baseStart_1825994 : Nat := 118140960795 + 1825994 * 2 ^ 59
def prefixEnd_1825994 : Nat := 4983230072969 + 3 ^ 40 * 1825994 * 2
def baseEnd_1825994 : Nat := 416716708544904010567739

theorem tailTrace_1825994 : CollatzResearch.WordTrace tailWord_1825994 prefixEnd_1825994 416716708544904010567739 := by
  unfold tailWord_1825994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16649868136685766948067259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44399648364495378528179357 16649868136685766948067259)
  ·
    refine ⟨24974802205028650422100889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16649868136685766948067259 24974802205028650422100889)
    ·
      refine ⟨18731101653771487816575667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24974802205028650422100889 18731101653771487816575667)
      ·
        refine ⟨28096652480657231724863501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18731101653771487816575667 28096652480657231724863501)
        ·
          refine ⟨10536244680246461896823813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28096652480657231724863501 10536244680246461896823813)
          ·
            refine ⟨1975545877546211605654465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10536244680246461896823813 1975545877546211605654465)
            ·
              refine ⟨1481659408159658704240849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975545877546211605654465 1481659408159658704240849)
              ·
                refine ⟨1111244556119744028180637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1481659408159658704240849 1111244556119744028180637)
                ·
                  refine ⟨416716708544904010567739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111244556119744028180637 416716708544904010567739)
                  ·
                    rfl

theorem cell21_1825994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_1825994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1825994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1825994 prefixEnd_1825994 := by exact prefixLift 1825994
  have htrace : WordTrace (prefixWord ++ tailWord_1825994) baseStart_1825994 baseEnd_1825994 := by
    simpa [prefixWord, tailWord_1825994, baseEnd_1825994] using wordTrace_append hprefix tailTrace_1825994
  have hstable : (prefixWord ++ tailWord_1825994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1825994).length < 2 ^ (prefixWord ++ tailWord_1825994).sum := by decide
  have hdescent : baseEnd_1825994 < baseStart_1825994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1825994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826005 : List Nat := [1, 3, 2, 4, 1, 1, 3, 6]
def baseStart_1826005 : Nat := 118140960795 + 1826005 * 2 ^ 59
def prefixEnd_1826005 : Nat := 4983230072969 + 3 ^ 40 * 1826005 * 2
def baseEnd_1826005 : Nat := 138906406298256811961461

theorem tailTrace_1826005 : CollatzResearch.WordTrace tailWord_1826005 prefixEnd_1826005 138906406298256811961461 := by
  unfold tailWord_1826005
  simp only [CollatzResearch.WordTrace]
  refine ⟨66599873749703216670919469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44399915833135477780612979 66599873749703216670919469)
  ·
    refine ⟨24974952656138706251594801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66599873749703216670919469 24974952656138706251594801)
    ·
      refine ⟨18731214492104029688696101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24974952656138706251594801 18731214492104029688696101)
      ·
        refine ⟨3512102717269505566630519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18731214492104029688696101 3512102717269505566630519)
        ·
          refine ⟨5268154075904258349945779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512102717269505566630519 5268154075904258349945779)
          ·
            refine ⟨7902231113856387524918669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5268154075904258349945779 7902231113856387524918669)
            ·
              refine ⟨2963336667696145321844501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7902231113856387524918669 2963336667696145321844501)
              ·
                refine ⟨138906406298256811961461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2963336667696145321844501 138906406298256811961461)
                ·
                  rfl

theorem cell21_1826005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 6].length) (baseStart_1826005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826005 prefixEnd_1826005 := by exact prefixLift 1826005
  have htrace : WordTrace (prefixWord ++ tailWord_1826005) baseStart_1826005 baseEnd_1826005 := by
    simpa [prefixWord, tailWord_1826005, baseEnd_1826005] using wordTrace_append hprefix tailTrace_1826005
  have hstable : (prefixWord ++ tailWord_1826005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826005).length < 2 ^ (prefixWord ++ tailWord_1826005).sum := by decide
  have hdescent : baseEnd_1826005 < baseStart_1826005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826033 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 6]
def baseStart_1826033 : Nat := 118140960795 + 1826033 * 2 ^ 59
def prefixEnd_1826033 : Nat := 4983230072969 + 3 ^ 40 * 1826033 * 2
def baseEnd_1826033 : Nat := 416725608876248609417659

theorem tailTrace_1826033 : CollatzResearch.WordTrace tailWord_1826033 prefixEnd_1826033 416725608876248609417659 := by
  unfold tailWord_1826033
  simp only [CollatzResearch.WordTrace]
  refine ⟨66600894993601777452938753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44400596662401184968625835 66600894993601777452938753)
  ·
    refine ⟨49950671245201333089704065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66600894993601777452938753 49950671245201333089704065)
    ·
      refine ⟨37463003433900999817278049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49950671245201333089704065 37463003433900999817278049)
      ·
        refine ⟨28097252575425749862958537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37463003433900999817278049 28097252575425749862958537)
        ·
          refine ⟨21072939431569312397218903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28097252575425749862958537 21072939431569312397218903)
          ·
            refine ⟨31609409147353968595828355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21072939431569312397218903 31609409147353968595828355)
            ·
              refine ⟨47414113721030952893742533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31609409147353968595828355 47414113721030952893742533)
              ·
                refine ⟨8890146322693303667576725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47414113721030952893742533 8890146322693303667576725)
                ·
                  refine ⟨416725608876248609417659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8890146322693303667576725 416725608876248609417659)
                  ·
                    rfl

theorem cell21_1826033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_1826033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826033 prefixEnd_1826033 := by exact prefixLift 1826033
  have htrace : WordTrace (prefixWord ++ tailWord_1826033) baseStart_1826033 baseEnd_1826033 := by
    simpa [prefixWord, tailWord_1826033, baseEnd_1826033] using wordTrace_append hprefix tailTrace_1826033
  have hstable : (prefixWord ++ tailWord_1826033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826033).length < 2 ^ (prefixWord ++ tailWord_1826033).sum := by decide
  have hdescent : baseEnd_1826033 < baseStart_1826033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826126 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_1826126 : Nat := 118140960795 + 1826126 * 2 ^ 59
def prefixEnd_1826126 : Nat := 4983230072969 + 3 ^ 40 * 1826126 * 2
def baseEnd_1826126 : Nat := 416746832743301114367469

theorem tailTrace_1826126 : CollatzResearch.WordTrace tailWord_1826126 prefixEnd_1826126 416746832743301114367469 := by
  unfold tailWord_1826126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325535872783106792009279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44402857988176569557382821 8325535872783106792009279)
  ·
    refine ⟨12488303809174660188013919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8325535872783106792009279 12488303809174660188013919)
    ·
      refine ⟨18732455713761990282020879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12488303809174660188013919 18732455713761990282020879)
      ·
        refine ⟨28098683570642985423031319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18732455713761990282020879 28098683570642985423031319)
        ·
          refine ⟨42148025355964478134546979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28098683570642985423031319 42148025355964478134546979)
          ·
            refine ⟨63222038033946717201820469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42148025355964478134546979 63222038033946717201820469)
            ·
              refine ⟨5927066065682504737670669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63222038033946717201820469 5927066065682504737670669)
              ·
                refine ⟨2222649774630939276626501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5927066065682504737670669 2222649774630939276626501)
                ·
                  refine ⟨416746832743301114367469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2222649774630939276626501 416746832743301114367469)
                  ·
                    rfl

theorem cell21_1826126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_1826126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826126 prefixEnd_1826126 := by exact prefixLift 1826126
  have htrace : WordTrace (prefixWord ++ tailWord_1826126) baseStart_1826126 baseEnd_1826126 := by
    simpa [prefixWord, tailWord_1826126, baseEnd_1826126] using wordTrace_append hprefix tailTrace_1826126
  have hstable : (prefixWord ++ tailWord_1826126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826126).length < 2 ^ (prefixWord ++ tailWord_1826126).sum := by decide
  have hdescent : baseEnd_1826126 < baseStart_1826126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826205 : List Nat := [1, 4, 2, 1, 3, 2, 2, 3, 3]
def baseStart_1826205 : Nat := 118140960795 + 1826205 * 2 ^ 59
def prefixEnd_1826205 : Nat := 4983230072969 + 3 ^ 40 * 1826205 * 2
def baseEnd_1826205 : Nat := 416764861619614532550641

theorem tailTrace_1826205 : CollatzResearch.WordTrace tailWord_1826205 prefixEnd_1826205 416764861619614532550641 := by
  unfold tailWord_1826205
  simp only [CollatzResearch.WordTrace]
  refine ⟨66607168348978650828200069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44404778899319100552133379 66607168348978650828200069)
  ·
    refine ⟨12488844065433497030287513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66607168348978650828200069 12488844065433497030287513)
    ·
      refine ⟨9366633049075122772715635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12488844065433497030287513 9366633049075122772715635)
      ·
        refine ⟨14049949573612684159073453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9366633049075122772715635 14049949573612684159073453)
        ·
          refine ⟨5268731090104756559652545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14049949573612684159073453 5268731090104756559652545)
          ·
            refine ⟨3951548317578567419739409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5268731090104756559652545 3951548317578567419739409)
            ·
              refine ⟨2963661238183925564804557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951548317578567419739409 2963661238183925564804557)
              ·
                refine ⟨1111372964318972086801709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2963661238183925564804557 1111372964318972086801709)
                ·
                  refine ⟨416764861619614532550641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111372964318972086801709 416764861619614532550641)
                  ·
                    rfl

theorem cell21_1826205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_1826205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826205 prefixEnd_1826205 := by exact prefixLift 1826205
  have htrace : WordTrace (prefixWord ++ tailWord_1826205) baseStart_1826205 baseEnd_1826205 := by
    simpa [prefixWord, tailWord_1826205, baseEnd_1826205] using wordTrace_append hprefix tailTrace_1826205
  have hstable : (prefixWord ++ tailWord_1826205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826205).length < 2 ^ (prefixWord ++ tailWord_1826205).sum := by decide
  have hdescent : baseEnd_1826205 < baseStart_1826205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826236 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_1826236 : Nat := 118140960795 + 1826236 * 2 ^ 59
def prefixEnd_1826236 : Nat := 4983230072969 + 3 ^ 40 * 1826236 * 2
def baseEnd_1826236 : Nat := 416771936241965367533911

theorem tailTrace_1826236 : CollatzResearch.WordTrace tailWord_1826236 prefixEnd_1826236 416771936241965367533911 := by
  unfold tailWord_1826236
  simp only [CollatzResearch.WordTrace]
  refine ⟨33304149505933171561289281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44405532674577562081719041 33304149505933171561289281)
  ·
    refine ⟨24978112129449878670966961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33304149505933171561289281 24978112129449878670966961)
    ·
      refine ⟨18733584097087409003225221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24978112129449878670966961 18733584097087409003225221)
      ·
        refine ⟨3512547018203889188104729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18733584097087409003225221 3512547018203889188104729)
        ·
          refine ⟨2634410263652916891078547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3512547018203889188104729 2634410263652916891078547)
          ·
            refine ⟨3951615395479375336617821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634410263652916891078547 3951615395479375336617821)
            ·
              refine ⟨1481855773304765751231683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3951615395479375336617821 1481855773304765751231683)
              ·
                refine ⟨2222783659957148626847525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1481855773304765751231683 2222783659957148626847525)
                ·
                  refine ⟨416771936241965367533911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2222783659957148626847525 416771936241965367533911)
                  ·
                    rfl

theorem cell21_1826236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_1826236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826236 prefixEnd_1826236 := by exact prefixLift 1826236
  have htrace : WordTrace (prefixWord ++ tailWord_1826236) baseStart_1826236 baseEnd_1826236 := by
    simpa [prefixWord, tailWord_1826236, baseEnd_1826236] using wordTrace_append hprefix tailTrace_1826236
  have hstable : (prefixWord ++ tailWord_1826236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826236).length < 2 ^ (prefixWord ++ tailWord_1826236).sum := by decide
  have hdescent : baseEnd_1826236 < baseStart_1826236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826242 : List Nat := [3, 5, 2, 1, 2, 1, 2, 5]
def baseStart_1826242 : Nat := 118140960795 + 1826242 * 2 ^ 59
def prefixEnd_1826242 : Nat := 4983230072969 + 3 ^ 40 * 1826242 * 2
def baseEnd_1826242 : Nat := 138924435174570230144633

theorem tailTrace_1826242 : CollatzResearch.WordTrace tailWord_1826242 prefixEnd_1826242 138924435174570230144633 := by
  unfold tailWord_1826242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16652129462461151536824245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44405678566563070764864653 16652129462461151536824245)
  ·
    refine ⟨1561137137105732956577273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16652129462461151536824245 1561137137105732956577273)
    ·
      refine ⟨1170852852829299717432955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1561137137105732956577273 1170852852829299717432955)
      ·
        refine ⟨1756279279243949576149433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1170852852829299717432955 1756279279243949576149433)
        ·
          refine ⟨1317209459432962182112075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756279279243949576149433 1317209459432962182112075)
          ·
            refine ⟨1975814189149443273168113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317209459432962182112075 1975814189149443273168113)
            ·
              refine ⟨1481860641862082454876085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1975814189149443273168113 1481860641862082454876085)
              ·
                refine ⟨138924435174570230144633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1481860641862082454876085 138924435174570230144633)
                ·
                  rfl

theorem cell21_1826242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_1826242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826242 prefixEnd_1826242 := by exact prefixLift 1826242
  have htrace : WordTrace (prefixWord ++ tailWord_1826242) baseStart_1826242 baseEnd_1826242 := by
    simpa [prefixWord, tailWord_1826242, baseEnd_1826242] using wordTrace_append hprefix tailTrace_1826242
  have hstable : (prefixWord ++ tailWord_1826242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826242).length < 2 ^ (prefixWord ++ tailWord_1826242).sum := by decide
  have hdescent : baseEnd_1826242 < baseStart_1826242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826261 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 8]
def baseStart_1826261 : Nat := 118140960795 + 1826261 * 2 ^ 59
def prefixEnd_1826261 : Nat := 4983230072969 + 3 ^ 40 * 1826261 * 2
def baseEnd_1826261 : Nat := 416777641582570879617193

theorem tailTrace_1826261 : CollatzResearch.WordTrace tailWord_1826261 prefixEnd_1826261 416777641582570879617193 := by
  unfold tailWord_1826261
  simp only [CollatzResearch.WordTrace]
  refine ⟨66609210836775772392238637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44406140557850514928159091 66609210836775772392238637)
  ·
    refine ⟨24978454063790914647089489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66609210836775772392238637 24978454063790914647089489)
    ·
      refine ⟨18733840547843185985317117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24978454063790914647089489 18733840547843185985317117)
      ·
        refine ⟨7025190205441194744493919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18733840547843185985317117 7025190205441194744493919)
        ·
          refine ⟨10537785308161792116740879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025190205441194744493919 10537785308161792116740879)
          ·
            refine ⟨15806677962242688175111319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10537785308161792116740879 15806677962242688175111319)
            ·
              refine ⟨23710016943364032262666979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15806677962242688175111319 23710016943364032262666979)
              ·
                refine ⟨35565025415046048394000469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23710016943364032262666979 35565025415046048394000469)
                ·
                  refine ⟨416777641582570879617193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35565025415046048394000469 416777641582570879617193)
                  ·
                    rfl

theorem cell21_1826261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_1826261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826261 prefixEnd_1826261 := by exact prefixLift 1826261
  have htrace : WordTrace (prefixWord ++ tailWord_1826261) baseStart_1826261 baseEnd_1826261 := by
    simpa [prefixWord, tailWord_1826261, baseEnd_1826261] using wordTrace_append hprefix tailTrace_1826261
  have hstable : (prefixWord ++ tailWord_1826261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826261).length < 2 ^ (prefixWord ++ tailWord_1826261).sum := by decide
  have hdescent : baseEnd_1826261 < baseStart_1826261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826264 : List Nat := [2, 1, 2, 2, 2, 1, 5, 3, 3]
def baseStart_1826264 : Nat := 118140960795 + 1826264 * 2 ^ 59
def prefixEnd_1826264 : Nat := 4983230072969 + 3 ^ 40 * 1826264 * 2
def baseEnd_1826264 : Nat := 416778326223443541067187

theorem tailTrace_1826264 : CollatzResearch.WordTrace tailWord_1826264 prefixEnd_1826264 416778326223443541067187 := by
  unfold tailWord_1826264
  simp only [CollatzResearch.WordTrace]
  refine ⟨33304660127882451952298923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44406213503843269269731897 33304660127882451952298923)
  ·
    refine ⟨49956990191823677928448385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33304660127882451952298923 49956990191823677928448385)
    ·
      refine ⟨37467742643867758446336289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49956990191823677928448385 37467742643867758446336289)
      ·
        refine ⟨28100806982900818834752217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37467742643867758446336289 28100806982900818834752217)
        ·
          refine ⟨21075605237175614126064163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28100806982900818834752217 21075605237175614126064163)
          ·
            refine ⟨31613407855763421189096245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21075605237175614126064163 31613407855763421189096245)
            ·
              refine ⟨2963756986477820736477773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31613407855763421189096245 2963756986477820736477773)
              ·
                refine ⟨1111408869929182776179165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2963756986477820736477773 1111408869929182776179165)
                ·
                  refine ⟨416778326223443541067187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111408869929182776179165 416778326223443541067187)
                  ·
                    rfl

theorem cell21_1826264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 3].length) (baseStart_1826264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826264 prefixEnd_1826264 := by exact prefixLift 1826264
  have htrace : WordTrace (prefixWord ++ tailWord_1826264) baseStart_1826264 baseEnd_1826264 := by
    simpa [prefixWord, tailWord_1826264, baseEnd_1826264] using wordTrace_append hprefix tailTrace_1826264
  have hstable : (prefixWord ++ tailWord_1826264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826264).length < 2 ^ (prefixWord ++ tailWord_1826264).sum := by decide
  have hdescent : baseEnd_1826264 < baseStart_1826264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826382 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1826382 : Nat := 118140960795 + 1826382 * 2 ^ 59
def prefixEnd_1826382 : Nat := 4983230072969 + 3 ^ 40 * 1826382 * 2
def baseEnd_1826382 : Nat := 416805255431101558100279

theorem tailTrace_1826382 : CollatzResearch.WordTrace tailWord_1826382 prefixEnd_1826382 416805255431101558100279 := by
  unfold tailWord_1826382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8326703008667176257174175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44409082712891606704928933 8326703008667176257174175)
  ·
    refine ⟨12490054513000764385761263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8326703008667176257174175 12490054513000764385761263)
    ·
      refine ⟨18735081769501146578641895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12490054513000764385761263 18735081769501146578641895)
      ·
        refine ⟨28102622654251719867962843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18735081769501146578641895 28102622654251719867962843)
        ·
          refine ⟨42153933981377579801944265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28102622654251719867962843 42153933981377579801944265)
          ·
            refine ⟨31615450486033184851458199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42153933981377579801944265 31615450486033184851458199)
            ·
              refine ⟨47423175729049777277187299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31615450486033184851458199 47423175729049777277187299)
              ·
                refine ⟨71134763593574665915780949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47423175729049777277187299 71134763593574665915780949)
                ·
                  refine ⟨416805255431101558100279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71134763593574665915780949 416805255431101558100279)
                  ·
                    rfl

theorem cell21_1826382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1826382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826382 prefixEnd_1826382 := by exact prefixLift 1826382
  have htrace : WordTrace (prefixWord ++ tailWord_1826382) baseStart_1826382 baseEnd_1826382 := by
    simpa [prefixWord, tailWord_1826382, baseEnd_1826382] using wordTrace_append hprefix tailTrace_1826382
  have hstable : (prefixWord ++ tailWord_1826382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826382).length < 2 ^ (prefixWord ++ tailWord_1826382).sum := by decide
  have hdescent : baseEnd_1826382 < baseStart_1826382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826427 : List Nat := [1, 1, 1, 1, 1, 4, 5, 7]
def baseStart_1826427 : Nat := 118140960795 + 1826427 * 2 ^ 59
def prefixEnd_1826427 : Nat := 4983230072969 + 3 ^ 40 * 1826427 * 2
def baseEnd_1826427 : Nat := 138938508348063826616729

theorem tailTrace_1826427 : CollatzResearch.WordTrace tailWord_1826427 prefixEnd_1826427 138938508348063826616729 := by
  unfold tailWord_1826427
  simp only [CollatzResearch.WordTrace]
  refine ⟨66615265354174382742781535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44410176902782921828521023 66615265354174382742781535)
  ·
    refine ⟨99922898031261574114172303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66615265354174382742781535 99922898031261574114172303)
    ·
      refine ⟨149884347046892361171258455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99922898031261574114172303 149884347046892361171258455)
      ·
        refine ⟨224826520570338541756887683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149884347046892361171258455 224826520570338541756887683)
        ·
          refine ⟨337239780855507812635331525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224826520570338541756887683 337239780855507812635331525)
          ·
            refine ⟨63232458910407714869124661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337239780855507812635331525 63232458910407714869124661)
            ·
              refine ⟨5928043022850723268980437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63232458910407714869124661 5928043022850723268980437)
              ·
                refine ⟨138938508348063826616729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5928043022850723268980437 138938508348063826616729)
                ·
                  rfl

theorem cell21_1826427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 7].length) (baseStart_1826427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826427 prefixEnd_1826427 := by exact prefixLift 1826427
  have htrace : WordTrace (prefixWord ++ tailWord_1826427) baseStart_1826427 baseEnd_1826427 := by
    simpa [prefixWord, tailWord_1826427, baseEnd_1826427] using wordTrace_append hprefix tailTrace_1826427
  have hstable : (prefixWord ++ tailWord_1826427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826427).length < 2 ^ (prefixWord ++ tailWord_1826427).sum := by decide
  have hdescent : baseEnd_1826427 < baseStart_1826427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826433 : List Nat := [1, 2, 4, 2, 1, 4, 1, 3, 3]
def baseStart_1826433 : Nat := 118140960795 + 1826433 * 2 ^ 59
def prefixEnd_1826433 : Nat := 4983230072969 + 3 ^ 40 * 1826433 * 2
def baseEnd_1826433 : Nat := 416816894325936802750175

theorem tailTrace_1826433 : CollatzResearch.WordTrace tailWord_1826433 prefixEnd_1826433 416816894325936802750175 := by
  unfold tailWord_1826433
  simp only [CollatzResearch.WordTrace]
  refine ⟨66615484192152645767499953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44410322794768430511666635 66615484192152645767499953)
  ·
    refine ⟨49961613144114484325624965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66615484192152645767499953 49961613144114484325624965)
    ·
      refine ⟨9367802464521465811054681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49961613144114484325624965 9367802464521465811054681)
      ·
        refine ⟨7025851848391099358291011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9367802464521465811054681 7025851848391099358291011)
        ·
          refine ⟨10538777772586649037436517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025851848391099358291011 10538777772586649037436517)
          ·
            refine ⟨1976020832359996694519347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10538777772586649037436517 1976020832359996694519347)
            ·
              refine ⟨2964031248539995041779021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976020832359996694519347 2964031248539995041779021)
              ·
                refine ⟨1111511718202498140667133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2964031248539995041779021 1111511718202498140667133)
                ·
                  refine ⟨416816894325936802750175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111511718202498140667133 416816894325936802750175)
                  ·
                    rfl

theorem cell21_1826433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_1826433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826433 prefixEnd_1826433 := by exact prefixLift 1826433
  have htrace : WordTrace (prefixWord ++ tailWord_1826433) baseStart_1826433 baseEnd_1826433 := by
    simpa [prefixWord, tailWord_1826433, baseEnd_1826433] using wordTrace_append hprefix tailTrace_1826433
  have hstable : (prefixWord ++ tailWord_1826433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826433).length < 2 ^ (prefixWord ++ tailWord_1826433).sum := by decide
  have hdescent : baseEnd_1826433 < baseStart_1826433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826450 : List Nat := [3, 2, 3, 1, 3, 1, 3, 2, 3]
def baseStart_1826450 : Nat := 118140960795 + 1826450 * 2 ^ 59
def prefixEnd_1826450 : Nat := 4983230072969 + 3 ^ 40 * 1826450 * 2
def baseEnd_1826450 : Nat := 416820773957548550966807

theorem tailTrace_1826450 : CollatzResearch.WordTrace tailWord_1826450 prefixEnd_1826450 416820773957548550966807 := by
  unfold tailWord_1826450
  simp only [CollatzResearch.WordTrace]
  refine ⟨16654026058272764417717201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44410736155394038447245869 16654026058272764417717201)
  ·
    refine ⟨12490519543704573313287901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16654026058272764417717201 12490519543704573313287901)
    ·
      refine ⟨4683944828889214992482963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12490519543704573313287901 4683944828889214992482963)
      ·
        refine ⟨7025917243333822488724445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683944828889214992482963 7025917243333822488724445)
        ·
          refine ⟨2634718966250183433271667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7025917243333822488724445 2634718966250183433271667)
          ·
            refine ⟨3952078449375275149907501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634718966250183433271667 3952078449375275149907501)
            ·
              refine ⟨1482029418515728181215313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3952078449375275149907501 1482029418515728181215313)
              ·
                refine ⟨1111522063886796135911485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1482029418515728181215313 1111522063886796135911485)
                ·
                  refine ⟨416820773957548550966807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111522063886796135911485 416820773957548550966807)
                  ·
                    rfl

theorem cell21_1826450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_1826450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826450 prefixEnd_1826450 := by exact prefixLift 1826450
  have htrace : WordTrace (prefixWord ++ tailWord_1826450) baseStart_1826450 baseEnd_1826450 := by
    simpa [prefixWord, tailWord_1826450, baseEnd_1826450] using wordTrace_append hprefix tailTrace_1826450
  have hstable : (prefixWord ++ tailWord_1826450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826450).length < 2 ^ (prefixWord ++ tailWord_1826450).sum := by decide
  have hdescent : baseEnd_1826450 < baseStart_1826450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826551 : List Nat := [1, 1, 3, 1, 1, 1, 5, 5, 3]
def baseStart_1826551 : Nat := 118140960795 + 1826551 * 2 ^ 59
def prefixEnd_1826551 : Nat := 4983230072969 + 3 ^ 40 * 1826551 * 2
def baseEnd_1826551 : Nat := 416843823533594819783267

theorem tailTrace_1826551 : CollatzResearch.WordTrace tailWord_1826551 prefixEnd_1826551 416843823533594819783267 := by
  unfold tailWord_1826551
  simp only [CollatzResearch.WordTrace]
  refine ⟨66619788005725151920295507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44413192003816767946863671 66619788005725151920295507)
  ·
    refine ⟨99929682008587727880443261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66619788005725151920295507 99929682008587727880443261)
    ·
      refine ⟨37473630753220397955166223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99929682008587727880443261 37473630753220397955166223)
      ·
        refine ⟨56210446129830596932749335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37473630753220397955166223 56210446129830596932749335)
        ·
          refine ⟨84315669194745895399124003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56210446129830596932749335 84315669194745895399124003)
          ·
            refine ⟨126473503792118843098686005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84315669194745895399124003 126473503792118843098686005)
            ·
              refine ⟨11856890980511141540501813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126473503792118843098686005 11856890980511141540501813)
              ·
                refine ⟨1111583529422919519422045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11856890980511141540501813 1111583529422919519422045)
                ·
                  refine ⟨416843823533594819783267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111583529422919519422045 416843823533594819783267)
                  ·
                    rfl

theorem cell21_1826551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 3].length) (baseStart_1826551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826551 prefixEnd_1826551 := by exact prefixLift 1826551
  have htrace : WordTrace (prefixWord ++ tailWord_1826551) baseStart_1826551 baseEnd_1826551 := by
    simpa [prefixWord, tailWord_1826551, baseEnd_1826551] using wordTrace_append hprefix tailTrace_1826551
  have hstable : (prefixWord ++ tailWord_1826551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826551).length < 2 ^ (prefixWord ++ tailWord_1826551).sum := by decide
  have hdescent : baseEnd_1826551 < baseStart_1826551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826596 : List Nat := [2, 3, 1, 3, 2, 2, 1, 7]
def baseStart_1826596 : Nat := 118140960795 + 1826596 * 2 ^ 59
def prefixEnd_1826596 : Nat := 4983230072969 + 3 ^ 40 * 1826596 * 2
def baseEnd_1826596 : Nat := 138951364382228247177725

theorem tailTrace_1826596 : CollatzResearch.WordTrace tailWord_1826596 prefixEnd_1826596 138951364382228247177725 := by
  unfold tailWord_1826596
  simp only [CollatzResearch.WordTrace]
  refine ⟨33310714645281062302841821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44414286193708083070455761 33310714645281062302841821)
  ·
    refine ⟨12491517991980398363565683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33310714645281062302841821 12491517991980398363565683)
    ·
      refine ⟨18737276987970597545348525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12491517991980398363565683 18737276987970597545348525)
      ·
        refine ⟨7026478870488974079505697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18737276987970597545348525 7026478870488974079505697)
        ·
          refine ⟨5269859152866730559629273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7026478870488974079505697 5269859152866730559629273)
          ·
            refine ⟨3952394364650047919721955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269859152866730559629273 3952394364650047919721955)
            ·
              refine ⟨5928591546975071879582933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952394364650047919721955 5928591546975071879582933)
              ·
                refine ⟨138951364382228247177725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5928591546975071879582933 138951364382228247177725)
                ·
                  rfl

theorem cell21_1826596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_1826596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826596 prefixEnd_1826596 := by exact prefixLift 1826596
  have htrace : WordTrace (prefixWord ++ tailWord_1826596) baseStart_1826596 baseEnd_1826596 := by
    simpa [prefixWord, tailWord_1826596, baseEnd_1826596] using wordTrace_append hprefix tailTrace_1826596
  have hstable : (prefixWord ++ tailWord_1826596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826596).length < 2 ^ (prefixWord ++ tailWord_1826596).sum := by decide
  have hdescent : baseEnd_1826596 < baseStart_1826596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826613 : List Nat := [1, 3, 3, 1, 5, 1, 7]
def baseStart_1826613 : Nat := 118140960795 + 1826613 * 2 ^ 59
def prefixEnd_1826613 : Nat := 4983230072969 + 3 ^ 40 * 1826613 * 2
def baseEnd_1826613 : Nat := 46317552530921832194423

theorem tailTrace_1826613 : CollatzResearch.WordTrace tailWord_1826613 prefixEnd_1826613 46317552530921832194423 := by
  unfold tailWord_1826613
  simp only [CollatzResearch.WordTrace]
  refine ⟨66622049331500536509052493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44414699554333691006034995 66622049331500536509052493)
  ·
    refine ⟨24983268499312701190894685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66622049331500536509052493 24983268499312701190894685)
    ·
      refine ⟨9368725687242262946585507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24983268499312701190894685 9368725687242262946585507)
      ·
        refine ⟨14053088530863394419878261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9368725687242262946585507 14053088530863394419878261)
        ·
          refine ⟨1317477049768443226863587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14053088530863394419878261 1317477049768443226863587)
          ·
            refine ⟨1976215574652664840295381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317477049768443226863587 1976215574652664840295381)
            ·
              refine ⟨46317552530921832194423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1976215574652664840295381 46317552530921832194423)
              ·
                rfl

theorem cell21_1826613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 7].length) (baseStart_1826613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826613 prefixEnd_1826613 := by exact prefixLift 1826613
  have htrace : WordTrace (prefixWord ++ tailWord_1826613) baseStart_1826613 baseEnd_1826613 := by
    simpa [prefixWord, tailWord_1826613, baseEnd_1826613] using wordTrace_append hprefix tailTrace_1826613
  have hstable : (prefixWord ++ tailWord_1826613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826613).length < 2 ^ (prefixWord ++ tailWord_1826613).sum := by decide
  have hdescent : baseEnd_1826613 < baseStart_1826613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826627 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 5]
def baseStart_1826627 : Nat := 118140960795 + 1826627 * 2 ^ 59
def prefixEnd_1826627 : Nat := 4983230072969 + 3 ^ 40 * 1826627 * 2
def baseEnd_1826627 : Nat := 416861167769035576516445

theorem tailTrace_1826627 : CollatzResearch.WordTrace tailWord_1826627 prefixEnd_1826627 416861167769035576516445 := by
  unfold tailWord_1826627
  simp only [CollatzResearch.WordTrace]
  refine ⟨66622559953449816900062135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44415039968966544600041423 66622559953449816900062135)
  ·
    refine ⟨99933839930174725350093203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66622559953449816900062135 99933839930174725350093203)
    ·
      refine ⟨149900759895262088025139805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99933839930174725350093203 149900759895262088025139805)
      ·
        refine ⟨56212784960723283009427427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149900759895262088025139805 56212784960723283009427427)
        ·
          refine ⟨84319177441084924514141141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56212784960723283009427427 84319177441084924514141141)
          ·
            refine ⟨1976230721275427918300183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 84319177441084924514141141 1976230721275427918300183)
            ·
              refine ⟨2964346081913141877450275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1976230721275427918300183 2964346081913141877450275)
              ·
                refine ⟨4446519122869712816175413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964346081913141877450275 4446519122869712816175413)
                ·
                  refine ⟨416861167769035576516445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4446519122869712816175413 416861167769035576516445)
                  ·
                    rfl

theorem cell21_1826627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 5].length) (baseStart_1826627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826627 prefixEnd_1826627 := by exact prefixLift 1826627
  have htrace : WordTrace (prefixWord ++ tailWord_1826627) baseStart_1826627 baseEnd_1826627 := by
    simpa [prefixWord, tailWord_1826627, baseEnd_1826627] using wordTrace_append hprefix tailTrace_1826627
  have hstable : (prefixWord ++ tailWord_1826627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826627).length < 2 ^ (prefixWord ++ tailWord_1826627).sum := by decide
  have hdescent : baseEnd_1826627 < baseStart_1826627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826630 : List Nat := [6, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1826630 : Nat := 118140960795 + 1826630 * 2 ^ 59
def prefixEnd_1826630 : Nat := 4983230072969 + 3 ^ 40 * 1826630 * 2
def baseEnd_1826630 : Nat := 138953950803302745988813

theorem tailTrace_1826630 : CollatzResearch.WordTrace tailWord_1826630 prefixEnd_1826630 138953950803302745988813 := by
  unfold tailWord_1826630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081958417888717137888167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44415112914959298941614229 2081958417888717137888167)
  ·
    refine ⟨3122937626833075706832251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081958417888717137888167 3122937626833075706832251)
    ·
      refine ⟨4684406440249613560248377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3122937626833075706832251 4684406440249613560248377)
      ·
        refine ⟨3513304830187210170186283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4684406440249613560248377 3513304830187210170186283)
        ·
          refine ⟨5269957245280815255279425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513304830187210170186283 5269957245280815255279425)
          ·
            refine ⟨3952467933960611441459569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269957245280815255279425 3952467933960611441459569)
            ·
              refine ⟨2964350950470458581094677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3952467933960611441459569 2964350950470458581094677)
              ·
                refine ⟨138953950803302745988813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2964350950470458581094677 138953950803302745988813)
                ·
                  rfl

theorem cell21_1826630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1826630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826630 prefixEnd_1826630 := by exact prefixLift 1826630
  have htrace : WordTrace (prefixWord ++ tailWord_1826630) baseStart_1826630 baseEnd_1826630 := by
    simpa [prefixWord, tailWord_1826630, baseEnd_1826630] using wordTrace_append hprefix tailTrace_1826630
  have hstable : (prefixWord ++ tailWord_1826630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826630).length < 2 ^ (prefixWord ++ tailWord_1826630).sum := by decide
  have hdescent : baseEnd_1826630 < baseStart_1826630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826655 : List Nat := [1, 1, 2, 3, 1, 4, 2, 7]
def baseStart_1826655 : Nat := 118140960795 + 1826655 * 2 ^ 59
def prefixEnd_1826655 : Nat := 4983230072969 + 3 ^ 40 * 1826655 * 2
def baseEnd_1826655 : Nat := 138955852583504583349907

theorem tailTrace_1826655 : CollatzResearch.WordTrace tailWord_1826655 prefixEnd_1826655 138955852583504583349907 := by
  unfold tailWord_1826655
  simp only [CollatzResearch.WordTrace]
  refine ⟨66623581197348377682081419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44415720798232251788054279 66623581197348377682081419)
  ·
    refine ⟨99935371796022566523122129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66623581197348377682081419 99935371796022566523122129)
    ·
      refine ⟨74951528847016924892341597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99935371796022566523122129 74951528847016924892341597)
      ·
        refine ⟨28106823317631346834628099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74951528847016924892341597 28106823317631346834628099)
        ·
          refine ⟨42160234976447020251942149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28106823317631346834628099 42160234976447020251942149)
          ·
            refine ⟨7905044058083816297239153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42160234976447020251942149 7905044058083816297239153)
            ·
              refine ⟨5928783043562862222929365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7905044058083816297239153 5928783043562862222929365)
              ·
                refine ⟨138955852583504583349907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5928783043562862222929365 138955852583504583349907)
                ·
                  rfl

theorem cell21_1826655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 7].length) (baseStart_1826655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826655 prefixEnd_1826655 := by exact prefixLift 1826655
  have htrace : WordTrace (prefixWord ++ tailWord_1826655) baseStart_1826655 baseEnd_1826655 := by
    simpa [prefixWord, tailWord_1826655, baseEnd_1826655] using wordTrace_append hprefix tailTrace_1826655
  have hstable : (prefixWord ++ tailWord_1826655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826655).length < 2 ^ (prefixWord ++ tailWord_1826655).sum := by decide
  have hdescent : baseEnd_1826655 < baseStart_1826655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826700 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_1826700 : Nat := 118140960795 + 1826700 * 2 ^ 59
def prefixEnd_1826700 : Nat := 4983230072969 + 3 ^ 40 * 1826700 * 2
def baseEnd_1826700 : Nat := 416877827363603671799629

theorem tailTrace_1826700 : CollatzResearch.WordTrace tailWord_1826700 prefixEnd_1826700 416877827363603671799629 := by
  unfold tailWord_1826700
  simp only [CollatzResearch.WordTrace]
  refine ⟨33312611241092675183734777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44416814988123566911646369 33312611241092675183734777)
  ·
    refine ⟨24984458430819506387801083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33312611241092675183734777 24984458430819506387801083)
    ·
      refine ⟨37476687646229259581701625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24984458430819506387801083 37476687646229259581701625)
      ·
        refine ⟨28107515734671944686276219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37476687646229259581701625 28107515734671944686276219)
        ·
          refine ⟨42161273602007917029414329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28107515734671944686276219 42161273602007917029414329)
          ·
            refine ⟨31620955201505937772060747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42161273602007917029414329 31620955201505937772060747)
            ·
              refine ⟨47431432802258906658091121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31620955201505937772060747 47431432802258906658091121)
              ·
                refine ⟨35573574601694179993568341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47431432802258906658091121 35573574601694179993568341)
                ·
                  refine ⟨416877827363603671799629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35573574601694179993568341 416877827363603671799629)
                  ·
                    rfl

theorem cell21_1826700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_1826700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826700 prefixEnd_1826700 := by exact prefixLift 1826700
  have htrace : WordTrace (prefixWord ++ tailWord_1826700) baseStart_1826700 baseEnd_1826700 := by
    simpa [prefixWord, tailWord_1826700, baseEnd_1826700] using wordTrace_append hprefix tailTrace_1826700
  have hstable : (prefixWord ++ tailWord_1826700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826700).length < 2 ^ (prefixWord ++ tailWord_1826700).sum := by decide
  have hdescent : baseEnd_1826700 < baseStart_1826700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826762 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_1826762 : Nat := 118140960795 + 1826762 * 2 ^ 59
def prefixEnd_1826762 : Nat := 4983230072969 + 3 ^ 40 * 1826762 * 2
def baseEnd_1826762 : Nat := 416891976608305341766169

theorem tailTrace_1826762 : CollatzResearch.WordTrace tailWord_1826762 prefixEnd_1826762 416891976608305341766169 := by
  unfold tailWord_1826762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16656870951990183739056635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44418322538640489970817693 16656870951990183739056635)
  ·
    refine ⟨24985306427985275608584953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16656870951990183739056635 24985306427985275608584953)
    ·
      refine ⟨18738979820988956706438715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24985306427985275608584953 18738979820988956706438715)
      ·
        refine ⟨28108469731483435059658073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18738979820988956706438715 28108469731483435059658073)
        ·
          refine ⟨21081352298612576294743555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28108469731483435059658073 21081352298612576294743555)
          ·
            refine ⟨31622028447918864442115333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21081352298612576294743555 31622028447918864442115333)
            ·
              refine ⟨5929130333984787082896625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31622028447918864442115333 5929130333984787082896625)
              ·
                refine ⟨4446847750488590312172469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5929130333984787082896625 4446847750488590312172469)
                ·
                  refine ⟨416891976608305341766169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4446847750488590312172469 416891976608305341766169)
                  ·
                    rfl

theorem cell21_1826762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_1826762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826762 prefixEnd_1826762 := by exact prefixLift 1826762
  have htrace : WordTrace (prefixWord ++ tailWord_1826762) baseStart_1826762 baseEnd_1826762 := by
    simpa [prefixWord, tailWord_1826762, baseEnd_1826762] using wordTrace_append hprefix tailTrace_1826762
  have hstable : (prefixWord ++ tailWord_1826762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826762).length < 2 ^ (prefixWord ++ tailWord_1826762).sum := by decide
  have hdescent : baseEnd_1826762 < baseStart_1826762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826776 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_1826776 : Nat := 118140960795 + 1826776 * 2 ^ 59
def prefixEnd_1826776 : Nat := 4983230072969 + 3 ^ 40 * 1826776 * 2
def baseEnd_1826776 : Nat := 416895171599044428532807

theorem tailTrace_1826776 : CollatzResearch.WordTrace tailWord_1826776 prefixEnd_1826776 416895171599044428532807 := by
  unfold tailWord_1826776
  simp only [CollatzResearch.WordTrace]
  refine ⟨33313997214955007673618091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44418662953273343564824121 33313997214955007673618091)
  ·
    refine ⟨49970995822432511510427137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33313997214955007673618091 49970995822432511510427137)
    ·
      refine ⟨37478246866824383632820353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49970995822432511510427137 37478246866824383632820353)
      ·
        refine ⟨28108685150118287724615265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37478246866824383632820353 28108685150118287724615265)
        ·
          refine ⟨21081513862588715793461449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28108685150118287724615265 21081513862588715793461449)
          ·
            refine ⟨15811135396941536845096087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21081513862588715793461449 15811135396941536845096087)
            ·
              refine ⟨23716703095412305267644131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15811135396941536845096087 23716703095412305267644131)
              ·
                refine ⟨35575054643118457901466197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23716703095412305267644131 35575054643118457901466197)
                ·
                  refine ⟨416895171599044428532807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35575054643118457901466197 416895171599044428532807)
                  ·
                    rfl

theorem cell21_1826776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_1826776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826776 prefixEnd_1826776 := by exact prefixLift 1826776
  have htrace : WordTrace (prefixWord ++ tailWord_1826776) baseStart_1826776 baseEnd_1826776 := by
    simpa [prefixWord, tailWord_1826776, baseEnd_1826776] using wordTrace_append hprefix tailTrace_1826776
  have hstable : (prefixWord ++ tailWord_1826776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826776).length < 2 ^ (prefixWord ++ tailWord_1826776).sum := by decide
  have hdescent : baseEnd_1826776 < baseStart_1826776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826869 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 4]
def baseStart_1826869 : Nat := 118140960795 + 1826869 * 2 ^ 59
def prefixEnd_1826869 : Nat := 4983230072969 + 3 ^ 40 * 1826869 * 2
def baseEnd_1826869 : Nat := 416916395466096933482617

theorem tailTrace_1826869 : CollatzResearch.WordTrace tailWord_1826869 prefixEnd_1826869 416916395466096933482617 := by
  unfold tailWord_1826869
  simp only [CollatzResearch.WordTrace]
  refine ⟨66631386418573092230371661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44420924279048728153581107 66631386418573092230371661)
  ·
    refine ⟨24986769906964909586389373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66631386418573092230371661 24986769906964909586389373)
    ·
      refine ⟨9370038715111841094896015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24986769906964909586389373 9370038715111841094896015)
      ·
        refine ⟨14055058072667761642344023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9370038715111841094896015 14055058072667761642344023)
        ·
          refine ⟨21082587109001642463516035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14055058072667761642344023 21082587109001642463516035)
          ·
            refine ⟨31623880663502463695274053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21082587109001642463516035 31623880663502463695274053)
            ·
              refine ⟨5929477624406711942863885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31623880663502463695274053 5929477624406711942863885)
              ·
                refine ⟨2223554109152516978573957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5929477624406711942863885 2223554109152516978573957)
                ·
                  refine ⟨416916395466096933482617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2223554109152516978573957 416916395466096933482617)
                  ·
                    rfl

theorem cell21_1826869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_1826869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826869 prefixEnd_1826869 := by exact prefixLift 1826869
  have htrace : WordTrace (prefixWord ++ tailWord_1826869) baseStart_1826869 baseEnd_1826869 := by
    simpa [prefixWord, tailWord_1826869, baseEnd_1826869] using wordTrace_append hprefix tailTrace_1826869
  have hstable : (prefixWord ++ tailWord_1826869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826869).length < 2 ^ (prefixWord ++ tailWord_1826869).sum := by decide
  have hdescent : baseEnd_1826869 < baseStart_1826869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826886 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1826886 : Nat := 118140960795 + 1826886 * 2 ^ 59
def prefixEnd_1826886 : Nat := 4983230072969 + 3 ^ 40 * 1826886 * 2
def baseEnd_1826886 : Nat := 416920275097708681699249

theorem tailTrace_1826886 : CollatzResearch.WordTrace tailWord_1826886 prefixEnd_1826886 416920275097708681699249 := by
  unfold tailWord_1826886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2082250201859734504179391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44421337639674336089160341 2082250201859734504179391)
  ·
    refine ⟨3123375302789601756269087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2082250201859734504179391 3123375302789601756269087)
    ·
      refine ⟨4685062954184402634403631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3123375302789601756269087 4685062954184402634403631)
      ·
        refine ⟨7027594431276603951605447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4685062954184402634403631 7027594431276603951605447)
        ·
          refine ⟨10541391646914905927408171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7027594431276603951605447 10541391646914905927408171)
          ·
            refine ⟨15812087470372358891112257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10541391646914905927408171 15812087470372358891112257)
            ·
              refine ⟨11859065602779269168334193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15812087470372358891112257 11859065602779269168334193)
              ·
                refine ⟨8894299202084451876250645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11859065602779269168334193 8894299202084451876250645)
                ·
                  refine ⟨416920275097708681699249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8894299202084451876250645 416920275097708681699249)
                  ·
                    rfl

theorem cell21_1826886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1826886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826886 prefixEnd_1826886 := by exact prefixLift 1826886
  have htrace : WordTrace (prefixWord ++ tailWord_1826886) baseStart_1826886 baseEnd_1826886 := by
    simpa [prefixWord, tailWord_1826886, baseEnd_1826886] using wordTrace_append hprefix tailTrace_1826886
  have hstable : (prefixWord ++ tailWord_1826886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826886).length < 2 ^ (prefixWord ++ tailWord_1826886).sum := by decide
  have hdescent : baseEnd_1826886 < baseStart_1826886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1826897 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 9]
def baseStart_1826897 : Nat := 118140960795 + 1826897 * 2 ^ 59
def prefixEnd_1826897 : Nat := 4983230072969 + 3 ^ 40 * 1826897 * 2
def baseEnd_1826897 : Nat := 416922785447575107015893

theorem tailTrace_1826897 : CollatzResearch.WordTrace tailWord_1826897 prefixEnd_1826897 416922785447575107015893 := by
  unfold tailWord_1826897
  simp only [CollatzResearch.WordTrace]
  refine ⟨66632407662471653012390945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44421605108314435341593963 66632407662471653012390945)
  ·
    refine ⟨49974305746853739759293209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66632407662471653012390945 49974305746853739759293209)
    ·
      refine ⟨37480729310140304819469907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49974305746853739759293209 37480729310140304819469907)
      ·
        refine ⟨56221093965210457229204861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37480729310140304819469907 56221093965210457229204861)
        ·
          refine ⟨21082910236953921460951823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56221093965210457229204861 21082910236953921460951823)
          ·
            refine ⟨31624365355430882191427735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21082910236953921460951823 31624365355430882191427735)
            ·
              refine ⟨47436548033146323287141603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31624365355430882191427735 47436548033146323287141603)
              ·
                refine ⟨71154822049719484930712405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47436548033146323287141603 71154822049719484930712405)
                ·
                  refine ⟨416922785447575107015893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71154822049719484930712405 416922785447575107015893)
                  ·
                    rfl

theorem cell21_1826897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_1826897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1826897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1826897 prefixEnd_1826897 := by exact prefixLift 1826897
  have htrace : WordTrace (prefixWord ++ tailWord_1826897) baseStart_1826897 baseEnd_1826897 := by
    simpa [prefixWord, tailWord_1826897, baseEnd_1826897] using wordTrace_append hprefix tailTrace_1826897
  have hstable : (prefixWord ++ tailWord_1826897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1826897).length < 2 ^ (prefixWord ++ tailWord_1826897).sum := by decide
  have hdescent : baseEnd_1826897 < baseStart_1826897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1826897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827049 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 5]
def baseStart_1827049 : Nat := 118140960795 + 1827049 * 2 ^ 59
def prefixEnd_1827049 : Nat := 4983230072969 + 3 ^ 40 * 1827049 * 2
def baseEnd_1827049 : Nat := 416957473918456620482249

theorem tailTrace_1827049 : CollatzResearch.WordTrace tailWord_1827049 prefixEnd_1827049 416957473918456620482249 := by
  unfold tailWord_1827049
  simp only [CollatzResearch.WordTrace]
  refine ⟨66637951557920982971924201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44425301038613988647949467 66637951557920982971924201)
  ·
    refine ⟨49978463668440737228943151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66637951557920982971924201 49978463668440737228943151)
    ·
      refine ⟨74967695502661105843414727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49978463668440737228943151 74967695502661105843414727)
      ·
        refine ⟨112451543253991658765122091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74967695502661105843414727 112451543253991658765122091)
        ·
          refine ⟨168677314880987488147683137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112451543253991658765122091 168677314880987488147683137)
          ·
            refine ⟨126507986160740616110762353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168677314880987488147683137 126507986160740616110762353)
            ·
              refine ⟨94880989620555462083071765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126507986160740616110762353 94880989620555462083071765)
              ·
                refine ⟨4447546388463537285143989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94880989620555462083071765 4447546388463537285143989)
                ·
                  refine ⟨416957473918456620482249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4447546388463537285143989 416957473918456620482249)
                  ·
                    rfl

theorem cell21_1827049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_1827049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827049 prefixEnd_1827049 := by exact prefixLift 1827049
  have htrace : WordTrace (prefixWord ++ tailWord_1827049) baseStart_1827049 baseEnd_1827049 := by
    simpa [prefixWord, tailWord_1827049, baseEnd_1827049] using wordTrace_append hprefix tailTrace_1827049
  have hstable : (prefixWord ++ tailWord_1827049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827049).length < 2 ^ (prefixWord ++ tailWord_1827049).sum := by decide
  have hdescent : baseEnd_1827049 < baseStart_1827049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827235 : List Nat := [1, 1, 1, 4, 1, 5, 2, 3, 3]
def baseStart_1827235 : Nat := 118140960795 + 1827235 * 2 ^ 59
def prefixEnd_1827235 : Nat := 4983230072969 + 3 ^ 40 * 1827235 * 2
def baseEnd_1827235 : Nat := 416999921652561630381869

theorem tailTrace_1827235 : CollatzResearch.WordTrace tailWord_1827235 prefixEnd_1827235 416999921652561630381869 := by
  unfold tailWord_1827235
  simp only [CollatzResearch.WordTrace]
  refine ⟨66644735535247136738195159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44429823690164757825463439 66644735535247136738195159)
  ·
    refine ⟨99967103302870705107292739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66644735535247136738195159 99967103302870705107292739)
    ·
      refine ⟨149950654954306057660939109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99967103302870705107292739 149950654954306057660939109)
      ·
        refine ⟨28115747803932385811426083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149950654954306057660939109 28115747803932385811426083)
        ·
          refine ⟨42173621705898578717139125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28115747803932385811426083 42173621705898578717139125)
          ·
            refine ⟨3953777034927991754731793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42173621705898578717139125 3953777034927991754731793)
            ·
              refine ⟨2965332776195993816048845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3953777034927991754731793 2965332776195993816048845)
              ·
                refine ⟨1111999791073497681018317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2965332776195993816048845 1111999791073497681018317)
                ·
                  refine ⟨416999921652561630381869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1111999791073497681018317 416999921652561630381869)
                  ·
                    rfl

theorem cell21_1827235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 3].length) (baseStart_1827235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827235 prefixEnd_1827235 := by exact prefixLift 1827235
  have htrace : WordTrace (prefixWord ++ tailWord_1827235) baseStart_1827235 baseEnd_1827235 := by
    simpa [prefixWord, tailWord_1827235, baseEnd_1827235] using wordTrace_append hprefix tailTrace_1827235
  have hstable : (prefixWord ++ tailWord_1827235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827235).length < 2 ^ (prefixWord ++ tailWord_1827235).sum := by decide
  have hdescent : baseEnd_1827235 < baseStart_1827235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827249 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 4]
def baseStart_1827249 : Nat := 118140960795 + 1827249 * 2 ^ 59
def prefixEnd_1827249 : Nat := 4983230072969 + 3 ^ 40 * 1827249 * 2
def baseEnd_1827249 : Nat := 417003116643300717148507

theorem tailTrace_1827249 : CollatzResearch.WordTrace tailWord_1827249 prefixEnd_1827249 417003116643300717148507 := by
  unfold tailWord_1827249
  simp only [CollatzResearch.WordTrace]
  refine ⟨66645246157196417129204801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44430164104797611419469867 66645246157196417129204801)
  ·
    refine ⟨49983934617897312846903601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66645246157196417129204801 49983934617897312846903601)
    ·
      refine ⟨37487950963422984635177701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49983934617897312846903601 37487950963422984635177701)
      ·
        refine ⟨7028990805641809619095819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37487950963422984635177701 7028990805641809619095819)
        ·
          refine ⟨10543486208462714428643729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7028990805641809619095819 10543486208462714428643729)
          ·
            refine ⟨7907614656347035821482797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10543486208462714428643729 7907614656347035821482797)
            ·
              refine ⟨2965355496130138433056049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7907614656347035821482797 2965355496130138433056049)
              ·
                refine ⟨2224016622097603824792037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965355496130138433056049 2224016622097603824792037)
                ·
                  refine ⟨417003116643300717148507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2224016622097603824792037 417003116643300717148507)
                  ·
                    rfl

theorem cell21_1827249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_1827249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827249 prefixEnd_1827249 := by exact prefixLift 1827249
  have htrace : WordTrace (prefixWord ++ tailWord_1827249) baseStart_1827249 baseEnd_1827249 := by
    simpa [prefixWord, tailWord_1827249, baseEnd_1827249] using wordTrace_append hprefix tailTrace_1827249
  have hstable : (prefixWord ++ tailWord_1827249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827249).length < 2 ^ (prefixWord ++ tailWord_1827249).sum := by decide
  have hdescent : baseEnd_1827249 < baseStart_1827249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827308 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 4]
def baseStart_1827308 : Nat := 118140960795 + 1827308 * 2 ^ 59
def prefixEnd_1827308 : Nat := 4983230072969 + 3 ^ 40 * 1827308 * 2
def baseEnd_1827308 : Nat := 417016581247129725665053

theorem tailTrace_1827308 : CollatzResearch.WordTrace tailWord_1827308 prefixEnd_1827308 417016581247129725665053 := by
  unfold tailWord_1827308
  simp only [CollatzResearch.WordTrace]
  refine ⟨33323699031991335102801289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44431598709321780137068385 33323699031991335102801289)
  ·
    refine ⟨24992774273993501327100967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33323699031991335102801289 24992774273993501327100967)
    ·
      refine ⟨37489161410990251990651451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24992774273993501327100967 37489161410990251990651451)
      ·
        refine ⟨56233742116485377985977177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37489161410990251990651451 56233742116485377985977177)
        ·
          refine ⟨42175306587364033489482883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56233742116485377985977177 42175306587364033489482883)
          ·
            refine ⟨63262959881046050234224325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42175306587364033489482883 63262959881046050234224325)
            ·
              refine ⟨11861804977696134418917061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63262959881046050234224325 11861804977696134418917061)
              ·
                refine ⟨2224088433318025203546949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11861804977696134418917061 2224088433318025203546949)
                ·
                  refine ⟨417016581247129725665053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2224088433318025203546949 417016581247129725665053)
                  ·
                    rfl

theorem cell21_1827308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_1827308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827308 prefixEnd_1827308 := by exact prefixLift 1827308
  have htrace : WordTrace (prefixWord ++ tailWord_1827308) baseStart_1827308 baseEnd_1827308 := by
    simpa [prefixWord, tailWord_1827308, baseEnd_1827308] using wordTrace_append hprefix tailTrace_1827308
  have hstable : (prefixWord ++ tailWord_1827308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827308).length < 2 ^ (prefixWord ++ tailWord_1827308).sum := by decide
  have hdescent : baseEnd_1827308 < baseStart_1827308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827384 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_1827384 : Nat := 118140960795 + 1827384 * 2 ^ 59
def prefixEnd_1827384 : Nat := 4983230072969 + 3 ^ 40 * 1827384 * 2
def baseEnd_1827384 : Nat := 417033925482570482398231

theorem tailTrace_1827384 : CollatzResearch.WordTrace tailWord_1827384 prefixEnd_1827384 417033925482570482398231 := by
  unfold tailWord_1827384
  simp only [CollatzResearch.WordTrace]
  refine ⟨33325085005853667592684603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44433446674471556790246137 33325085005853667592684603)
  ·
    refine ⟨49987627508780501389026905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33325085005853667592684603 49987627508780501389026905)
    ·
      refine ⟨37490720631585376041770179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49987627508780501389026905 37490720631585376041770179)
      ·
        refine ⟨56236080947378064062655269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37490720631585376041770179 56236080947378064062655269)
        ·
          refine ⟨10544265177633387011747863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56236080947378064062655269 10544265177633387011747863)
          ·
            refine ⟨15816397766450080517621795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10544265177633387011747863 15816397766450080517621795)
            ·
              refine ⟨23724596649675120776432693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15816397766450080517621795 23724596649675120776432693)
              ·
                refine ⟨2224180935907042572790565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23724596649675120776432693 2224180935907042572790565)
                ·
                  refine ⟨417033925482570482398231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2224180935907042572790565 417033925482570482398231)
                  ·
                    rfl

theorem cell21_1827384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_1827384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827384 prefixEnd_1827384 := by exact prefixLift 1827384
  have htrace : WordTrace (prefixWord ++ tailWord_1827384) baseStart_1827384 baseEnd_1827384 := by
    simpa [prefixWord, tailWord_1827384, baseEnd_1827384] using wordTrace_append hprefix tailTrace_1827384
  have hstable : (prefixWord ++ tailWord_1827384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827384).length < 2 ^ (prefixWord ++ tailWord_1827384).sum := by decide
  have hdescent : baseEnd_1827384 < baseStart_1827384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827460 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_1827460 : Nat := 118140960795 + 1827460 * 2 ^ 59
def prefixEnd_1827460 : Nat := 4983230072969 + 3 ^ 40 * 1827460 * 2
def baseEnd_1827460 : Nat := 417051269718011239131409

theorem tailTrace_1827460 : CollatzResearch.WordTrace tailWord_1827460 prefixEnd_1827460 417051269718011239131409 := by
  unfold tailWord_1827460
  simp only [CollatzResearch.WordTrace]
  refine ⟨33326470979716000082567917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44435294639621333443423889 33326470979716000082567917)
  ·
    refine ⟨12497426617393500030962969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33326470979716000082567917 12497426617393500030962969)
    ·
      refine ⟨9373069963045125023222227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12497426617393500030962969 9373069963045125023222227)
      ·
        refine ⟨14059604944567687534833341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9373069963045125023222227 14059604944567687534833341)
        ·
          refine ⟨5272351854212882825562503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14059604944567687534833341 5272351854212882825562503)
          ·
            refine ⟨7908527781319324238343755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272351854212882825562503 7908527781319324238343755)
            ·
              refine ⟨11862791671978986357515633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908527781319324238343755 11862791671978986357515633)
              ·
                refine ⟨8897093753984239768136725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11862791671978986357515633 8897093753984239768136725)
                ·
                  refine ⟨417051269718011239131409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8897093753984239768136725 417051269718011239131409)
                  ·
                    rfl

theorem cell21_1827460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_1827460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827460 prefixEnd_1827460 := by exact prefixLift 1827460
  have htrace : WordTrace (prefixWord ++ tailWord_1827460) baseStart_1827460 baseEnd_1827460 := by
    simpa [prefixWord, tailWord_1827460, baseEnd_1827460] using wordTrace_append hprefix tailTrace_1827460
  have hstable : (prefixWord ++ tailWord_1827460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827460).length < 2 ^ (prefixWord ++ tailWord_1827460).sum := by decide
  have hdescent : baseEnd_1827460 < baseStart_1827460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827567 : List Nat := [1, 1, 2, 1, 5, 3, 3, 5]
def baseStart_1827567 : Nat := 118140960795 + 1827567 * 2 ^ 59
def prefixEnd_1827567 : Nat := 4983230072969 + 3 ^ 40 * 1827567 * 2
def baseEnd_1827567 : Nat := 139025229525267610282619

theorem tailTrace_1827567 : CollatzResearch.WordTrace tailWord_1827567 prefixEnd_1827567 139025229525267610282619 := by
  unfold tailWord_1827567
  simp only [CollatzResearch.WordTrace]
  refine ⟨66656844570044357439280955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44437896380029571626187303 66656844570044357439280955)
  ·
    refine ⟨99985266855066536158921433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66656844570044357439280955 99985266855066536158921433)
    ·
      refine ⟨74988950141299902119191075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99985266855066536158921433 74988950141299902119191075)
      ·
        refine ⟨112483425211949853178786613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74988950141299902119191075 112483425211949853178786613)
        ·
          refine ⟨10545321113620298735511245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112483425211949853178786613 10545321113620298735511245)
          ·
            refine ⟨3954495417607612025816717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10545321113620298735511245 3954495417607612025816717)
            ·
              refine ⟨1482935781602854509681269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3954495417607612025816717 1482935781602854509681269)
              ·
                refine ⟨139025229525267610282619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1482935781602854509681269 139025229525267610282619)
                ·
                  rfl

theorem cell21_1827567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 5].length) (baseStart_1827567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827567 prefixEnd_1827567 := by exact prefixLift 1827567
  have htrace : WordTrace (prefixWord ++ tailWord_1827567) baseStart_1827567 baseEnd_1827567 := by
    simpa [prefixWord, tailWord_1827567, baseEnd_1827567] using wordTrace_append hprefix tailTrace_1827567
  have hstable : (prefixWord ++ tailWord_1827567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827567).length < 2 ^ (prefixWord ++ tailWord_1827567).sum := by decide
  have hdescent : baseEnd_1827567 < baseStart_1827567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827649 : List Nat := [1, 2, 5, 3, 1, 1, 3, 2, 3]
def baseStart_1827649 : Nat := 118140960795 + 1827649 * 2 ^ 59
def prefixEnd_1827649 : Nat := 4983230072969 + 3 ^ 40 * 1827649 * 2
def baseEnd_1827649 : Nat := 417094402092988910481023

theorem tailTrace_1827649 : CollatzResearch.WordTrace tailWord_1827649 prefixEnd_1827649 417094402092988910481023 := by
  unfold tailWord_1827649
  simp only [CollatzResearch.WordTrace]
  refine ⟨66659835355747285443766001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44439890237164856962510667 66659835355747285443766001)
  ·
    refine ⟨49994876516810464082824501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66659835355747285443766001 49994876516810464082824501)
    ·
      refine ⟨4687019673450981007764797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49994876516810464082824501 4687019673450981007764797)
      ·
        refine ⟨1757632377544117877911799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4687019673450981007764797 1757632377544117877911799)
        ·
          refine ⟨2636448566316176816867699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757632377544117877911799 2636448566316176816867699)
          ·
            refine ⟨3954672849474265225301549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636448566316176816867699 3954672849474265225301549)
            ·
              refine ⟨1483002318552849459488081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3954672849474265225301549 1483002318552849459488081)
              ·
                refine ⟨1112251738914637094616061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483002318552849459488081 1112251738914637094616061)
                ·
                  refine ⟨417094402092988910481023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112251738914637094616061 417094402092988910481023)
                  ·
                    rfl

theorem cell21_1827649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 3].length) (baseStart_1827649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827649 prefixEnd_1827649 := by exact prefixLift 1827649
  have htrace : WordTrace (prefixWord ++ tailWord_1827649) baseStart_1827649 baseEnd_1827649 := by
    simpa [prefixWord, tailWord_1827649, baseEnd_1827649] using wordTrace_append hprefix tailTrace_1827649
  have hstable : (prefixWord ++ tailWord_1827649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827649).length < 2 ^ (prefixWord ++ tailWord_1827649).sum := by decide
  have hdescent : baseEnd_1827649 < baseStart_1827649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827657 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 5]
def baseStart_1827657 : Nat := 118140960795 + 1827657 * 2 ^ 59
def prefixEnd_1827657 : Nat := 4983230072969 + 3 ^ 40 * 1827657 * 2
def baseEnd_1827657 : Nat := 417096227801982674347673

theorem tailTrace_1827657 : CollatzResearch.WordTrace tailWord_1827657 prefixEnd_1827657 417096227801982674347673 := by
  unfold tailWord_1827657
  simp only [CollatzResearch.WordTrace]
  refine ⟨66660127139718302810057225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44440084759812201873371483 66660127139718302810057225)
  ·
    refine ⟨49995095354788727107542919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66660127139718302810057225 49995095354788727107542919)
    ·
      refine ⟨74992643032183090661314379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49995095354788727107542919 74992643032183090661314379)
      ·
        refine ⟨112488964548274635991971569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74992643032183090661314379 112488964548274635991971569)
        ·
          refine ⟨84366723411205976993978677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112488964548274635991971569 84366723411205976993978677)
          ·
            refine ⟨7909380319800560343185501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84366723411205976993978677 7909380319800560343185501)
            ·
              refine ⟨2966017619925210128694563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7909380319800560343185501 2966017619925210128694563)
              ·
                refine ⟨4449026429887815193041845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966017619925210128694563 4449026429887815193041845)
                ·
                  refine ⟨417096227801982674347673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449026429887815193041845 417096227801982674347673)
                  ·
                    rfl

theorem cell21_1827657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_1827657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827657 prefixEnd_1827657 := by exact prefixLift 1827657
  have htrace : WordTrace (prefixWord ++ tailWord_1827657) baseStart_1827657 baseEnd_1827657 := by
    simpa [prefixWord, tailWord_1827657, baseEnd_1827657] using wordTrace_append hprefix tailTrace_1827657
  have hstable : (prefixWord ++ tailWord_1827657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827657).length < 2 ^ (prefixWord ++ tailWord_1827657).sum := by decide
  have hdescent : baseEnd_1827657 < baseStart_1827657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827719 : List Nat := [1, 1, 4, 2, 3, 3, 1, 6]
def baseStart_1827719 : Nat := 118140960795 + 1827719 * 2 ^ 59
def prefixEnd_1827719 : Nat := 4983230072969 + 3 ^ 40 * 1827719 * 2
def baseEnd_1827719 : Nat := 139036792348894781438071

theorem tailTrace_1827719 : CollatzResearch.WordTrace tailWord_1827719 prefixEnd_1827719 139036792348894781438071 := by
  unfold tailWord_1827719
  simp only [CollatzResearch.WordTrace]
  refine ⟨66662388465493687398814211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44441592310329124932542807 66662388465493687398814211)
  ·
    refine ⟨99993582698240531098221317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66662388465493687398814211 99993582698240531098221317)
    ·
      refine ⟨18748796755920099580916497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99993582698240531098221317 18748796755920099580916497)
      ·
        refine ⟨14061597566940074685687373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18748796755920099580916497 14061597566940074685687373)
        ·
          refine ⟨5273099087602528007132765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14061597566940074685687373 5273099087602528007132765)
          ·
            refine ⟨1977412157850948002674787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5273099087602528007132765 1977412157850948002674787)
            ·
              refine ⟨2966118236776422004012181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1977412157850948002674787 2966118236776422004012181)
              ·
                refine ⟨139036792348894781438071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2966118236776422004012181 139036792348894781438071)
                ·
                  rfl

theorem cell21_1827719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 6].length) (baseStart_1827719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827719 prefixEnd_1827719 := by exact prefixLift 1827719
  have htrace : WordTrace (prefixWord ++ tailWord_1827719) baseStart_1827719 baseEnd_1827719 := by
    simpa [prefixWord, tailWord_1827719, baseEnd_1827719] using wordTrace_append hprefix tailTrace_1827719
  have hstable : (prefixWord ++ tailWord_1827719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827719).length < 2 ^ (prefixWord ++ tailWord_1827719).sum := by decide
  have hdescent : baseEnd_1827719 < baseStart_1827719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827733 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 5]
def baseStart_1827733 : Nat := 118140960795 + 1827733 * 2 ^ 59
def prefixEnd_1827733 : Nat := 4983230072969 + 3 ^ 40 * 1827733 * 2
def baseEnd_1827733 : Nat := 417113572037423431080851

theorem tailTrace_1827733 : CollatzResearch.WordTrace tailWord_1827733 prefixEnd_1827733 417113572037423431080851 := by
  unfold tailWord_1827733
  simp only [CollatzResearch.WordTrace]
  refine ⟨66662899087442967789823853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44441932724961978526549235 66662899087442967789823853)
  ·
    refine ⟨24998587157791112921183945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66662899087442967789823853 24998587157791112921183945)
    ·
      refine ⟨18748940368343334690887959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24998587157791112921183945 18748940368343334690887959)
      ·
        refine ⟨28123410552515002036331939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18748940368343334690887959 28123410552515002036331939)
        ·
          refine ⟨42185115828772503054497909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28123410552515002036331939 42185115828772503054497909)
          ·
            refine ⟨3954854608947422161359179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42185115828772503054497909 3954854608947422161359179)
            ·
              refine ⟨5932281913421133242038769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954854608947422161359179 5932281913421133242038769)
              ·
                refine ⟨4449211435065849931529077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932281913421133242038769 4449211435065849931529077)
                ·
                  refine ⟨417113572037423431080851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449211435065849931529077 417113572037423431080851)
                  ·
                    rfl

theorem cell21_1827733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_1827733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827733 prefixEnd_1827733 := by exact prefixLift 1827733
  have htrace : WordTrace (prefixWord ++ tailWord_1827733) baseStart_1827733 baseEnd_1827733 := by
    simpa [prefixWord, tailWord_1827733, baseEnd_1827733] using wordTrace_append hprefix tailTrace_1827733
  have hstable : (prefixWord ++ tailWord_1827733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827733).length < 2 ^ (prefixWord ++ tailWord_1827733).sum := by decide
  have hdescent : baseEnd_1827733 < baseStart_1827733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827823 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 6]
def baseStart_1827823 : Nat := 118140960795 + 1827823 * 2 ^ 59
def prefixEnd_1827823 : Nat := 4983230072969 + 3 ^ 40 * 1827823 * 2
def baseEnd_1827823 : Nat := 417134111263603274580667

theorem tailTrace_1827823 : CollatzResearch.WordTrace tailWord_1827823 prefixEnd_1827823 417134111263603274580667 := by
  unfold tailWord_1827823
  simp only [CollatzResearch.WordTrace]
  refine ⟨66666181657116913160600123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44444121104744608773733415 66666181657116913160600123)
  ·
    refine ⟨99999272485675369740900185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66666181657116913160600123 99999272485675369740900185)
    ·
      refine ⟨74999454364256527305675139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99999272485675369740900185 74999454364256527305675139)
      ·
        refine ⟨112499181546384790958512709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74999454364256527305675139 112499181546384790958512709)
        ·
          refine ⟨21093596539947148304721133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112499181546384790958512709 21093596539947148304721133)
          ·
            refine ⟨7910098702480180614270425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21093596539947148304721133 7910098702480180614270425)
            ·
              refine ⟨5932574026860135460702819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910098702480180614270425 5932574026860135460702819)
              ·
                refine ⟨8898861040290203191054229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932574026860135460702819 8898861040290203191054229)
                ·
                  refine ⟨417134111263603274580667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8898861040290203191054229 417134111263603274580667)
                  ·
                    rfl

theorem cell21_1827823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_1827823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827823 prefixEnd_1827823 := by exact prefixLift 1827823
  have htrace : WordTrace (prefixWord ++ tailWord_1827823) baseStart_1827823 baseEnd_1827823 := by
    simpa [prefixWord, tailWord_1827823, baseEnd_1827823] using wordTrace_append hprefix tailTrace_1827823
  have hstable : (prefixWord ++ tailWord_1827823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827823).length < 2 ^ (prefixWord ++ tailWord_1827823).sum := by decide
  have hdescent : baseEnd_1827823 < baseStart_1827823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827854 : List Nat := [4, 1, 1, 2, 2, 2, 2, 7]
def baseStart_1827854 : Nat := 118140960795 + 1827854 * 2 ^ 59
def prefixEnd_1827854 : Nat := 4983230072969 + 3 ^ 40 * 1827854 * 2
def baseEnd_1827854 : Nat := 139047061961984703187979

theorem tailTrace_1827854 : CollatzResearch.WordTrace tailWord_1827854 prefixEnd_1827854 139047061961984703187979 := by
  unfold tailWord_1827854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8333414040000575681872327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44444874880003070303319077 8333414040000575681872327)
  ·
    refine ⟨12500121060000863522808491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8333414040000575681872327 12500121060000863522808491)
    ·
      refine ⟨18750181590001295284212737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12500121060000863522808491 18750181590001295284212737)
      ·
        refine ⟨14062636192500971463159553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18750181590001295284212737 14062636192500971463159553)
        ·
          refine ⟨10546977144375728597369665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14062636192500971463159553 10546977144375728597369665)
          ·
            refine ⟨7910232858281796448027249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10546977144375728597369665 7910232858281796448027249)
            ·
              refine ⟨5932674643711347336020437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910232858281796448027249 5932674643711347336020437)
              ·
                refine ⟨139047061961984703187979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5932674643711347336020437 139047061961984703187979)
                ·
                  rfl

theorem cell21_1827854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_1827854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827854 prefixEnd_1827854 := by exact prefixLift 1827854
  have htrace : WordTrace (prefixWord ++ tailWord_1827854) baseStart_1827854 baseEnd_1827854 := by
    simpa [prefixWord, tailWord_1827854, baseEnd_1827854] using wordTrace_append hprefix tailTrace_1827854
  have hstable : (prefixWord ++ tailWord_1827854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827854).length < 2 ^ (prefixWord ++ tailWord_1827854).sum := by decide
  have hdescent : baseEnd_1827854 < baseStart_1827854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827902 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 5]
def baseStart_1827902 : Nat := 118140960795 + 1827902 * 2 ^ 59
def prefixEnd_1827902 : Nat := 4983230072969 + 3 ^ 40 * 1827902 * 2
def baseEnd_1827902 : Nat := 417152140139916692763839

theorem tailTrace_1827902 : CollatzResearch.WordTrace tailWord_1827902 prefixEnd_1827902 417152140139916692763839 := by
  unfold tailWord_1827902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8333632877978838706590745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44446042015887139768483973 8333632877978838706590745)
  ·
    refine ⟨6250224658484129029943059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8333632877978838706590745 6250224658484129029943059)
    ·
      refine ⟨9375336987726193544914589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6250224658484129029943059 9375336987726193544914589)
      ·
        refine ⟨3515751370397322579342971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9375336987726193544914589 3515751370397322579342971)
        ·
          refine ⟨5273627055595983869014457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3515751370397322579342971 5273627055595983869014457)
          ·
            refine ⟨3955220291696987901760843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5273627055595983869014457 3955220291696987901760843)
            ·
              refine ⟨5932830437545481852641265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955220291696987901760843 5932830437545481852641265)
              ·
                refine ⟨4449622828159111389480949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932830437545481852641265 4449622828159111389480949)
                ·
                  refine ⟨417152140139916692763839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449622828159111389480949 417152140139916692763839)
                  ·
                    rfl

theorem cell21_1827902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_1827902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827902 prefixEnd_1827902 := by exact prefixLift 1827902
  have htrace : WordTrace (prefixWord ++ tailWord_1827902) baseStart_1827902 baseEnd_1827902 := by
    simpa [prefixWord, tailWord_1827902, baseEnd_1827902] using wordTrace_append hprefix tailTrace_1827902
  have hstable : (prefixWord ++ tailWord_1827902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827902).length < 2 ^ (prefixWord ++ tailWord_1827902).sum := by decide
  have hdescent : baseEnd_1827902 < baseStart_1827902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1827933 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1827933 : Nat := 118140960795 + 1827933 * 2 ^ 59
def prefixEnd_1827933 : Nat := 4983230072969 + 3 ^ 40 * 1827933 * 2
def baseEnd_1827933 : Nat := 417159214762267527747109

theorem tailTrace_1827933 : CollatzResearch.WordTrace tailWord_1827933 prefixEnd_1827933 417159214762267527747109 := by
  unfold tailWord_1827933
  simp only [CollatzResearch.WordTrace]
  refine ⟨66670193686718401947104453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44446795791145601298069635 66670193686718401947104453)
  ·
    refine ⟨12500661316259700365082085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66670193686718401947104453 12500661316259700365082085)
    ·
      refine ⟨2343873996798693818452891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12500661316259700365082085 2343873996798693818452891)
      ·
        refine ⟨3515810995198040727679337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343873996798693818452891 3515810995198040727679337)
        ·
          refine ⟨2636858246398530545759503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3515810995198040727679337 2636858246398530545759503)
          ·
            refine ⟨3955287369597795818639255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636858246398530545759503 3955287369597795818639255)
            ·
              refine ⟨5932931054396693727958883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955287369597795818639255 5932931054396693727958883)
              ·
                refine ⟨8899396581595040591938325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932931054396693727958883 8899396581595040591938325)
                ·
                  refine ⟨417159214762267527747109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8899396581595040591938325 417159214762267527747109)
                  ·
                    rfl

theorem cell21_1827933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1827933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1827933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1827933 prefixEnd_1827933 := by exact prefixLift 1827933
  have htrace : WordTrace (prefixWord ++ tailWord_1827933) baseStart_1827933 baseEnd_1827933 := by
    simpa [prefixWord, tailWord_1827933, baseEnd_1827933] using wordTrace_append hprefix tailTrace_1827933
  have hstable : (prefixWord ++ tailWord_1827933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1827933).length < 2 ^ (prefixWord ++ tailWord_1827933).sum := by decide
  have hdescent : baseEnd_1827933 < baseStart_1827933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1827933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828037 : List Nat := [1, 3, 1, 1, 1, 1, 3, 7, 3]
def baseStart_1828037 : Nat := 118140960795 + 1828037 * 2 ^ 59
def prefixEnd_1828037 : Nat := 4983230072969 + 3 ^ 40 * 1828037 * 2
def baseEnd_1828037 : Nat := 417182948979186458013563

theorem tailTrace_1828037 : CollatzResearch.WordTrace tailWord_1828037 prefixEnd_1828037 417182948979186458013563 := by
  unfold tailWord_1828037
  simp only [CollatzResearch.WordTrace]
  refine ⟨66673986878341627708890365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44449324585561085139260243 66673986878341627708890365)
  ·
    refine ⟨25002745079378110390833887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66673986878341627708890365 25002745079378110390833887)
    ·
      refine ⟨37504117619067165586250831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25002745079378110390833887 37504117619067165586250831)
      ·
        refine ⟨56256176428600748379376247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37504117619067165586250831 56256176428600748379376247)
        ·
          refine ⟨84384264642901122569064371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56256176428600748379376247 84384264642901122569064371)
          ·
            refine ⟨126576396964351683853596557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84384264642901122569064371 126576396964351683853596557)
            ·
              refine ⟨47466148861631881445098709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126576396964351683853596557 47466148861631881445098709)
              ·
                refine ⟨1112487863944497221369501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47466148861631881445098709 1112487863944497221369501)
                ·
                  refine ⟨417182948979186458013563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112487863944497221369501 417182948979186458013563)
                  ·
                    rfl

theorem cell21_1828037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_1828037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828037 prefixEnd_1828037 := by exact prefixLift 1828037
  have htrace : WordTrace (prefixWord ++ tailWord_1828037) baseStart_1828037 baseEnd_1828037 := by
    simpa [prefixWord, tailWord_1828037, baseEnd_1828037] using wordTrace_append hprefix tailTrace_1828037
  have hstable : (prefixWord ++ tailWord_1828037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828037).length < 2 ^ (prefixWord ++ tailWord_1828037).sum := by decide
  have hdescent : baseEnd_1828037 < baseStart_1828037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828113 : List Nat := [1, 2, 2, 1, 1, 4, 1, 6, 3]
def baseStart_1828113 : Nat := 118140960795 + 1828113 * 2 ^ 59
def prefixEnd_1828113 : Nat := 4983230072969 + 3 ^ 40 * 1828113 * 2
def baseEnd_1828113 : Nat := 417200293214627214746741

theorem tailTrace_1828113 : CollatzResearch.WordTrace tailWord_1828113 prefixEnd_1828113 417200293214627214746741 := by
  unfold tailWord_1828113
  simp only [CollatzResearch.WordTrace]
  refine ⟨66676758826066292688656993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44451172550710861792437995 66676758826066292688656993)
  ·
    refine ⟨50007569119549719516492745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66676758826066292688656993 50007569119549719516492745)
    ·
      refine ⟨37505676839662289637369559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50007569119549719516492745 37505676839662289637369559)
      ·
        refine ⟨56258515259493434456054339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37505676839662289637369559 56258515259493434456054339)
        ·
          refine ⟨84387772889240151684081509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56258515259493434456054339 84387772889240151684081509)
          ·
            refine ⟨15822707416732528440765283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84387772889240151684081509 15822707416732528440765283)
            ·
              refine ⟨23734061125098792661147925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15822707416732528440765283 23734061125098792661147925)
              ·
                refine ⟨1112534115239005905991309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23734061125098792661147925 1112534115239005905991309)
                ·
                  refine ⟨417200293214627214746741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112534115239005905991309 417200293214627214746741)
                  ·
                    rfl

theorem cell21_1828113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 3].length) (baseStart_1828113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828113 prefixEnd_1828113 := by exact prefixLift 1828113
  have htrace : WordTrace (prefixWord ++ tailWord_1828113) baseStart_1828113 baseEnd_1828113 := by
    simpa [prefixWord, tailWord_1828113, baseEnd_1828113] using wordTrace_append hprefix tailTrace_1828113
  have hstable : (prefixWord ++ tailWord_1828113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828113).length < 2 ^ (prefixWord ++ tailWord_1828113).sum := by decide
  have hdescent : baseEnd_1828113 < baseStart_1828113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828164 : List Nat := [2, 3, 4, 1, 1, 2, 3, 2, 3]
def baseStart_1828164 : Nat := 118140960795 + 1828164 * 2 ^ 59
def prefixEnd_1828164 : Nat := 4983230072969 + 3 ^ 40 * 1828164 * 2
def baseEnd_1828164 : Nat := 417211932109462459396637

theorem tailTrace_1828164 : CollatzResearch.WordTrace tailWord_1828164 prefixEnd_1828164 417211932109462459396637 := by
  unfold tailWord_1828164
  simp only [CollatzResearch.WordTrace]
  refine ⟨33339309474440764199381773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44452412632587685599175697 33339309474440764199381773)
  ·
    refine ⟨12502241052915286574768165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33339309474440764199381773 12502241052915286574768165)
    ·
      refine ⟨2344170197421616232769031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12502241052915286574768165 2344170197421616232769031)
      ·
        refine ⟨3516255296132424349153547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344170197421616232769031 3516255296132424349153547)
        ·
          refine ⟨5274382944198636523730321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3516255296132424349153547 5274382944198636523730321)
          ·
            refine ⟨3955787208148977392797741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5274382944198636523730321 3955787208148977392797741)
            ·
              refine ⟨1483420203055866522299153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3955787208148977392797741 1483420203055866522299153)
              ·
                refine ⟨1112565152291899891724365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483420203055866522299153 1112565152291899891724365)
                ·
                  refine ⟨417211932109462459396637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112565152291899891724365 417211932109462459396637)
                  ·
                    rfl

theorem cell21_1828164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_1828164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828164 prefixEnd_1828164 := by exact prefixLift 1828164
  have htrace : WordTrace (prefixWord ++ tailWord_1828164) baseStart_1828164 baseEnd_1828164 := by
    simpa [prefixWord, tailWord_1828164, baseEnd_1828164] using wordTrace_append hprefix tailTrace_1828164
  have hstable : (prefixWord ++ tailWord_1828164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828164).length < 2 ^ (prefixWord ++ tailWord_1828164).sum := by decide
  have hdescent : baseEnd_1828164 < baseStart_1828164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828296 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_1828296 : Nat := 118140960795 + 1828296 * 2 ^ 59
def prefixEnd_1828296 : Nat := 4983230072969 + 3 ^ 40 * 1828296 * 2
def baseEnd_1828296 : Nat := 417242056307859563196367

theorem tailTrace_1828296 : CollatzResearch.WordTrace tailWord_1828296 prefixEnd_1828296 417242056307859563196367 := by
  unfold tailWord_1828296
  simp only [CollatzResearch.WordTrace]
  refine ⟨33341716692201657471284371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44455622256268876628379161 33341716692201657471284371)
  ·
    refine ⟨50012575038302486206926557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33341716692201657471284371 50012575038302486206926557)
    ·
      refine ⟨18754715639363432327597459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50012575038302486206926557 18754715639363432327597459)
      ·
        refine ⟨28132073459045148491396189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18754715639363432327597459 28132073459045148491396189)
        ·
          refine ⟨10549527547141930684273571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28132073459045148491396189 10549527547141930684273571)
          ·
            refine ⟨15824291320712896026410357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10549527547141930684273571 15824291320712896026410357)
            ·
              refine ⟨1483527311316834002475971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15824291320712896026410357 1483527311316834002475971)
              ·
                refine ⟨2225290966975251003713957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483527311316834002475971 2225290966975251003713957)
                ·
                  refine ⟨417242056307859563196367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225290966975251003713957 417242056307859563196367)
                  ·
                    rfl

theorem cell21_1828296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_1828296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828296 prefixEnd_1828296 := by exact prefixLift 1828296
  have htrace : WordTrace (prefixWord ++ tailWord_1828296) baseStart_1828296 baseEnd_1828296 := by
    simpa [prefixWord, tailWord_1828296, baseEnd_1828296] using wordTrace_append hprefix tailTrace_1828296
  have hstable : (prefixWord ++ tailWord_1828296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828296).length < 2 ^ (prefixWord ++ tailWord_1828296).sum := by decide
  have hdescent : baseEnd_1828296 < baseStart_1828296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828392 : List Nat := [2, 1, 5, 2, 2, 2, 2, 2, 3]
def baseStart_1828392 : Nat := 118140960795 + 1828392 * 2 ^ 59
def prefixEnd_1828392 : Nat := 4983230072969 + 3 ^ 40 * 1828392 * 2
def baseEnd_1828392 : Nat := 417263964815784729596171

theorem tailTrace_1828392 : CollatzResearch.WordTrace tailWord_1828392 prefixEnd_1828392 417263964815784729596171 := by
  unfold tailWord_1828392
  simp only [CollatzResearch.WordTrace]
  refine ⟨33343467396027761669031715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44457956528037015558708953 33343467396027761669031715)
  ·
    refine ⟨50015201094041642503547573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33343467396027761669031715 50015201094041642503547573)
    ·
      refine ⟨4688925102566403984707585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50015201094041642503547573 4688925102566403984707585)
      ·
        refine ⟨3516693826924802988530689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4688925102566403984707585 3516693826924802988530689)
        ·
          refine ⟨2637520370193602241398017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3516693826924802988530689 2637520370193602241398017)
          ·
            refine ⟨1978140277645201681048513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2637520370193602241398017 1978140277645201681048513)
            ·
              refine ⟨1483605208233901260786385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1978140277645201681048513 1483605208233901260786385)
              ·
                refine ⟨1112703906175425945589789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1483605208233901260786385 1112703906175425945589789)
                ·
                  refine ⟨417263964815784729596171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112703906175425945589789 417263964815784729596171)
                  ·
                    rfl

theorem cell21_1828392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 3].length) (baseStart_1828392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828392 prefixEnd_1828392 := by exact prefixLift 1828392
  have htrace : WordTrace (prefixWord ++ tailWord_1828392) baseStart_1828392 baseEnd_1828392 := by
    simpa [prefixWord, tailWord_1828392, baseEnd_1828392] using wordTrace_append hprefix tailTrace_1828392
  have hstable : (prefixWord ++ tailWord_1828392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828392).length < 2 ^ (prefixWord ++ tailWord_1828392).sum := by decide
  have hdescent : baseEnd_1828392 < baseStart_1828392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828434 : List Nat := [3, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_1828434 : Nat := 118140960795 + 1828434 * 2 ^ 59
def prefixEnd_1828434 : Nat := 4983230072969 + 3 ^ 40 * 1828434 * 2
def baseEnd_1828434 : Nat := 417273549788001989896085

theorem tailTrace_1828434 : CollatzResearch.WordTrace tailWord_1828434 prefixEnd_1828434 417273549788001989896085 := by
  unfold tailWord_1828434
  simp only [CollatzResearch.WordTrace]
  refine ⟨16672116664475841127773089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44458977771935576340728237 16672116664475841127773089)
  ·
    refine ⟨12504087498356880845829817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16672116664475841127773089 12504087498356880845829817)
    ·
      refine ⟨9378065623767660634372363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12504087498356880845829817 9378065623767660634372363)
      ·
        refine ⟨14067098435651490951558545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9378065623767660634372363 14067098435651490951558545)
        ·
          refine ⟨10550323826738618213668909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14067098435651490951558545 10550323826738618213668909)
          ·
            refine ⟨3956371435026981830125841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10550323826738618213668909 3956371435026981830125841)
            ·
              refine ⟨2967278576270236372594381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3956371435026981830125841 2967278576270236372594381)
              ·
                refine ⟨1112729466101338639722893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2967278576270236372594381 1112729466101338639722893)
                ·
                  refine ⟨417273549788001989896085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112729466101338639722893 417273549788001989896085)
                  ·
                    rfl

theorem cell21_1828434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_1828434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828434 prefixEnd_1828434 := by exact prefixLift 1828434
  have htrace : WordTrace (prefixWord ++ tailWord_1828434) baseStart_1828434 baseEnd_1828434 := by
    simpa [prefixWord, tailWord_1828434, baseEnd_1828434] using wordTrace_append hprefix tailTrace_1828434
  have hstable : (prefixWord ++ tailWord_1828434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828434).length < 2 ^ (prefixWord ++ tailWord_1828434).sum := by decide
  have hdescent : baseEnd_1828434 < baseStart_1828434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828510 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1828510 : Nat := 118140960795 + 1828510 * 2 ^ 59
def prefixEnd_1828510 : Nat := 4983230072969 + 3 ^ 40 * 1828510 * 2
def baseEnd_1828510 : Nat := 417290894023442746629263

theorem tailTrace_1828510 : CollatzResearch.WordTrace tailWord_1828510 prefixEnd_1828510 417290894023442746629263 := by
  unfold tailWord_1828510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8336404825703503686357373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44460825737085352993905989 8336404825703503686357373)
  ·
    refine ⟨3126151809638813882384015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8336404825703503686357373 3126151809638813882384015)
    ·
      refine ⟨4689227714458220823576023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3126151809638813882384015 4689227714458220823576023)
      ·
        refine ⟨7033841571687331235364035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4689227714458220823576023 7033841571687331235364035)
        ·
          refine ⟨10550762357530996853046053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033841571687331235364035 10550762357530996853046053)
          ·
            refine ⟨1978267942037061909946135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10550762357530996853046053 1978267942037061909946135)
            ·
              refine ⟨2967401913055592864919203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978267942037061909946135 2967401913055592864919203)
              ·
                refine ⟨4451102869583389297378805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967401913055592864919203 4451102869583389297378805)
                ·
                  refine ⟨417290894023442746629263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4451102869583389297378805 417290894023442746629263)
                  ·
                    rfl

theorem cell21_1828510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1828510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828510 prefixEnd_1828510 := by exact prefixLift 1828510
  have htrace : WordTrace (prefixWord ++ tailWord_1828510) baseStart_1828510 baseEnd_1828510 := by
    simpa [prefixWord, tailWord_1828510, baseEnd_1828510] using wordTrace_append hprefix tailTrace_1828510
  have hstable : (prefixWord ++ tailWord_1828510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828510).length < 2 ^ (prefixWord ++ tailWord_1828510).sum := by decide
  have hdescent : baseEnd_1828510 < baseStart_1828510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828569 : List Nat := [1, 2, 1, 2, 3, 4, 1, 4, 3]
def baseStart_1828569 : Nat := 118140960795 + 1828569 * 2 ^ 59
def prefixEnd_1828569 : Nat := 4983230072969 + 3 ^ 40 * 1828569 * 2
def baseEnd_1828569 : Nat := 417304358627271755145809

theorem tailTrace_1828569 : CollatzResearch.WordTrace tailWord_1828569 prefixEnd_1828569 417304358627271755145809 := by
  unfold tailWord_1828569
  simp only [CollatzResearch.WordTrace]
  refine ⟨66693390512414282567256761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44462260341609521711504507 66693390512414282567256761)
  ·
    refine ⟨50020042884310711925442571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66693390512414282567256761 50020042884310711925442571)
    ·
      refine ⟨75030064326466067888163857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50020042884310711925442571 75030064326466067888163857)
      ·
        refine ⟨56272548244849550916122893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75030064326466067888163857 56272548244849550916122893)
        ·
          refine ⟨21102205591818581593546085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56272548244849550916122893 21102205591818581593546085)
          ·
            refine ⟨3956663548465984048789891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21102205591818581593546085 3956663548465984048789891)
            ·
              refine ⟨5934995322698976073184837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956663548465984048789891 5934995322698976073184837)
              ·
                refine ⟨1112811623006058013722157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5934995322698976073184837 1112811623006058013722157)
                ·
                  refine ⟨417304358627271755145809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112811623006058013722157 417304358627271755145809)
                  ·
                    rfl

theorem cell21_1828569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 3].length) (baseStart_1828569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828569 prefixEnd_1828569 := by exact prefixLift 1828569
  have htrace : WordTrace (prefixWord ++ tailWord_1828569) baseStart_1828569 baseEnd_1828569 := by
    simpa [prefixWord, tailWord_1828569, baseEnd_1828569] using wordTrace_append hprefix tailTrace_1828569
  have hstable : (prefixWord ++ tailWord_1828569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828569).length < 2 ^ (prefixWord ++ tailWord_1828569).sum := by decide
  have hdescent : baseEnd_1828569 < baseStart_1828569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828572 : List Nat := [2, 2, 5, 1, 3, 1, 1, 6]
def baseStart_1828572 : Nat := 118140960795 + 1828572 * 2 ^ 59
def prefixEnd_1828572 : Nat := 4983230072969 + 3 ^ 40 * 1828572 * 2
def baseEnd_1828572 : Nat := 139101681089381472198601

theorem tailTrace_1828572 : CollatzResearch.WordTrace tailWord_1828572 prefixEnd_1828572 139101681089381472198601 := by
  unfold tailWord_1828572
  simp only [CollatzResearch.WordTrace]
  refine ⟨33346749965701707039807985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44462333287602276053077313 33346749965701707039807985)
  ·
    refine ⟨25010062474276280279855989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33346749965701707039807985 25010062474276280279855989)
    ·
      refine ⟨2344693356963401276236499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25010062474276280279855989 2344693356963401276236499)
      ·
        refine ⟨3517040035445101914354749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344693356963401276236499 3517040035445101914354749)
        ·
          refine ⟨1318890013291913217883031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3517040035445101914354749 1318890013291913217883031)
          ·
            refine ⟨1978335019937869826824547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1318890013291913217883031 1978335019937869826824547)
            ·
              refine ⟨2967502529906804740236821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1978335019937869826824547 2967502529906804740236821)
              ·
                refine ⟨139101681089381472198601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2967502529906804740236821 139101681089381472198601)
                ·
                  rfl

theorem cell21_1828572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_1828572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828572 prefixEnd_1828572 := by exact prefixLift 1828572
  have htrace : WordTrace (prefixWord ++ tailWord_1828572) baseStart_1828572 baseEnd_1828572 := by
    simpa [prefixWord, tailWord_1828572, baseEnd_1828572] using wordTrace_append hprefix tailTrace_1828572
  have hstable : (prefixWord ++ tailWord_1828572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828572).length < 2 ^ (prefixWord ++ tailWord_1828572).sum := by decide
  have hdescent : baseEnd_1828572 < baseStart_1828572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828794 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_1828794 : Nat := 118140960795 + 1828794 * 2 ^ 59
def prefixEnd_1828794 : Nat := 4983230072969 + 3 ^ 40 * 1828794 * 2
def baseEnd_1828794 : Nat := 417355706692721363895349

theorem tailTrace_1828794 : CollatzResearch.WordTrace tailWord_1828794 prefixEnd_1828794 417355706692721363895349 := by
  unfold tailWord_1828794
  simp only [CollatzResearch.WordTrace]
  refine ⟨16675399234149786498549359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44467731291066097329464957 16675399234149786498549359)
  ·
    refine ⟨25013098851224679747824039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16675399234149786498549359 25013098851224679747824039)
    ·
      refine ⟨37519648276837019621736059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25013098851224679747824039 37519648276837019621736059)
      ·
        refine ⟨56279472415255529432604089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37519648276837019621736059 56279472415255529432604089)
        ·
          refine ⟨42209604311441647074453067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56279472415255529432604089 42209604311441647074453067)
          ·
            refine ⟨63314406467162470611679601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42209604311441647074453067 63314406467162470611679601)
            ·
              refine ⟨47485804850371852958759701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63314406467162470611679601 47485804850371852958759701)
              ·
                refine ⟨2225897102361180607441861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47485804850371852958759701 2225897102361180607441861)
                ·
                  refine ⟨417355706692721363895349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225897102361180607441861 417355706692721363895349)
                  ·
                    rfl

theorem cell21_1828794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_1828794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828794 prefixEnd_1828794 := by exact prefixLift 1828794
  have htrace : WordTrace (prefixWord ++ tailWord_1828794) baseStart_1828794 baseEnd_1828794 := by
    simpa [prefixWord, tailWord_1828794, baseEnd_1828794] using wordTrace_append hprefix tailTrace_1828794
  have hstable : (prefixWord ++ tailWord_1828794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828794).length < 2 ^ (prefixWord ++ tailWord_1828794).sum := by decide
  have hdescent : baseEnd_1828794 < baseStart_1828794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828797 : List Nat := [1, 4, 1, 2, 3, 1, 2, 4, 3]
def baseStart_1828797 : Nat := 118140960795 + 1828797 * 2 ^ 59
def prefixEnd_1828797 : Nat := 4983230072969 + 3 ^ 40 * 1828797 * 2
def baseEnd_1828797 : Nat := 417356391333594025345343

theorem tailTrace_1828797 : CollatzResearch.WordTrace tailWord_1828797 prefixEnd_1828797 417356391333594025345343 := by
  unfold tailWord_1828797
  simp only [CollatzResearch.WordTrace]
  refine ⟨66701706355588277506556645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44467804237058851671037763 66701706355588277506556645)
  ·
    refine ⟨12506569941672802032479371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66701706355588277506556645 12506569941672802032479371)
    ·
      refine ⟨18759854912509203048719057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12506569941672802032479371 18759854912509203048719057)
      ·
        refine ⟨14069891184381902286539293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18759854912509203048719057 14069891184381902286539293)
        ·
          refine ⟨5276209194143213357452235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14069891184381902286539293 5276209194143213357452235)
          ·
            refine ⟨7914313791214820036178353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276209194143213357452235 7914313791214820036178353)
            ·
              refine ⟨5935735343411115027133765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7914313791214820036178353 5935735343411115027133765)
              ·
                refine ⟨1112950376889584067587581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5935735343411115027133765 1112950376889584067587581)
                ·
                  refine ⟨417356391333594025345343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112950376889584067587581 417356391333594025345343)
                  ·
                    rfl

theorem cell21_1828797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_1828797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828797 prefixEnd_1828797 := by exact prefixLift 1828797
  have htrace : WordTrace (prefixWord ++ tailWord_1828797) baseStart_1828797 baseEnd_1828797 := by
    simpa [prefixWord, tailWord_1828797, baseEnd_1828797] using wordTrace_append hprefix tailTrace_1828797
  have hstable : (prefixWord ++ tailWord_1828797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828797).length < 2 ^ (prefixWord ++ tailWord_1828797).sum := by decide
  have hdescent : baseEnd_1828797 < baseStart_1828797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828811 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 4]
def baseStart_1828811 : Nat := 118140960795 + 1828811 * 2 ^ 59
def prefixEnd_1828811 : Nat := 4983230072969 + 3 ^ 40 * 1828811 * 2
def baseEnd_1828811 : Nat := 417359586324333112111981

theorem tailTrace_1828811 : CollatzResearch.WordTrace tailWord_1828811 prefixEnd_1828811 417359586324333112111981 := by
  unfold tailWord_1828811
  simp only [CollatzResearch.WordTrace]
  refine ⟨66702216977537557897566287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44468144651691705265044191 66702216977537557897566287)
  ·
    refine ⟨100053325466306336846349431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66702216977537557897566287 100053325466306336846349431)
    ·
      refine ⟨150079988199459505269524147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100053325466306336846349431 150079988199459505269524147)
      ·
        refine ⟨225119982299189257904286221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150079988199459505269524147 225119982299189257904286221)
        ·
          refine ⟨84419993362195971714107333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225119982299189257904286221 84419993362195971714107333)
          ·
            refine ⟨15828748755411744696395125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84419993362195971714107333 15828748755411744696395125)
            ·
              refine ⟨1483945195819851065287043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15828748755411744696395125 1483945195819851065287043)
              ·
                refine ⟨2225917793729776597930565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1483945195819851065287043 2225917793729776597930565)
                ·
                  refine ⟨417359586324333112111981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225917793729776597930565 417359586324333112111981)
                  ·
                    rfl

theorem cell21_1828811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 4].length) (baseStart_1828811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828811 prefixEnd_1828811 := by exact prefixLift 1828811
  have htrace : WordTrace (prefixWord ++ tailWord_1828811) baseStart_1828811 baseEnd_1828811 := by
    simpa [prefixWord, tailWord_1828811, baseEnd_1828811] using wordTrace_append hprefix tailTrace_1828811
  have hstable : (prefixWord ++ tailWord_1828811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828811).length < 2 ^ (prefixWord ++ tailWord_1828811).sum := by decide
  have hdescent : baseEnd_1828811 < baseStart_1828811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828825 : List Nat := [1, 2, 1, 2, 6, 1, 1, 7]
def baseStart_1828825 : Nat := 118140960795 + 1828825 * 2 ^ 59
def prefixEnd_1828825 : Nat := 4983230072969 + 3 ^ 40 * 1828825 * 2
def baseEnd_1828825 : Nat := 139120927105024066292873

theorem tailTrace_1828825 : CollatzResearch.WordTrace tailWord_1828825 prefixEnd_1828825 139120927105024066292873 := by
  unfold tailWord_1828825
  simp only [CollatzResearch.WordTrace]
  refine ⟨66702727599486838288575929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44468485066324558859050619 66702727599486838288575929)
  ·
    refine ⟨50027045699615128716431947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66702727599486838288575929 50027045699615128716431947)
    ·
      refine ⟨75040568549422693074647921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50027045699615128716431947 75040568549422693074647921)
      ·
        refine ⟨56280426412067019805985941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75040568549422693074647921 56280426412067019805985941)
        ·
          refine ⟨2638144988065641553405591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56280426412067019805985941 2638144988065641553405591)
          ·
            refine ⟨3957217482098462330108387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638144988065641553405591 3957217482098462330108387)
            ·
              refine ⟨5935826223147693495162581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957217482098462330108387 5935826223147693495162581)
              ·
                refine ⟨139120927105024066292873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5935826223147693495162581 139120927105024066292873)
                ·
                  rfl

theorem cell21_1828825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 7].length) (baseStart_1828825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828825 prefixEnd_1828825 := by exact prefixLift 1828825
  have htrace : WordTrace (prefixWord ++ tailWord_1828825) baseStart_1828825 baseEnd_1828825 := by
    simpa [prefixWord, tailWord_1828825, baseEnd_1828825] using wordTrace_append hprefix tailTrace_1828825
  have hstable : (prefixWord ++ tailWord_1828825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828825).length < 2 ^ (prefixWord ++ tailWord_1828825).sum := by decide
  have hdescent : baseEnd_1828825 < baseStart_1828825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828856 : List Nat := [2, 1, 2, 1, 1, 3, 2, 6, 3]
def baseStart_1828856 : Nat := 118140960795 + 1828856 * 2 ^ 59
def prefixEnd_1828856 : Nat := 4983230072969 + 3 ^ 40 * 1828856 * 2
def baseEnd_1828856 : Nat := 417369855937423033861889

theorem tailTrace_1828856 : CollatzResearch.WordTrace tailWord_1828856 prefixEnd_1828856 417369855937423033861889 := by
  unfold tailWord_1828856
  simp only [CollatzResearch.WordTrace]
  refine ⟨33351929131187265291477211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44469238841583020388636281 33351929131187265291477211)
  ·
    refine ⟨50027893696780897937215817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33351929131187265291477211 50027893696780897937215817)
    ·
      refine ⟨37520920272585673452911863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50027893696780897937215817 37520920272585673452911863)
      ·
        refine ⟨56281380408878510179367795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37520920272585673452911863 56281380408878510179367795)
        ·
          refine ⟨84422070613317765269051693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56281380408878510179367795 84422070613317765269051693)
          ·
            refine ⟨31658276479994161975894385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84422070613317765269051693 31658276479994161975894385)
            ·
              refine ⟨23743707359995621481920789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31658276479994161975894385 23743707359995621481920789)
              ·
                refine ⟨1112986282499794756965037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23743707359995621481920789 1112986282499794756965037)
                ·
                  refine ⟨417369855937423033861889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1112986282499794756965037 417369855937423033861889)
                  ·
                    rfl

theorem cell21_1828856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 3].length) (baseStart_1828856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828856 prefixEnd_1828856 := by exact prefixLift 1828856
  have htrace : WordTrace (prefixWord ++ tailWord_1828856) baseStart_1828856 baseEnd_1828856 := by
    simpa [prefixWord, tailWord_1828856, baseEnd_1828856] using wordTrace_append hprefix tailTrace_1828856
  have hstable : (prefixWord ++ tailWord_1828856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828856).length < 2 ^ (prefixWord ++ tailWord_1828856).sum := by decide
  have hdescent : baseEnd_1828856 < baseStart_1828856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828949 : List Nat := [1, 3, 2, 2, 1, 4, 2, 3, 3]
def baseStart_1828949 : Nat := 118140960795 + 1828949 * 2 ^ 59
def prefixEnd_1828949 : Nat := 4983230072969 + 3 ^ 40 * 1828949 * 2
def baseEnd_1828949 : Nat := 417391079804475538811699

theorem tailTrace_1828949 : CollatzResearch.WordTrace tailWord_1828949 prefixEnd_1828949 417391079804475538811699 := by
  unfold tailWord_1828949
  simp only [CollatzResearch.WordTrace]
  refine ⟨66707250251037607466089901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44471500167358404977393267 66707250251037607466089901)
  ·
    refine ⟨25015218844139102799783713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66707250251037607466089901 25015218844139102799783713)
    ·
      refine ⟨18761414133104327099837785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25015218844139102799783713 18761414133104327099837785)
      ·
        refine ⟨14071060599828245324878339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18761414133104327099837785 14071060599828245324878339)
        ·
          refine ⟨21106590899742367987317509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14071060599828245324878339 21106590899742367987317509)
          ·
            refine ⟨3957485793701693997622033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21106590899742367987317509 3957485793701693997622033)
            ·
              refine ⟨2968114345276270498216525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3957485793701693997622033 2968114345276270498216525)
              ·
                refine ⟨1113042879478601436831197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2968114345276270498216525 1113042879478601436831197)
                ·
                  refine ⟨417391079804475538811699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113042879478601436831197 417391079804475538811699)
                  ·
                    rfl

theorem cell21_1828949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_1828949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828949 prefixEnd_1828949 := by exact prefixLift 1828949
  have htrace : WordTrace (prefixWord ++ tailWord_1828949) baseStart_1828949 baseEnd_1828949 := by
    simpa [prefixWord, tailWord_1828949, baseEnd_1828949] using wordTrace_append hprefix tailTrace_1828949
  have hstable : (prefixWord ++ tailWord_1828949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828949).length < 2 ^ (prefixWord ++ tailWord_1828949).sum := by decide
  have hdescent : baseEnd_1828949 < baseStart_1828949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1828960 : List Nat := [2, 1, 1, 3, 2, 4, 8]
def baseStart_1828960 : Nat := 118140960795 + 1828960 * 2 ^ 59
def prefixEnd_1828960 : Nat := 4983230072969 + 3 ^ 40 * 1828960 * 2
def baseEnd_1828960 : Nat := 46377065572704662680927

theorem tailTrace_1828960 : CollatzResearch.WordTrace tailWord_1828960 prefixEnd_1828960 46377065572704662680927 := by
  unfold tailWord_1828960
  simp only [CollatzResearch.WordTrace]
  refine ⟨33353825726998878172370167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44471767635998504229826889 33353825726998878172370167)
  ·
    refine ⟨50030738590498317258555251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33353825726998878172370167 50030738590498317258555251)
    ·
      refine ⟨75046107885747475887832877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50030738590498317258555251 75046107885747475887832877)
      ·
        refine ⟨28142290457155303457937329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75046107885747475887832877 28142290457155303457937329)
        ·
          refine ⟨21106717842866477593452997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28142290457155303457937329 21106717842866477593452997)
          ·
            refine ⟨3957509595537464548772437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21106717842866477593452997 3957509595537464548772437)
            ·
              refine ⟨46377065572704662680927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3957509595537464548772437 46377065572704662680927)
              ·
                rfl

theorem cell21_1828960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 8].length) (baseStart_1828960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1828960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1828960 prefixEnd_1828960 := by exact prefixLift 1828960
  have htrace : WordTrace (prefixWord ++ tailWord_1828960) baseStart_1828960 baseEnd_1828960 := by
    simpa [prefixWord, tailWord_1828960, baseEnd_1828960] using wordTrace_append hprefix tailTrace_1828960
  have hstable : (prefixWord ++ tailWord_1828960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1828960).length < 2 ^ (prefixWord ++ tailWord_1828960).sum := by decide
  have hdescent : baseEnd_1828960 < baseStart_1828960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1828960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829081 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 6]
def baseStart_1829081 : Nat := 118140960795 + 1829081 * 2 ^ 59
def prefixEnd_1829081 : Nat := 4983230072969 + 3 ^ 40 * 1829081 * 2
def baseEnd_1829081 : Nat := 417421204002872642611429

theorem tailTrace_1829081 : CollatzResearch.WordTrace tailWord_1829081 prefixEnd_1829081 417421204002872642611429 := by
  unfold tailWord_1829081
  simp only [CollatzResearch.WordTrace]
  refine ⟨66712064686559394009895097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44474709791039596006596731 66712064686559394009895097)
  ·
    refine ⟨50034048514919545507421323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66712064686559394009895097 50034048514919545507421323)
    ·
      refine ⟨75051072772379318261131985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50034048514919545507421323 75051072772379318261131985)
      ·
        refine ⟨56288304579284488695848989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75051072772379318261131985 56288304579284488695848989)
        ·
          refine ⟨21108114217231683260943371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56288304579284488695848989 21108114217231683260943371)
          ·
            refine ⟨31662171325847524891415057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21108114217231683260943371 31662171325847524891415057)
            ·
              refine ⟨23746628494385643668561293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31662171325847524891415057 23746628494385643668561293)
              ·
                refine ⟨8904985685394616375710485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23746628494385643668561293 8904985685394616375710485)
                ·
                  refine ⟨417421204002872642611429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8904985685394616375710485 417421204002872642611429)
                  ·
                    rfl

theorem cell21_1829081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_1829081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829081 prefixEnd_1829081 := by exact prefixLift 1829081
  have htrace : WordTrace (prefixWord ++ tailWord_1829081) baseStart_1829081 baseEnd_1829081 := by
    simpa [prefixWord, tailWord_1829081, baseEnd_1829081] using wordTrace_append hprefix tailTrace_1829081
  have hstable : (prefixWord ++ tailWord_1829081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829081).length < 2 ^ (prefixWord ++ tailWord_1829081).sum := by decide
  have hdescent : baseEnd_1829081 < baseStart_1829081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829098 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_1829098 : Nat := 118140960795 + 1829098 * 2 ^ 59
def prefixEnd_1829098 : Nat := 4983230072969 + 3 ^ 40 * 1829098 * 2
def baseEnd_1829098 : Nat := 417425083634484390828061

theorem tailTrace_1829098 : CollatzResearch.WordTrace tailWord_1829098 prefixEnd_1829098 417425083634484390828061 := by
  unfold tailWord_1829098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16678171181874451478315987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44475123151665203942175965 16678171181874451478315987)
  ·
    refine ⟨25017256772811677217473981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16678171181874451478315987 25017256772811677217473981)
    ·
      refine ⟨9381471289804378956552743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25017256772811677217473981 9381471289804378956552743)
      ·
        refine ⟨14072206934706568434829115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9381471289804378956552743 14072206934706568434829115)
        ·
          refine ⟨21108310402059852652243673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14072206934706568434829115 21108310402059852652243673)
          ·
            refine ⟨15831232801544889489182755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21108310402059852652243673 15831232801544889489182755)
            ·
              refine ⟨23746849202317334233774133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15831232801544889489182755 23746849202317334233774133)
              ·
                refine ⟨2226267112717250084416325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23746849202317334233774133 2226267112717250084416325)
                ·
                  refine ⟨417425083634484390828061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2226267112717250084416325 417425083634484390828061)
                  ·
                    rfl

theorem cell21_1829098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_1829098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829098 prefixEnd_1829098 := by exact prefixLift 1829098
  have htrace : WordTrace (prefixWord ++ tailWord_1829098) baseStart_1829098 baseEnd_1829098 := by
    simpa [prefixWord, tailWord_1829098, baseEnd_1829098] using wordTrace_append hprefix tailTrace_1829098
  have hstable : (prefixWord ++ tailWord_1829098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829098).length < 2 ^ (prefixWord ++ tailWord_1829098).sum := by decide
  have hdescent : baseEnd_1829098 < baseStart_1829098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829143 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 5]
def baseStart_1829143 : Nat := 118140960795 + 1829143 * 2 ^ 59
def prefixEnd_1829143 : Nat := 4983230072969 + 3 ^ 40 * 1829143 * 2
def baseEnd_1829143 : Nat := 417435353247574312577969

theorem tailTrace_1829143 : CollatzResearch.WordTrace tailWord_1829143 prefixEnd_1829143 417435353247574312577969 := by
  unfold tailWord_1829143
  simp only [CollatzResearch.WordTrace]
  refine ⟨66714326012334778598652083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44476217341556519065768055 66714326012334778598652083)
  ·
    refine ⟨100071489018502167897978125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66714326012334778598652083 100071489018502167897978125)
    ·
      refine ⟨37526808381938312961741797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100071489018502167897978125 37526808381938312961741797)
      ·
        refine ⟨7036276571613433680326587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37526808381938312961741797 7036276571613433680326587)
        ·
          refine ⟨10554414857420150520489881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7036276571613433680326587 10554414857420150520489881)
          ·
            refine ⟨7915811143065112890367411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10554414857420150520489881 7915811143065112890367411)
            ·
              refine ⟨11873716714597669335551117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915811143065112890367411 11873716714597669335551117)
              ·
                refine ⟨4452643767974126000831669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11873716714597669335551117 4452643767974126000831669)
                ·
                  refine ⟨417435353247574312577969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4452643767974126000831669 417435353247574312577969)
                  ·
                    rfl

theorem cell21_1829143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_1829143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829143 prefixEnd_1829143 := by exact prefixLift 1829143
  have htrace : WordTrace (prefixWord ++ tailWord_1829143) baseStart_1829143 baseEnd_1829143 := by
    simpa [prefixWord, tailWord_1829143, baseEnd_1829143] using wordTrace_append hprefix tailTrace_1829143
  have hstable : (prefixWord ++ tailWord_1829143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829143).length < 2 ^ (prefixWord ++ tailWord_1829143).sum := by decide
  have hdescent : baseEnd_1829143 < baseStart_1829143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829177 : List Nat := [1, 2, 1, 6, 1, 1, 3, 3, 3]
def baseStart_1829177 : Nat := 118140960795 + 1829177 * 2 ^ 59
def prefixEnd_1829177 : Nat := 4983230072969 + 3 ^ 40 * 1829177 * 2
def baseEnd_1829177 : Nat := 417443112510797809011233

theorem tailTrace_1829177 : CollatzResearch.WordTrace tailWord_1829177 prefixEnd_1829177 417443112510797809011233 := by
  unfold tailWord_1829177
  simp only [CollatzResearch.WordTrace]
  refine ⟨66715566094211602405389785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44477044062807734936926523 66715566094211602405389785)
  ·
    refine ⟨50036674570658701804042339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66715566094211602405389785 50036674570658701804042339)
    ·
      refine ⟨75055011855988052706063509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50036674570658701804042339 75055011855988052706063509)
      ·
        refine ⟨3518203680749439970596727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75055011855988052706063509 3518203680749439970596727)
        ·
          refine ⟨5277305521124159955895091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518203680749439970596727 5277305521124159955895091)
          ·
            refine ⟨7915958281686239933842637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277305521124159955895091 7915958281686239933842637)
            ·
              refine ⟨2968484355632339975190989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7915958281686239933842637 2968484355632339975190989)
              ·
                refine ⟨1113181633362127490696621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2968484355632339975190989 1113181633362127490696621)
                ·
                  refine ⟨417443112510797809011233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1113181633362127490696621 417443112510797809011233)
                  ·
                    rfl

theorem cell21_1829177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_1829177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829177 prefixEnd_1829177 := by exact prefixLift 1829177
  have htrace : WordTrace (prefixWord ++ tailWord_1829177) baseStart_1829177 baseEnd_1829177 := by
    simpa [prefixWord, tailWord_1829177, baseEnd_1829177] using wordTrace_append hprefix tailTrace_1829177
  have hstable : (prefixWord ++ tailWord_1829177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829177).length < 2 ^ (prefixWord ++ tailWord_1829177).sum := by decide
  have hdescent : baseEnd_1829177 < baseStart_1829177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829205 : List Nat := [1, 3, 2, 2, 4, 1, 2, 6]
def baseStart_1829205 : Nat := 118140960795 + 1829205 * 2 ^ 59
def prefixEnd_1829205 : Nat := 4983230072969 + 3 ^ 40 * 1829205 * 2
def baseEnd_1829205 : Nat := 139149834164091994181503

theorem tailTrace_1829205 : CollatzResearch.WordTrace tailWord_1829205 prefixEnd_1829205 139149834164091994181503 := by
  unfold tailWord_1829205
  simp only [CollatzResearch.WordTrace]
  refine ⟨66716587338110163187409069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44477724892073442124939379 66716587338110163187409069)
  ·
    refine ⟨25018720251791311195278401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66716587338110163187409069 25018720251791311195278401)
    ·
      refine ⟨18764040188843483396458801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25018720251791311195278401 18764040188843483396458801)
      ·
        refine ⟨14073030141632612547344101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18764040188843483396458801 14073030141632612547344101)
        ·
          refine ⟨2638693151556114852627019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14073030141632612547344101 2638693151556114852627019)
          ·
            refine ⟨3958039727334172278940529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638693151556114852627019 3958039727334172278940529)
            ·
              refine ⟨2968529795500629209205397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3958039727334172278940529 2968529795500629209205397)
              ·
                refine ⟨139149834164091994181503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2968529795500629209205397 139149834164091994181503)
                ·
                  rfl

theorem cell21_1829205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 6].length) (baseStart_1829205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829205 prefixEnd_1829205 := by exact prefixLift 1829205
  have htrace : WordTrace (prefixWord ++ tailWord_1829205) baseStart_1829205 baseEnd_1829205 := by
    simpa [prefixWord, tailWord_1829205, baseEnd_1829205] using wordTrace_append hprefix tailTrace_1829205
  have hstable : (prefixWord ++ tailWord_1829205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829205).length < 2 ^ (prefixWord ++ tailWord_1829205).sum := by decide
  have hdescent : baseEnd_1829205 < baseStart_1829205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829323 : List Nat := [1, 1, 1, 1, 3, 3, 1, 10]
def baseStart_1829323 : Nat := 118140960795 + 1829323 * 2 ^ 59
def prefixEnd_1829323 : Nat := 4983230072969 + 3 ^ 40 * 1829323 * 2
def baseEnd_1829323 : Nat := 139158810566644666525867

theorem tailTrace_1829323 : CollatzResearch.WordTrace tailWord_1829323 prefixEnd_1829323 139158810566644666525867 := by
  unfold tailWord_1829323
  simp only [CollatzResearch.WordTrace]
  refine ⟨66720891151682669340204623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44480594101121779560136415 66720891151682669340204623)
  ·
    refine ⟨100081336727524004010306935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66720891151682669340204623 100081336727524004010306935)
    ·
      refine ⟨150122005091286006015460403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100081336727524004010306935 150122005091286006015460403)
      ·
        refine ⟨225183007636929009023190605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150122005091286006015460403 225183007636929009023190605)
        ·
          refine ⟨84443627863848378383696477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225183007636929009023190605 84443627863848378383696477)
          ·
            refine ⟨31666360448943141893886179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84443627863848378383696477 31666360448943141893886179)
            ·
              refine ⟨47499540673414712840829269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31666360448943141893886179 47499540673414712840829269)
              ·
                refine ⟨139158810566644666525867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47499540673414712840829269 139158810566644666525867)
                ·
                  rfl

theorem cell21_1829323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 10].length) (baseStart_1829323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829323 prefixEnd_1829323 := by exact prefixLift 1829323
  have htrace : WordTrace (prefixWord ++ tailWord_1829323) baseStart_1829323 baseEnd_1829323 := by
    simpa [prefixWord, tailWord_1829323, baseEnd_1829323] using wordTrace_append hprefix tailTrace_1829323
  have hstable : (prefixWord ++ tailWord_1829323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829323).length < 2 ^ (prefixWord ++ tailWord_1829323).sum := by decide
  have hdescent : baseEnd_1829323 < baseStart_1829323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829357 : List Nat := [1, 5, 1, 3, 1, 3, 7]
def baseStart_1829357 : Nat := 118140960795 + 1829357 * 2 ^ 59
def prefixEnd_1829357 : Nat := 4983230072969 + 3 ^ 40 * 1829357 * 2
def baseEnd_1829357 : Nat := 46387132329239721778985

theorem tailTrace_1829357 : CollatzResearch.WordTrace tailWord_1829357 prefixEnd_1829357 46387132329239721778985 := by
  unfold tailWord_1829357
  simp only [CollatzResearch.WordTrace]
  refine ⟨66722131233559493146942325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44481420822372995431294883 66722131233559493146942325)
  ·
    refine ⟨6255199803146202482525843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66722131233559493146942325 6255199803146202482525843)
    ·
      refine ⟨9382799704719303723788765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6255199803146202482525843 9382799704719303723788765)
      ·
        refine ⟨3518549889269738896420787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9382799704719303723788765 3518549889269738896420787)
        ·
          refine ⟨5277824833904608344631181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518549889269738896420787 5277824833904608344631181)
          ·
            refine ⟨1979184312714228129236693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5277824833904608344631181 1979184312714228129236693)
            ·
              refine ⟨46387132329239721778985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1979184312714228129236693 46387132329239721778985)
              ·
                rfl

theorem cell21_1829357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 7].length) (baseStart_1829357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829357 prefixEnd_1829357 := by exact prefixLift 1829357
  have htrace : WordTrace (prefixWord ++ tailWord_1829357) baseStart_1829357 baseEnd_1829357 := by
    simpa [prefixWord, tailWord_1829357, baseEnd_1829357] using wordTrace_append hprefix tailTrace_1829357
  have hstable : (prefixWord ++ tailWord_1829357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829357).length < 2 ^ (prefixWord ++ tailWord_1829357).sum := by decide
  have hdescent : baseEnd_1829357 < baseStart_1829357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829416 : List Nat := [2, 1, 5, 2, 1, 10]
def baseStart_1829416 : Nat := 118140960795 + 1829416 * 2 ^ 59
def prefixEnd_1829416 : Nat := 4983230072969 + 3 ^ 40 * 1829416 * 2
def baseEnd_1829416 : Nat := 15462876132110611278793

theorem tailTrace_1829416 : CollatzResearch.WordTrace tailWord_1829416 prefixEnd_1829416 15462876132110611278793 := by
  unfold tailWord_1829416
  simp only [CollatzResearch.WordTrace]
  refine ⟨33362141570172873111670051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44482855426897164148893401 33362141570172873111670051)
  ·
    refine ⟨50043212355259309667505077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33362141570172873111670051 50043212355259309667505077)
    ·
      refine ⟨4691551158305560281328601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50043212355259309667505077 4691551158305560281328601)
      ·
        refine ⟨3518663368729170210996451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4691551158305560281328601 3518663368729170210996451)
        ·
          refine ⟨5277995053093755316494677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518663368729170210996451 5277995053093755316494677)
          ·
            refine ⟨15462876132110611278793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5277995053093755316494677 15462876132110611278793)
            ·
              rfl

theorem cell21_1829416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 10].length) (baseStart_1829416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829416 prefixEnd_1829416 := by exact prefixLift 1829416
  have htrace : WordTrace (prefixWord ++ tailWord_1829416) baseStart_1829416 baseEnd_1829416 := by
    simpa [prefixWord, tailWord_1829416, baseEnd_1829416] using wordTrace_append hprefix tailTrace_1829416
  have hstable : (prefixWord ++ tailWord_1829416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829416).length < 2 ^ (prefixWord ++ tailWord_1829416).sum := by decide
  have hdescent : baseEnd_1829416 < baseStart_1829416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829447 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 5]
def baseStart_1829447 : Nat := 118140960795 + 1829447 * 2 ^ 59
def prefixEnd_1829447 : Nat := 4983230072969 + 3 ^ 40 * 1829447 * 2
def baseEnd_1829447 : Nat := 417504730189337339510681

theorem tailTrace_1829447 : CollatzResearch.WordTrace tailWord_1829447 prefixEnd_1829447 417504730189337339510681 := by
  unfold tailWord_1829447
  simp only [CollatzResearch.WordTrace]
  refine ⟨66725413803233438517718595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44483609202155625678479063 66725413803233438517718595)
  ·
    refine ⟨100088120704850157776577893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66725413803233438517718595 100088120704850157776577893)
    ·
      refine ⟨18766522632159404583108355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100088120704850157776577893 18766522632159404583108355)
      ·
        refine ⟨28149783948239106874662533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18766522632159404583108355 28149783948239106874662533)
        ·
          refine ⟨5278084490294832538999225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28149783948239106874662533 5278084490294832538999225)
          ·
            refine ⟨3958563367721124404249419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278084490294832538999225 3958563367721124404249419)
            ·
              refine ⟨5937845051581686606374129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958563367721124404249419 5937845051581686606374129)
              ·
                refine ⟨4453383788686264954780597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5937845051581686606374129 4453383788686264954780597)
                ·
                  refine ⟨417504730189337339510681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4453383788686264954780597 417504730189337339510681)
                  ·
                    rfl

theorem cell21_1829447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 5].length) (baseStart_1829447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829447 prefixEnd_1829447 := by exact prefixLift 1829447
  have htrace : WordTrace (prefixWord ++ tailWord_1829447) baseStart_1829447 baseEnd_1829447 := by
    simpa [prefixWord, tailWord_1829447, baseEnd_1829447] using wordTrace_append hprefix tailTrace_1829447
  have hstable : (prefixWord ++ tailWord_1829447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829447).length < 2 ^ (prefixWord ++ tailWord_1829447).sum := by decide
  have hdescent : baseEnd_1829447 < baseStart_1829447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829470 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1829470 : Nat := 118140960795 + 1829470 * 2 ^ 59
def prefixEnd_1829470 : Nat := 4983230072969 + 3 ^ 40 * 1829470 * 2
def baseEnd_1829470 : Nat := 417509979102694410627301

theorem tailTrace_1829470 : CollatzResearch.WordTrace tailWord_1829470 prefixEnd_1829470 417509979102694410627301 := by
  unfold tailWord_1829470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8340781585268764180725733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44484168454766742297203909 8340781585268764180725733)
  ·
    refine ⟨1563896547237893283886075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8340781585268764180725733 1563896547237893283886075)
    ·
      refine ⟨2345844820856839925829113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1563896547237893283886075 2345844820856839925829113)
      ·
        refine ⟨1759383615642629944371835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2345844820856839925829113 1759383615642629944371835)
        ·
          refine ⟨2639075423463944916557753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1759383615642629944371835 2639075423463944916557753)
          ·
            refine ⟨1979306567597958687418315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2639075423463944916557753 1979306567597958687418315)
            ·
              refine ⟨2968959851396938031127473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1979306567597958687418315 2968959851396938031127473)
              ·
                refine ⟨2226719888547703523345605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2968959851396938031127473 2226719888547703523345605)
                ·
                  refine ⟨417509979102694410627301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2226719888547703523345605 417509979102694410627301)
                  ·
                    rfl

theorem cell21_1829470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1829470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829470 prefixEnd_1829470 := by exact prefixLift 1829470
  have htrace : WordTrace (prefixWord ++ tailWord_1829470) baseStart_1829470 baseEnd_1829470 := by
    simpa [prefixWord, tailWord_1829470, baseEnd_1829470] using wordTrace_append hprefix tailTrace_1829470
  have hstable : (prefixWord ++ tailWord_1829470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829470).length < 2 ^ (prefixWord ++ tailWord_1829470).sum := by decide
  have hdescent : baseEnd_1829470 < baseStart_1829470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829475 : List Nat := [1, 1, 1, 5, 1, 2, 10]
def baseStart_1829475 : Nat := 118140960795 + 1829475 * 2 ^ 59
def prefixEnd_1829475 : Nat := 4983230072969 + 3 ^ 40 * 1829475 * 2
def baseEnd_1829475 : Nat := 46390124463423945893773

theorem tailTrace_1829475 : CollatzResearch.WordTrace tailWord_1829475 prefixEnd_1829475 46390124463423945893773 := by
  unfold tailWord_1829475
  simp only [CollatzResearch.WordTrace]
  refine ⟨66726435047131999299737879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44484290031421332866491919 66726435047131999299737879)
  ·
    refine ⟨100089652570697998949606819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66726435047131999299737879 100089652570697998949606819)
    ·
      refine ⟨150134478856046998424410229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100089652570697998949606819 150134478856046998424410229)
      ·
        refine ⟨14075107392754406102288459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150134478856046998424410229 14075107392754406102288459)
        ·
          refine ⟨21112661089131609153432689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14075107392754406102288459 21112661089131609153432689)
          ·
            refine ⟨15834495816848706865074517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21112661089131609153432689 15834495816848706865074517)
            ·
              refine ⟨46390124463423945893773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15834495816848706865074517 46390124463423945893773)
              ·
                rfl

theorem cell21_1829475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 10].length) (baseStart_1829475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829475 prefixEnd_1829475 := by exact prefixLift 1829475
  have htrace : WordTrace (prefixWord ++ tailWord_1829475) baseStart_1829475 baseEnd_1829475 := by
    simpa [prefixWord, tailWord_1829475, baseEnd_1829475] using wordTrace_append hprefix tailTrace_1829475
  have hstable : (prefixWord ++ tailWord_1829475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829475).length < 2 ^ (prefixWord ++ tailWord_1829475).sum := by decide
  have hdescent : baseEnd_1829475 < baseStart_1829475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829509 : List Nat := [1, 3, 1, 1, 4, 4, 2, 5]
def baseStart_1829509 : Nat := 118140960795 + 1829509 * 2 ^ 59
def prefixEnd_1829509 : Nat := 4983230072969 + 3 ^ 40 * 1829509 * 2
def baseEnd_1829509 : Nat := 139172959811346336492407

theorem tailTrace_1829509 : CollatzResearch.WordTrace tailWord_1829509 prefixEnd_1829509 139172959811346336492407 := by
  unfold tailWord_1829509
  simp only [CollatzResearch.WordTrace]
  refine ⟨66727675129008823106475581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44485116752672548737650387 66727675129008823106475581)
  ·
    refine ⟨25022878173378308664928343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66727675129008823106475581 25022878173378308664928343)
    ·
      refine ⟨37534317260067462997392515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25022878173378308664928343 37534317260067462997392515)
      ·
        refine ⟨56301475890101194496088773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37534317260067462997392515 56301475890101194496088773)
        ·
          refine ⟨10556526729393973968016645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56301475890101194496088773 10556526729393973968016645)
          ·
            refine ⟨1979348761761370119003121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10556526729393973968016645 1979348761761370119003121)
            ·
              refine ⟨1484511571321027589252341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1979348761761370119003121 1484511571321027589252341)
              ·
                refine ⟨139172959811346336492407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1484511571321027589252341 139172959811346336492407)
                ·
                  rfl

theorem cell21_1829509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 5].length) (baseStart_1829509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829509 prefixEnd_1829509 := by exact prefixLift 1829509
  have htrace : WordTrace (prefixWord ++ tailWord_1829509) baseStart_1829509 baseEnd_1829509 := by
    simpa [prefixWord, tailWord_1829509, baseEnd_1829509] using wordTrace_append hprefix tailTrace_1829509
  have hstable : (prefixWord ++ tailWord_1829509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829509).length < 2 ^ (prefixWord ++ tailWord_1829509).sum := by decide
  have hdescent : baseEnd_1829509 < baseStart_1829509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829546 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 4]
def baseStart_1829546 : Nat := 118140960795 + 1829546 * 2 ^ 59
def prefixEnd_1829546 : Nat := 4983230072969 + 3 ^ 40 * 1829546 * 2
def baseEnd_1829546 : Nat := 417527323338135167360479

theorem tailTrace_1829546 : CollatzResearch.WordTrace tailWord_1829546 prefixEnd_1829546 417527323338135167360479 := by
  unfold tailWord_1829546
  simp only [CollatzResearch.WordTrace]
  refine ⟨16682256157468694606393123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44486016419916518950381661 16682256157468694606393123)
  ·
    refine ⟨25023384236203041909589685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16682256157468694606393123 25023384236203041909589685)
    ·
      refine ⟨2345942272144035179024033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25023384236203041909589685 2345942272144035179024033)
      ·
        refine ⟨1759456704108026384268025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2345942272144035179024033 1759456704108026384268025)
        ·
          refine ⟨1319592528081019788201019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1759456704108026384268025 1319592528081019788201019)
          ·
            refine ⟨1979388792121529682301529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319592528081019788201019 1979388792121529682301529)
            ·
              refine ⟨1484541594091147261726147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1979388792121529682301529 1484541594091147261726147)
              ·
                refine ⟨2226812391136720892589221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1484541594091147261726147 2226812391136720892589221)
                ·
                  refine ⟨417527323338135167360479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2226812391136720892589221 417527323338135167360479)
                  ·
                    rfl

theorem cell21_1829546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_1829546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829546 prefixEnd_1829546 := by exact prefixLift 1829546
  have htrace : WordTrace (prefixWord ++ tailWord_1829546) baseStart_1829546 baseEnd_1829546 := by
    simpa [prefixWord, tailWord_1829546, baseEnd_1829546] using wordTrace_append hprefix tailTrace_1829546
  have hstable : (prefixWord ++ tailWord_1829546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829546).length < 2 ^ (prefixWord ++ tailWord_1829546).sum := by decide
  have hdescent : baseEnd_1829546 < baseStart_1829546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829551 : List Nat := [1, 1, 2, 1, 2, 5, 1, 8]
def baseStart_1829551 : Nat := 118140960795 + 1829551 * 2 ^ 59
def prefixEnd_1829551 : Nat := 4983230072969 + 3 ^ 40 * 1829551 * 2
def baseEnd_1829551 : Nat := 139176154802085423259045

theorem tailTrace_1829551 : CollatzResearch.WordTrace tailWord_1829551 prefixEnd_1829551 139176154802085423259045 := by
  unfold tailWord_1829551
  simp only [CollatzResearch.WordTrace]
  refine ⟨66729206994856664279504507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44486137996571109519669671 66729206994856664279504507)
  ·
    refine ⟨100093810492284996419256761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66729206994856664279504507 100093810492284996419256761)
    ·
      refine ⟨75070357869213747314442571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100093810492284996419256761 75070357869213747314442571)
      ·
        refine ⟨112605536803820620971663857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75070357869213747314442571 112605536803820620971663857)
        ·
          refine ⟨84454152602865465728747893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112605536803820620971663857 84454152602865465728747893)
          ·
            refine ⟨7917576806518637412070115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84454152602865465728747893 7917576806518637412070115)
            ·
              refine ⟨11876365209777956118105173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7917576806518637412070115 11876365209777956118105173)
              ·
                refine ⟨139176154802085423259045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11876365209777956118105173 139176154802085423259045)
                ·
                  rfl

theorem cell21_1829551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 8].length) (baseStart_1829551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829551 prefixEnd_1829551 := by exact prefixLift 1829551
  have htrace : WordTrace (prefixWord ++ tailWord_1829551) baseStart_1829551 baseEnd_1829551 := by
    simpa [prefixWord, tailWord_1829551, baseEnd_1829551] using wordTrace_append hprefix tailTrace_1829551
  have hstable : (prefixWord ++ tailWord_1829551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829551).length < 2 ^ (prefixWord ++ tailWord_1829551).sum := by decide
  have hdescent : baseEnd_1829551 < baseStart_1829551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1829678 : List Nat := [4, 1, 3, 2, 1, 3, 2, 5]
def baseStart_1829678 : Nat := 118140960795 + 1829678 * 2 ^ 59
def prefixEnd_1829678 : Nat := 4983230072969 + 3 ^ 40 * 1829678 * 2
def baseEnd_1829678 : Nat := 139185815845510757053403

theorem tailTrace_1829678 : CollatzResearch.WordTrace tailWord_1829678 prefixEnd_1829678 139185815845510757053403 := by
  unfold tailWord_1829678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341729883174570621172211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44489226043597709979585125 8341729883174570621172211)
  ·
    refine ⟨12512594824761855931758317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8341729883174570621172211 12512594824761855931758317)
    ·
      refine ⟨4692223059285695974409369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12512594824761855931758317 4692223059285695974409369)
      ·
        refine ⟨3519167294464271980807027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4692223059285695974409369 3519167294464271980807027)
        ·
          refine ⟨5278750941696407971210541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519167294464271980807027 5278750941696407971210541)
          ·
            refine ⟨1979531603136152989203953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5278750941696407971210541 1979531603136152989203953)
            ·
              refine ⟨1484648702352114741902965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1979531603136152989203953 1484648702352114741902965)
              ·
                refine ⟨139185815845510757053403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1484648702352114741902965 139185815845510757053403)
                ·
                  rfl

theorem cell21_1829678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_1829678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1829678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1829678 prefixEnd_1829678 := by exact prefixLift 1829678
  have htrace : WordTrace (prefixWord ++ tailWord_1829678) baseStart_1829678 baseEnd_1829678 := by
    simpa [prefixWord, tailWord_1829678, baseEnd_1829678] using wordTrace_append hprefix tailTrace_1829678
  have hstable : (prefixWord ++ tailWord_1829678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1829678).length < 2 ^ (prefixWord ++ tailWord_1829678).sum := by decide
  have hdescent : baseEnd_1829678 < baseStart_1829678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1829678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
