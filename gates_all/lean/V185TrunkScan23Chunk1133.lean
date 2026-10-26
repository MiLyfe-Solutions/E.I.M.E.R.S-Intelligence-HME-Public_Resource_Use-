import V185TrunkScan23Chunk1132

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6710833 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 2, 2, 2]
def baseStart_6710833 : Nat := 118140960795 + 6710833 * 2 ^ 59
def prefixEnd_6710833 : Nat := 4983230072969 + 3 ^ 40 * 6710833 * 2
def baseEnd_6710833 : Nat := 3445882921054047568724947

theorem tailTrace_6710833 : CollatzResearch.WordTrace tailWord_6710833 prefixEnd_6710833 3445882921054047568724947 := by
  unfold tailWord_6710833
  simp only [CollatzResearch.WordTrace]
  refine ⟨244764187696805634874313153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163176125131203756582875435 244764187696805634874313153)
  ·
    refine ⟨183573140772604226155734865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244764187696805634874313153 183573140772604226155734865)
    ·
      refine ⟨137679855579453169616801149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183573140772604226155734865 137679855579453169616801149)
      ·
        refine ⟨51629945842294938606300431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137679855579453169616801149 51629945842294938606300431)
        ·
          refine ⟨77444918763442407909450647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51629945842294938606300431 77444918763442407909450647)
          ·
            refine ⟨116167378145163611864175971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77444918763442407909450647 116167378145163611864175971)
            ·
              refine ⟨174251067217745417796263957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116167378145163611864175971 174251067217745417796263957)
              ·
                refine ⟨8168018775831816459199873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174251067217745417796263957 8168018775831816459199873)
                ·
                  refine ⟨6126014081873862344399905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8168018775831816459199873 6126014081873862344399905)
                  ·
                    refine ⟨4594510561405396758299929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6126014081873862344399905 4594510561405396758299929)
                    ·
                      refine ⟨3445882921054047568724947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594510561405396758299929 3445882921054047568724947)
                      ·
                        rfl

theorem cell23_6710833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_6710833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710833 prefixEnd_6710833 := by exact prefixLift 6710833
  have htrace : WordTrace (prefixWord ++ tailWord_6710833) baseStart_6710833 baseEnd_6710833 := by
    simpa [prefixWord, tailWord_6710833, baseEnd_6710833] using wordTrace_append hprefix tailTrace_6710833
  have hstable : (prefixWord ++ tailWord_6710833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710833).length < 2 ^ (prefixWord ++ tailWord_6710833).sum := by decide
  have hdescent : baseEnd_6710833 < baseStart_6710833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710839 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 7]
def baseStart_6710839 : Nat := 118140960795 + 6710839 * 2 ^ 59
def prefixEnd_6710839 : Nat := 4983230072969 + 3 ^ 40 * 6710839 * 2
def baseEnd_6710839 : Nat := 382876222437552727249991

theorem tailTrace_6710839 : CollatzResearch.WordTrace tailWord_6710839 prefixEnd_6710839 382876222437552727249991 := by
  unfold tailWord_6710839
  simp only [CollatzResearch.WordTrace]
  refine ⟨244764406534783897899031571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163176271023189265266021047 244764406534783897899031571)
  ·
    refine ⟨367146609802175846848547357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244764406534783897899031571 367146609802175846848547357)
    ·
      refine ⟨137679978675815942568205259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367146609802175846848547357 137679978675815942568205259)
      ·
        refine ⟨206519968013723913852307889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137679978675815942568205259 206519968013723913852307889)
        ·
          refine ⟨154889976010292935389230917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206519968013723913852307889 154889976010292935389230917)
          ·
            refine ⟨29041870501929925385480797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154889976010292935389230917 29041870501929925385480797)
            ·
              refine ⟨10890701438223722019555299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29041870501929925385480797 10890701438223722019555299)
              ·
                refine ⟨16336052157335583029332949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10890701438223722019555299 16336052157335583029332949)
                ·
                  refine ⟨382876222437552727249991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16336052157335583029332949 382876222437552727249991)
                  ·
                    rfl

theorem cell23_6710839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 7].length) (baseStart_6710839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710839 prefixEnd_6710839 := by exact prefixLift 6710839
  have htrace : WordTrace (prefixWord ++ tailWord_6710839) baseStart_6710839 baseEnd_6710839 := by
    simpa [prefixWord, tailWord_6710839, baseEnd_6710839] using wordTrace_append hprefix tailTrace_6710839
  have hstable : (prefixWord ++ tailWord_6710839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710839).length < 2 ^ (prefixWord ++ tailWord_6710839).sum := by decide
  have hdescent : baseEnd_6710839 < baseStart_6710839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710854 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_6710854 : Nat := 118140960795 + 6710854 * 2 ^ 59
def prefixEnd_6710854 : Nat := 4983230072969 + 3 ^ 40 * 6710854 * 2
def baseEnd_6710854 : Nat := 3445893704147791986562351

theorem tailTrace_6710854 : CollatzResearch.WordTrace tailWord_6710854 prefixEnd_6710854 3445893704147791986562351 := by
  unfold tailWord_6710854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648904800929048608150863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163176635753153036973885077 7648904800929048608150863)
  ·
    refine ⟨11473357201393572912226295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7648904800929048608150863 11473357201393572912226295)
    ·
      refine ⟨17210035802090359368339443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11473357201393572912226295 17210035802090359368339443)
      ·
        refine ⟨25815053703135539052509165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17210035802090359368339443 25815053703135539052509165)
        ·
          refine ⟨9680645138675827144690937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25815053703135539052509165 9680645138675827144690937)
          ·
            refine ⟨7260483854006870358518203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9680645138675827144690937 7260483854006870358518203)
            ·
              refine ⟨10890725781010305537777305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7260483854006870358518203 10890725781010305537777305)
              ·
                refine ⟨8168044335757729153332979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10890725781010305537777305 8168044335757729153332979)
                ·
                  refine ⟨12252066503636593729999469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8168044335757729153332979 12252066503636593729999469)
                  ·
                    refine ⟨4594524938863722648749801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12252066503636593729999469 4594524938863722648749801)
                    ·
                      refine ⟨3445893704147791986562351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594524938863722648749801 3445893704147791986562351)
                      ·
                        rfl

theorem cell23_6710854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_6710854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710854 prefixEnd_6710854 := by exact prefixLift 6710854
  have htrace : WordTrace (prefixWord ++ tailWord_6710854) baseStart_6710854 baseEnd_6710854 := by
    simpa [prefixWord, tailWord_6710854, baseEnd_6710854] using wordTrace_append hprefix tailTrace_6710854
  have hstable : (prefixWord ++ tailWord_6710854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710854).length < 2 ^ (prefixWord ++ tailWord_6710854).sum := by decide
  have hdescent : baseEnd_6710854 < baseStart_6710854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710890 : List Nat := [3, 1, 3, 2, 1, 4, 2, 2, 5]
def baseStart_6710890 : Nat := 118140960795 + 6710890 * 2 ^ 59
def prefixEnd_6710890 : Nat := 4983230072969 + 3 ^ 40 * 6710890 * 2
def baseEnd_6710890 : Nat := 382879132161261538412465

theorem tailTrace_6710890 : CollatzResearch.WordTrace tailWord_6710890 prefixEnd_6710890 382879132161261538412465 := by
  unfold tailWord_6710890
  simp only [CollatzResearch.WordTrace]
  refine ⟨61191566664399783402284531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163177511105066089072758749 61191566664399783402284531)
  ·
    refine ⟨91787349996599675103426797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61191566664399783402284531 91787349996599675103426797)
    ·
      refine ⟨34420256248724878163785049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91787349996599675103426797 34420256248724878163785049)
      ·
        refine ⟨25815192186543658622838787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34420256248724878163785049 25815192186543658622838787)
        ·
          refine ⟨38722788279815487934258181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25815192186543658622838787 38722788279815487934258181)
          ·
            refine ⟨7260522802465403987673409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38722788279815487934258181 7260522802465403987673409)
            ·
              refine ⟨5445392101849052990755057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7260522802465403987673409 5445392101849052990755057)
              ·
                refine ⟨4084044076386789743066293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5445392101849052990755057 4084044076386789743066293)
                ·
                  refine ⟨382879132161261538412465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4084044076386789743066293 382879132161261538412465)
                  ·
                    rfl

theorem cell23_6710890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 5].length) (baseStart_6710890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710890 prefixEnd_6710890 := by exact prefixLift 6710890
  have htrace : WordTrace (prefixWord ++ tailWord_6710890) baseStart_6710890 baseEnd_6710890 := by
    simpa [prefixWord, tailWord_6710890, baseEnd_6710890] using wordTrace_append hprefix tailTrace_6710890
  have hstable : (prefixWord ++ tailWord_6710890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710890).length < 2 ^ (prefixWord ++ tailWord_6710890).sum := by decide
  have hdescent : baseEnd_6710890 < baseStart_6710890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710920 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 2, 5]
def baseStart_6710920 : Nat := 118140960795 + 6710920 * 2 ^ 59
def prefixEnd_6710920 : Nat := 4983230072969 + 3 ^ 40 * 6710920 * 2
def baseEnd_6710920 : Nat := 1148642531290329576112349

theorem tailTrace_6710920 : CollatzResearch.WordTrace tailWord_6710920 prefixEnd_6710920 1148642531290329576112349 := by
  unfold tailWord_6710920
  simp only [CollatzResearch.WordTrace]
  refine ⟨122383680423745224366365107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163178240564993632488486809 122383680423745224366365107)
  ·
    refine ⟨183575520635617836549547661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122383680423745224366365107 183575520635617836549547661)
    ·
      refine ⟨68840820238356688706080373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183575520635617836549547661 68840820238356688706080373)
      ·
        refine ⟨6453826897345939566195035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68840820238356688706080373 6453826897345939566195035)
        ·
          refine ⟨9680740346018909349292553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6453826897345939566195035 9680740346018909349292553)
          ·
            refine ⟨7260555259514182011969415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9680740346018909349292553 7260555259514182011969415)
            ·
              refine ⟨10890832889271273017954123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7260555259514182011969415 10890832889271273017954123)
              ·
                refine ⟨16336249333906909526931185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10890832889271273017954123 16336249333906909526931185)
                ·
                  refine ⟨12252187000430182145198389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16336249333906909526931185 12252187000430182145198389)
                  ·
                    refine ⟨1148642531290329576112349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12252187000430182145198389 1148642531290329576112349)
                    ·
                      rfl

theorem cell23_6710920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_6710920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710920 prefixEnd_6710920 := by exact prefixLift 6710920
  have htrace : WordTrace (prefixWord ++ tailWord_6710920) baseStart_6710920 baseEnd_6710920 := by
    simpa [prefixWord, tailWord_6710920, baseEnd_6710920] using wordTrace_append hprefix tailTrace_6710920
  have hstable : (prefixWord ++ tailWord_6710920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710920).length < 2 ^ (prefixWord ++ tailWord_6710920).sum := by decide
  have hdescent : baseEnd_6710920 < baseStart_6710920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710949 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_6710949 : Nat := 118140960795 + 6710949 * 2 ^ 59
def prefixEnd_6710949 : Nat := 4983230072969 + 3 ^ 40 * 6710949 * 2
def baseEnd_6710949 : Nat := 3445942484809969114874413

theorem tailTrace_6710949 : CollatzResearch.WordTrace tailWord_6710949 prefixEnd_6710949 3445942484809969114874413 := by
  unfold tailWord_6710949
  simp only [CollatzResearch.WordTrace]
  refine ⟨244768418564385386685535901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163178945709590257790357267 244768418564385386685535901)
  ·
    refine ⟨91788156961644520007075963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244768418564385386685535901 91788156961644520007075963)
    ·
      refine ⟨137682235442466780010613945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91788156961644520007075963 137682235442466780010613945)
      ·
        refine ⟨103261676581850085007960459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137682235442466780010613945 103261676581850085007960459)
        ·
          refine ⟨154892514872775127511940689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103261676581850085007960459 154892514872775127511940689)
          ·
            refine ⟨116169386154581345633955517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154892514872775127511940689 116169386154581345633955517)
            ·
              refine ⟨43563519807968004612733319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116169386154581345633955517 43563519807968004612733319)
              ·
                refine ⟨65345279711952006919099979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43563519807968004612733319 65345279711952006919099979)
                ·
                  refine ⟨98017919567928010378649969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65345279711952006919099979 98017919567928010378649969)
                  ·
                    refine ⟨73513439675946007783987477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98017919567928010378649969 73513439675946007783987477)
                    ·
                      refine ⟨3445942484809969114874413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73513439675946007783987477 3445942484809969114874413)
                      ·
                        rfl

theorem cell23_6710949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_6710949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710949 prefixEnd_6710949 := by exact prefixLift 6710949
  have htrace : WordTrace (prefixWord ++ tailWord_6710949) baseStart_6710949 baseEnd_6710949 := by
    simpa [prefixWord, tailWord_6710949, baseEnd_6710949] using wordTrace_append hprefix tailTrace_6710949
  have hstable : (prefixWord ++ tailWord_6710949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710949).length < 2 ^ (prefixWord ++ tailWord_6710949).sum := by decide
  have hdescent : baseEnd_6710949 < baseStart_6710949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710969 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_6710969 : Nat := 118140960795 + 6710969 * 2 ^ 59
def prefixEnd_6710969 : Nat := 4983230072969 + 3 ^ 40 * 6710969 * 2
def baseEnd_6710969 : Nat := 3445952754423059036624321

theorem tailTrace_6710969 : CollatzResearch.WordTrace tailWord_6710969 prefixEnd_6710969 3445952754423059036624321 := by
  unfold tailWord_6710969
  simp only [CollatzResearch.WordTrace]
  refine ⟨244769148024312930101263961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163179432016208620067509307 244769148024312930101263961)
  ·
    refine ⟨183576861018234697575947971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244769148024312930101263961 183576861018234697575947971)
    ·
      refine ⟨275365291527352046363921957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183576861018234697575947971 275365291527352046363921957)
      ·
        refine ⟨51630992161378508693235367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275365291527352046363921957 51630992161378508693235367)
        ·
          refine ⟨77446488242067763039853051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51630992161378508693235367 77446488242067763039853051)
          ·
            refine ⟨116169732363101644559779577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77446488242067763039853051 116169732363101644559779577)
            ·
              refine ⟨87127299272326233419834683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116169732363101644559779577 87127299272326233419834683)
              ·
                refine ⟨130690948908489350129752025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87127299272326233419834683 130690948908489350129752025)
                ·
                  refine ⟨98018211681367012597314019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130690948908489350129752025 98018211681367012597314019)
                  ·
                    refine ⟨147027317522050518895971029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98018211681367012597314019 147027317522050518895971029)
                    ·
                      refine ⟨3445952754423059036624321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147027317522050518895971029 3445952754423059036624321)
                      ·
                        rfl

theorem cell23_6710969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_6710969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710969 prefixEnd_6710969 := by exact prefixLift 6710969
  have htrace : WordTrace (prefixWord ++ tailWord_6710969) baseStart_6710969 baseEnd_6710969 := by
    simpa [prefixWord, tailWord_6710969, baseEnd_6710969] using wordTrace_append hprefix tailTrace_6710969
  have hstable : (prefixWord ++ tailWord_6710969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710969).length < 2 ^ (prefixWord ++ tailWord_6710969).sum := by decide
  have hdescent : baseEnd_6710969 < baseStart_6710969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710973 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_6710973 : Nat := 118140960795 + 6710973 * 2 ^ 59
def prefixEnd_6710973 : Nat := 4983230072969 + 3 ^ 40 * 6710973 * 2
def baseEnd_6710973 : Nat := 3445954808345677020974303

theorem tailTrace_6710973 : CollatzResearch.WordTrace tailWord_6710973 prefixEnd_6710973 3445954808345677020974303 := by
  unfold tailWord_6710973
  simp only [CollatzResearch.WordTrace]
  refine ⟨244769293916298438784409573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163179529277532292522939715 244769293916298438784409573)
  ·
    refine ⟨45894242609305957272076795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244769293916298438784409573 45894242609305957272076795)
    ·
      refine ⟨68841363913958935908115193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45894242609305957272076795 68841363913958935908115193)
      ·
        refine ⟨51631022935469201931086395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68841363913958935908115193 51631022935469201931086395)
        ·
          refine ⟨77446534403203802896629593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51631022935469201931086395 77446534403203802896629593)
          ·
            refine ⟨58084900802402852172472195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77446534403203802896629593 58084900802402852172472195)
            ·
              refine ⟨87127351203604278258708293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58084900802402852172472195 87127351203604278258708293)
              ·
                refine ⟨16336378350675802173507805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87127351203604278258708293 16336378350675802173507805)
                ·
                  refine ⟨6126141881503425815065427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16336378350675802173507805 6126141881503425815065427)
                  ·
                    refine ⟨9189212822255138722598141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6126141881503425815065427 9189212822255138722598141)
                    ·
                      refine ⟨3445954808345677020974303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9189212822255138722598141 3445954808345677020974303)
                      ·
                        rfl

theorem cell23_6710973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_6710973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710973 prefixEnd_6710973 := by exact prefixLift 6710973
  have htrace : WordTrace (prefixWord ++ tailWord_6710973) baseStart_6710973 baseEnd_6710973 := by
    simpa [prefixWord, tailWord_6710973, baseEnd_6710973] using wordTrace_append hprefix tailTrace_6710973
  have hstable : (prefixWord ++ tailWord_6710973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710973).length < 2 ^ (prefixWord ++ tailWord_6710973).sum := by decide
  have hdescent : baseEnd_6710973 < baseStart_6710973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710979 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 4]
def baseStart_6710979 : Nat := 118140960795 + 6710979 * 2 ^ 59
def prefixEnd_6710979 : Nat := 4983230072969 + 3 ^ 40 * 6710979 * 2
def baseEnd_6710979 : Nat := 3445957889229603997499275

theorem tailTrace_6710979 : CollatzResearch.WordTrace tailWord_6710979 prefixEnd_6710979 3445957889229603997499275 := by
  unfold tailWord_6710979
  simp only [CollatzResearch.WordTrace]
  refine ⟨244769512754276701809127991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163179675169517801206085327 244769512754276701809127991)
  ·
    refine ⟨367154269131415052713691987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244769512754276701809127991 367154269131415052713691987)
    ·
      refine ⟨550731403697122579070537981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367154269131415052713691987 550731403697122579070537981)
      ·
        refine ⟨206524276386420967151451743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550731403697122579070537981 206524276386420967151451743)
        ·
          refine ⟨309786414579631450727177615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206524276386420967151451743 309786414579631450727177615)
          ·
            refine ⟨464679621869447176090766423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309786414579631450727177615 464679621869447176090766423)
            ·
              refine ⟨697019432804170764136149635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464679621869447176090766423 697019432804170764136149635)
              ·
                refine ⟨1045529149206256146204224453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697019432804170764136149635 1045529149206256146204224453)
                ·
                  refine ⟨196036715476173027413292085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045529149206256146204224453 196036715476173027413292085)
                  ·
                    refine ⟨18378442075891221319996133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 196036715476173027413292085 18378442075891221319996133)
                    ·
                      refine ⟨3445957889229603997499275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18378442075891221319996133 3445957889229603997499275)
                      ·
                        rfl

theorem cell23_6710979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_6710979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710979 prefixEnd_6710979 := by exact prefixLift 6710979
  have htrace : WordTrace (prefixWord ++ tailWord_6710979) baseStart_6710979 baseEnd_6710979 := by
    simpa [prefixWord, tailWord_6710979, baseEnd_6710979] using wordTrace_append hprefix tailTrace_6710979
  have hstable : (prefixWord ++ tailWord_6710979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710979).length < 2 ^ (prefixWord ++ tailWord_6710979).sum := by decide
  have hdescent : baseEnd_6710979 < baseStart_6710979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6710983 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_6710983 : Nat := 118140960795 + 6710983 * 2 ^ 59
def prefixEnd_6710983 : Nat := 4983230072969 + 3 ^ 40 * 6710983 * 2
def baseEnd_6710983 : Nat := 3445959943152221981849257

theorem tailTrace_6710983 : CollatzResearch.WordTrace tailWord_6710983 prefixEnd_6710983 3445959943152221981849257 := by
  unfold tailWord_6710983
  simp only [CollatzResearch.WordTrace]
  refine ⟨244769658646262210492273603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163179772430841473661515735 244769658646262210492273603)
  ·
    refine ⟨367154487969393315738410405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244769658646262210492273603 367154487969393315738410405)
    ·
      refine ⟨68841466494261246700951951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367154487969393315738410405 68841466494261246700951951)
      ·
        refine ⟨103262199741391870051427927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68841466494261246700951951 103262199741391870051427927)
        ·
          refine ⟨154893299612087805077141891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103262199741391870051427927 154893299612087805077141891)
          ·
            refine ⟨232339949418131707615712837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154893299612087805077141891 232339949418131707615712837)
            ·
              refine ⟨43563740515899695177946157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232339949418131707615712837 43563740515899695177946157)
              ·
                refine ⟨16336402693462385691729809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43563740515899695177946157 16336402693462385691729809)
                ·
                  refine ⟨12252302020096789268797357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16336402693462385691729809 12252302020096789268797357)
                  ·
                    refine ⟨4594613257536295975799009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12252302020096789268797357 4594613257536295975799009)
                    ·
                      refine ⟨3445959943152221981849257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594613257536295975799009 3445959943152221981849257)
                      ·
                        rfl

theorem cell23_6710983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_6710983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6710983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6710983 prefixEnd_6710983 := by exact prefixLift 6710983
  have htrace : WordTrace (prefixWord ++ tailWord_6710983) baseStart_6710983 baseEnd_6710983 := by
    simpa [prefixWord, tailWord_6710983, baseEnd_6710983] using wordTrace_append hprefix tailTrace_6710983
  have hstable : (prefixWord ++ tailWord_6710983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6710983).length < 2 ^ (prefixWord ++ tailWord_6710983).sum := by decide
  have hdescent : baseEnd_6710983 < baseStart_6710983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6710983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711007 : List Nat := [1, 1, 2, 3, 2, 2, 5, 2, 1, 1, 3]
def baseStart_6711007 : Nat := 118140960795 + 6711007 * 2 ^ 59
def prefixEnd_6711007 : Nat := 4983230072969 + 3 ^ 40 * 6711007 * 2
def baseEnd_6711007 : Nat := 3445972266687929887949147

theorem tailTrace_6711007 : CollatzResearch.WordTrace tailWord_6711007 prefixEnd_6711007 3445972266687929887949147 := by
  unfold tailWord_6711007
  simp only [CollatzResearch.WordTrace]
  refine ⟨244770533998175262591147275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163180355998783508394098183 244770533998175262591147275)
  ·
    refine ⟨367155800997262893886720913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244770533998175262591147275 367155800997262893886720913)
    ·
      refine ⟨275366850747947170415040685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367155800997262893886720913 275366850747947170415040685)
      ·
        refine ⟨103262569030480188905640257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275366850747947170415040685 103262569030480188905640257)
        ·
          refine ⟨77446926772860141679230193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103262569030480188905640257 77446926772860141679230193)
          ·
            refine ⟨58085195079645106259422645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77446926772860141679230193 58085195079645106259422645)
            ·
              refine ⟨5445487038716728711820873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58085195079645106259422645 5445487038716728711820873)
              ·
                refine ⟨4084115279037546533865655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5445487038716728711820873 4084115279037546533865655)
                ·
                  refine ⟨6126172918556319800798483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084115279037546533865655 6126172918556319800798483)
                  ·
                    refine ⟨9189259377834479701197725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6126172918556319800798483 9189259377834479701197725)
                    ·
                      refine ⟨3445972266687929887949147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9189259377834479701197725 3445972266687929887949147)
                      ·
                        rfl

theorem cell23_6711007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_6711007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711007 prefixEnd_6711007 := by exact prefixLift 6711007
  have htrace : WordTrace (prefixWord ++ tailWord_6711007) baseStart_6711007 baseEnd_6711007 := by
    simpa [prefixWord, tailWord_6711007, baseEnd_6711007] using wordTrace_append hprefix tailTrace_6711007
  have hstable : (prefixWord ++ tailWord_6711007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711007).length < 2 ^ (prefixWord ++ tailWord_6711007).sum := by decide
  have hdescent : baseEnd_6711007 < baseStart_6711007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711019 : List Nat := [1, 1, 1, 1, 2, 4, 3, 10]
def baseStart_6711019 : Nat := 118140960795 + 6711019 * 2 ^ 59
def prefixEnd_6711019 : Nat := 4983230072969 + 3 ^ 40 * 6711019 * 2
def baseEnd_6711019 : Nat := 127628830683547549666633

theorem tailTrace_6711019 : CollatzResearch.WordTrace tailWord_6711019 prefixEnd_6711019 127628830683547549666633 := by
  unfold tailWord_6711019
  simp only [CollatzResearch.WordTrace]
  refine ⟨244770971674131788640584111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163180647782754525760389407 244770971674131788640584111)
  ·
    refine ⟨367156457511197682960876167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244770971674131788640584111 367156457511197682960876167)
    ·
      refine ⟨550734686266796524441314251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367156457511197682960876167 550734686266796524441314251)
      ·
        refine ⟨826102029400194786661971377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550734686266796524441314251 826102029400194786661971377)
        ·
          refine ⟨619576522050146089996478533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826102029400194786661971377 619576522050146089996478533)
          ·
            refine ⟨116170597884402391874339725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 619576522050146089996478533 116170597884402391874339725)
            ·
              refine ⟨43563974206650896952877397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116170597884402391874339725 43563974206650896952877397)
              ·
                refine ⟨127628830683547549666633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43563974206650896952877397 127628830683547549666633)
                ·
                  rfl

theorem cell23_6711019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 10].length) (baseStart_6711019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711019 prefixEnd_6711019 := by exact prefixLift 6711019
  have htrace : WordTrace (prefixWord ++ tailWord_6711019) baseStart_6711019 baseEnd_6711019 := by
    simpa [prefixWord, tailWord_6711019, baseEnd_6711019] using wordTrace_append hprefix tailTrace_6711019
  have hstable : (prefixWord ++ tailWord_6711019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711019).length < 2 ^ (prefixWord ++ tailWord_6711019).sum := by decide
  have hdescent : baseEnd_6711019 < baseStart_6711019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711023 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 2, 4]
def baseStart_6711023 : Nat := 118140960795 + 6711023 * 2 ^ 59
def prefixEnd_6711023 : Nat := 4983230072969 + 3 ^ 40 * 6711023 * 2
def baseEnd_6711023 : Nat := 1148660160792800608449691

theorem tailTrace_6711023 : CollatzResearch.WordTrace tailWord_6711023 prefixEnd_6711023 1148660160792800608449691 := by
  unfold tailWord_6711023
  simp only [CollatzResearch.WordTrace]
  refine ⟨244771117566117297323729723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163180745044078198215819815 244771117566117297323729723)
  ·
    refine ⟨367156676349175945985594585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244771117566117297323729723 367156676349175945985594585)
    ·
      refine ⟨275367507261881959489195939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367156676349175945985594585 275367507261881959489195939)
      ·
        refine ⟨413051260892822939233793909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275367507261881959489195939 413051260892822939233793909)
        ·
          refine ⟨38723555708702150553168179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 413051260892822939233793909 38723555708702150553168179)
          ·
            refine ⟨58085333563053225829752269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38723555708702150553168179 58085333563053225829752269)
            ·
              refine ⟨21782000086144959686157101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58085333563053225829752269 21782000086144959686157101)
              ·
                refine ⟨8168250032304359882308913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21782000086144959686157101 8168250032304359882308913)
                ·
                  refine ⟨6126187524228269911731685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8168250032304359882308913 6126187524228269911731685)
                  ·
                    refine ⟨1148660160792800608449691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6126187524228269911731685 1148660160792800608449691)
                    ·
                      rfl

theorem cell23_6711023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 4].length) (baseStart_6711023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711023 prefixEnd_6711023 := by exact prefixLift 6711023
  have htrace : WordTrace (prefixWord ++ tailWord_6711023) baseStart_6711023 baseEnd_6711023 := by
    simpa [prefixWord, tailWord_6711023, baseEnd_6711023] using wordTrace_append hprefix tailTrace_6711023
  have hstable : (prefixWord ++ tailWord_6711023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711023).length < 2 ^ (prefixWord ++ tailWord_6711023).sum := by decide
  have hdescent : baseEnd_6711023 < baseStart_6711023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711026 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_6711026 : Nat := 118140960795 + 6711026 * 2 ^ 59
def prefixEnd_6711026 : Nat := 4983230072969 + 3 ^ 40 * 6711026 * 2
def baseEnd_6711026 : Nat := 3445982022820365313611559

theorem tailTrace_6711026 : CollatzResearch.WordTrace tailWord_6711026 prefixEnd_6711026 3445982022820365313611559 := by
  unfold tailWord_6711026
  simp only [CollatzResearch.WordTrace]
  refine ⟨61192806746276607209022233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163180817990070952557392621 61192806746276607209022233)
  ·
    refine ⟨45894605059707455406766675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61192806746276607209022233 45894605059707455406766675)
    ·
      refine ⟨68841907589561183110150013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45894605059707455406766675 68841907589561183110150013)
      ·
        refine ⟨25815715346085443666306255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68841907589561183110150013 25815715346085443666306255)
        ·
          refine ⟨38723573019128165499459383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25815715346085443666306255 38723573019128165499459383)
          ·
            refine ⟨58085359528692248249189075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38723573019128165499459383 58085359528692248249189075)
            ·
              refine ⟨87128039293038372373783613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58085359528692248249189075 87128039293038372373783613)
              ·
                refine ⟨32673014734889389640168855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87128039293038372373783613 32673014734889389640168855)
                ·
                  refine ⟨49009522102334084460253283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32673014734889389640168855 49009522102334084460253283)
                  ·
                    refine ⟨73514283153501126690379925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49009522102334084460253283 73514283153501126690379925)
                    ·
                      refine ⟨3445982022820365313611559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73514283153501126690379925 3445982022820365313611559)
                      ·
                        rfl

theorem cell23_6711026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_6711026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711026 prefixEnd_6711026 := by exact prefixLift 6711026
  have htrace : WordTrace (prefixWord ++ tailWord_6711026) baseStart_6711026 baseEnd_6711026 := by
    simpa [prefixWord, tailWord_6711026, baseEnd_6711026] using wordTrace_append hprefix tailTrace_6711026
  have hstable : (prefixWord ++ tailWord_6711026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711026).length < 2 ^ (prefixWord ++ tailWord_6711026).sum := by decide
  have hdescent : baseEnd_6711026 < baseStart_6711026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711030 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_6711030 : Nat := 118140960795 + 6711030 * 2 ^ 59
def prefixEnd_6711030 : Nat := 4983230072969 + 3 ^ 40 * 6711030 * 2
def baseEnd_6711030 : Nat := 3445984076742983297961541

theorem tailTrace_6711030 : CollatzResearch.WordTrace tailWord_6711030 prefixEnd_6711030 3445984076742983297961541 := by
  unfold tailWord_6711030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15298210804818246094952159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163180915251394625012823029 15298210804818246094952159)
  ·
    refine ⟨22947316207227369142428239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15298210804818246094952159 22947316207227369142428239)
    ·
      refine ⟨34420974310841053713642359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22947316207227369142428239 34420974310841053713642359)
      ·
        refine ⟨51631461466261580570463539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34420974310841053713642359 51631461466261580570463539)
        ·
          refine ⟨77447192199392370855695309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51631461466261580570463539 77447192199392370855695309)
          ·
            refine ⟨29042697074772139070885741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77447192199392370855695309 29042697074772139070885741)
            ·
              refine ⟨10891011403039552151582153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29042697074772139070885741 10891011403039552151582153)
              ·
                refine ⟨8168258552279664113686615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10891011403039552151582153 8168258552279664113686615)
                ·
                  refine ⟨12252387828419496170529923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8168258552279664113686615 12252387828419496170529923)
                  ·
                    refine ⟨18378581742629244255794885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12252387828419496170529923 18378581742629244255794885)
                    ·
                      refine ⟨3445984076742983297961541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18378581742629244255794885 3445984076742983297961541)
                      ·
                        rfl

theorem cell23_6711030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_6711030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711030 prefixEnd_6711030 := by exact prefixLift 6711030
  have htrace : WordTrace (prefixWord ++ tailWord_6711030) baseStart_6711030 baseEnd_6711030 := by
    simpa [prefixWord, tailWord_6711030, baseEnd_6711030] using wordTrace_append hprefix tailTrace_6711030
  have hstable : (prefixWord ++ tailWord_6711030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711030).length < 2 ^ (prefixWord ++ tailWord_6711030).sum := by decide
  have hdescent : baseEnd_6711030 < baseStart_6711030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711047 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6711047 : Nat := 118140960795 + 6711047 * 2 ^ 59
def prefixEnd_6711047 : Nat := 4983230072969 + 3 ^ 40 * 6711047 * 2
def baseEnd_6711047 : Nat := 3445992805914109731448963

theorem tailTrace_6711047 : CollatzResearch.WordTrace tailWord_6711047 prefixEnd_6711047 3445992805914109731448963 := by
  unfold tailWord_6711047
  simp only [CollatzResearch.WordTrace]
  refine ⟨244771992918030349422603395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163181328612020232948402263 244771992918030349422603395)
  ·
    refine ⟨367157989377045524133905093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244771992918030349422603395 367157989377045524133905093)
    ·
      refine ⟨68842123008196035775107205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367157989377045524133905093 68842123008196035775107205)
      ·
        refine ⟨12907898064036756707832601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68842123008196035775107205 12907898064036756707832601)
        ·
          refine ⟨9680923548027567530874451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12907898064036756707832601 9680923548027567530874451)
          ·
            refine ⟨14521385322041351296311677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9680923548027567530874451 14521385322041351296311677)
            ·
              refine ⟨5445519495765506736116879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14521385322041351296311677 5445519495765506736116879)
              ·
                refine ⟨8168279243648260104175319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445519495765506736116879 8168279243648260104175319)
                ·
                  refine ⟨12252418865472390156262979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8168279243648260104175319 12252418865472390156262979)
                  ·
                    refine ⟨18378628298208585234394469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12252418865472390156262979 18378628298208585234394469)
                    ·
                      refine ⟨3445992805914109731448963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18378628298208585234394469 3445992805914109731448963)
                      ·
                        rfl

theorem cell23_6711047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6711047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711047 prefixEnd_6711047 := by exact prefixLift 6711047
  have htrace : WordTrace (prefixWord ++ tailWord_6711047) baseStart_6711047 baseEnd_6711047 := by
    simpa [prefixWord, tailWord_6711047, baseEnd_6711047] using wordTrace_append hprefix tailTrace_6711047
  have hstable : (prefixWord ++ tailWord_6711047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711047).length < 2 ^ (prefixWord ++ tailWord_6711047).sum := by decide
  have hdescent : baseEnd_6711047 < baseStart_6711047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711064 : List Nat := [2, 1, 2, 3, 1, 1, 6, 2, 1, 2, 2]
def baseStart_6711064 : Nat := 118140960795 + 6711064 * 2 ^ 59
def prefixEnd_6711064 : Nat := 4983230072969 + 3 ^ 40 * 6711064 * 2
def baseEnd_6711064 : Nat := 3446001535085236164936385

theorem tailTrace_6711064 : CollatzResearch.WordTrace tailWord_6711064 prefixEnd_6711064 3446001535085236164936385 := by
  unfold tailWord_6711064
  simp only [CollatzResearch.WordTrace]
  refine ⟨122386306479484380662986123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163181741972645840883981497 122386306479484380662986123)
  ·
    refine ⟨183579459719226570994479185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122386306479484380662986123 183579459719226570994479185)
    ·
      refine ⟨137684594789419928245859389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183579459719226570994479185 137684594789419928245859389)
      ·
        refine ⟨51631723046032473092197271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137684594789419928245859389 51631723046032473092197271)
        ·
          refine ⟨77447584569048709638295907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51631723046032473092197271 77447584569048709638295907)
          ·
            refine ⟨116171376853573064457443861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77447584569048709638295907 116171376853573064457443861)
            ·
              refine ⟨5445533290011237396442681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116171376853573064457443861 5445533290011237396442681)
              ·
                refine ⟨4084149967508428047332011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5445533290011237396442681 4084149967508428047332011)
                ·
                  refine ⟨6126224951262642070998017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084149967508428047332011 6126224951262642070998017)
                  ·
                    refine ⟨4594668713446981553248513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6126224951262642070998017 4594668713446981553248513)
                    ·
                      refine ⟨3446001535085236164936385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594668713446981553248513 3446001535085236164936385)
                      ·
                        rfl

theorem cell23_6711064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_6711064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711064 prefixEnd_6711064 := by exact prefixLift 6711064
  have htrace : WordTrace (prefixWord ++ tailWord_6711064) baseStart_6711064 baseEnd_6711064 := by
    simpa [prefixWord, tailWord_6711064, baseEnd_6711064] using wordTrace_append hprefix tailTrace_6711064
  have hstable : (prefixWord ++ tailWord_6711064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711064).length < 2 ^ (prefixWord ++ tailWord_6711064).sum := by decide
  have hdescent : baseEnd_6711064 < baseStart_6711064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711066 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_6711066 : Nat := 118140960795 + 6711066 * 2 ^ 59
def prefixEnd_6711066 : Nat := 4983230072969 + 3 ^ 40 * 6711066 * 2
def baseEnd_6711066 : Nat := 1148667520682181719037125

theorem tailTrace_6711066 : CollatzResearch.WordTrace tailWord_6711066 prefixEnd_6711066 1148667520682181719037125 := by
  unfold tailWord_6711066
  simp only [CollatzResearch.WordTrace]
  refine ⟨61193171476240378916886263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163181790603307677111696701 61193171476240378916886263)
  ·
    refine ⟨91789757214360568375329395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61193171476240378916886263 91789757214360568375329395)
    ·
      refine ⟨137684635821540852562994093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91789757214360568375329395 137684635821540852562994093)
      ·
        refine ⟨51631738433077819711122785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137684635821540852562994093 51631738433077819711122785)
        ·
          refine ⟨38723803824808364783342089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51631738433077819711122785 38723803824808364783342089)
          ·
            refine ⟨29042852868606273587506567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38723803824808364783342089 29042852868606273587506567)
            ·
              refine ⟨43564279302909410381259851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29042852868606273587506567 43564279302909410381259851)
              ·
                refine ⟨65346418954364115571889777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43564279302909410381259851 65346418954364115571889777)
                ·
                  refine ⟨49009814215773086678917333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65346418954364115571889777 49009814215773086678917333)
                  ·
                    refine ⟨1148667520682181719037125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49009814215773086678917333 1148667520682181719037125)
                    ·
                      rfl

theorem cell23_6711066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_6711066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711066 prefixEnd_6711066 := by exact prefixLift 6711066
  have htrace : WordTrace (prefixWord ++ tailWord_6711066) baseStart_6711066 baseEnd_6711066 := by
    simpa [prefixWord, tailWord_6711066, baseEnd_6711066] using wordTrace_append hprefix tailTrace_6711066
  have hstable : (prefixWord ++ tailWord_6711066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711066).length < 2 ^ (prefixWord ++ tailWord_6711066).sum := by decide
  have hdescent : baseEnd_6711066 < baseStart_6711066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711080 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_6711080 : Nat := 118140960795 + 6711080 * 2 ^ 59
def prefixEnd_6711080 : Nat := 4983230072969 + 3 ^ 40 * 6711080 * 2
def baseEnd_6711080 : Nat := 3446009750775708102336311

theorem tailTrace_6711080 : CollatzResearch.WordTrace tailWord_6711080 prefixEnd_6711080 3446009750775708102336311 := by
  unfold tailWord_6711080
  simp only [CollatzResearch.WordTrace]
  refine ⟨122386598263455398029277347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163182131017940530705703129 122386598263455398029277347)
  ·
    refine ⟨183579897395183097043916021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122386598263455398029277347 183579897395183097043916021)
    ·
      refine ⟨17210615380798415347867127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183579897395183097043916021 17210615380798415347867127)
      ·
        refine ⟨25815923071197623021800691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17210615380798415347867127 25815923071197623021800691)
        ·
          refine ⟨38723884606796434532701037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25815923071197623021800691 38723884606796434532701037)
          ·
            refine ⟨14521456727548662949762889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38723884606796434532701037 14521456727548662949762889)
            ·
              refine ⟨10891092545661497212322167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14521456727548662949762889 10891092545661497212322167)
              ·
                refine ⟨16336638818492245818483251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10891092545661497212322167 16336638818492245818483251)
                ·
                  refine ⟨24504958227738368727724877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16336638818492245818483251 24504958227738368727724877)
                  ·
                    refine ⟨9189359335401888272896829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24504958227738368727724877 9189359335401888272896829)
                    ·
                      refine ⟨3446009750775708102336311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9189359335401888272896829 3446009750775708102336311)
                      ·
                        rfl

theorem cell23_6711080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_6711080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711080 prefixEnd_6711080 := by exact prefixLift 6711080
  have htrace : WordTrace (prefixWord ++ tailWord_6711080) baseStart_6711080 baseEnd_6711080 := by
    simpa [prefixWord, tailWord_6711080, baseEnd_6711080] using wordTrace_append hprefix tailTrace_6711080
  have hstable : (prefixWord ++ tailWord_6711080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711080).length < 2 ^ (prefixWord ++ tailWord_6711080).sum := by decide
  have hdescent : baseEnd_6711080 < baseStart_6711080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711090 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_6711090 : Nat := 118140960795 + 6711090 * 2 ^ 59
def prefixEnd_6711090 : Nat := 4983230072969 + 3 ^ 40 * 6711090 * 2
def baseEnd_6711090 : Nat := 3446014885582253063211265

theorem tailTrace_6711090 : CollatzResearch.WordTrace tailWord_6711090 prefixEnd_6711090 3446014885582253063211265 := by
  unfold tailWord_6711090
  simp only [CollatzResearch.WordTrace]
  refine ⟨61193390314218641941604681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163182374171249711844279149 61193390314218641941604681)
  ·
    refine ⟨45895042735663981456203511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61193390314218641941604681 45895042735663981456203511)
    ·
      refine ⟨68842564103495972184305267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45895042735663981456203511 68842564103495972184305267)
      ·
        refine ⟨103263846155243958276457901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68842564103495972184305267 103263846155243958276457901)
        ·
          refine ⟨38723942308216484353671713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103263846155243958276457901 38723942308216484353671713)
          ·
            refine ⟨29042956731162363265253785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38723942308216484353671713 29042956731162363265253785)
            ·
              refine ⟨21782217548371772448940339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29042956731162363265253785 21782217548371772448940339)
              ·
                refine ⟨32673326322557658673410509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21782217548371772448940339 32673326322557658673410509)
                ·
                  refine ⟨12252497370959122002528941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32673326322557658673410509 12252497370959122002528941)
                  ·
                    refine ⟨4594686514109670750948353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12252497370959122002528941 4594686514109670750948353)
                    ·
                      refine ⟨3446014885582253063211265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594686514109670750948353 3446014885582253063211265)
                      ·
                        rfl

theorem cell23_6711090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_6711090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711090 prefixEnd_6711090 := by exact prefixLift 6711090
  have htrace : WordTrace (prefixWord ++ tailWord_6711090) baseStart_6711090 baseEnd_6711090 := by
    simpa [prefixWord, tailWord_6711090, baseEnd_6711090] using wordTrace_append hprefix tailTrace_6711090
  have hstable : (prefixWord ++ tailWord_6711090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711090).length < 2 ^ (prefixWord ++ tailWord_6711090).sum := by decide
  have hdescent : baseEnd_6711090 < baseStart_6711090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711107 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 1, 3, 2]
def baseStart_6711107 : Nat := 118140960795 + 6711107 * 2 ^ 59
def prefixEnd_6711107 : Nat := 4983230072969 + 3 ^ 40 * 6711107 * 2
def baseEnd_6711107 : Nat := 3446023614753379496698687

theorem tailTrace_6711107 : CollatzResearch.WordTrace tailWord_6711107 prefixEnd_6711107 3446023614753379496698687 := by
  unfold tailWord_6711107
  simp only [CollatzResearch.WordTrace]
  refine ⟨244774181297812979669787575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163182787531875319779858383 244774181297812979669787575)
  ·
    refine ⟨367161271946719469504681363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244774181297812979669787575 367161271946719469504681363)
    ·
      refine ⟨550741907920079204257022045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367161271946719469504681363 550741907920079204257022045)
      ·
        refine ⟨206528215470029701596383267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550741907920079204257022045 206528215470029701596383267)
        ·
          refine ⟨309792323205044552394574901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206528215470029701596383267 309792323205044552394574901)
          ·
            refine ⟨29043030300472926786991397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 309792323205044552394574901 29043030300472926786991397)
            ·
              refine ⟨5445568181338673772560887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29043030300472926786991397 5445568181338673772560887)
              ·
                refine ⟨8168352272008010658841331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445568181338673772560887 8168352272008010658841331)
                ·
                  refine ⟨12252528408012015988261997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8168352272008010658841331 12252528408012015988261997)
                  ·
                    refine ⟨4594698153004505995598249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12252528408012015988261997 4594698153004505995598249)
                    ·
                      refine ⟨3446023614753379496698687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594698153004505995598249 3446023614753379496698687)
                      ·
                        rfl

theorem cell23_6711107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_6711107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711107 prefixEnd_6711107 := by exact prefixLift 6711107
  have htrace : WordTrace (prefixWord ++ tailWord_6711107) baseStart_6711107 baseEnd_6711107 := by
    simpa [prefixWord, tailWord_6711107, baseEnd_6711107] using wordTrace_append hprefix tailTrace_6711107
  have hstable : (prefixWord ++ tailWord_6711107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711107).length < 2 ^ (prefixWord ++ tailWord_6711107).sum := by decide
  have hdescent : baseEnd_6711107 < baseStart_6711107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711163 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 1, 7, 2]
def baseStart_6711163 : Nat := 118140960795 + 6711163 * 2 ^ 59
def prefixEnd_6711163 : Nat := 4983230072969 + 3 ^ 40 * 6711163 * 2
def baseEnd_6711163 : Nat := 3446052369670031277598429

theorem tailTrace_6711163 : CollatzResearch.WordTrace tailWord_6711163 prefixEnd_6711163 3446052369670031277598429 := by
  unfold tailWord_6711163
  simp only [CollatzResearch.WordTrace]
  refine ⟨244776223785610101233826143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163184149190406734155884095 244776223785610101233826143)
  ·
    refine ⟨367164335678415151850739215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244776223785610101233826143 367164335678415151850739215)
    ·
      refine ⟨550746503517622727776108823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367164335678415151850739215 550746503517622727776108823)
      ·
        refine ⟨826119755276434091664163235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550746503517622727776108823 826119755276434091664163235)
        ·
          refine ⟨1239179632914651137496244853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826119755276434091664163235 1239179632914651137496244853)
          ·
            refine ⟨116173090585748544140272955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1239179632914651137496244853 116173090585748544140272955)
            ·
              refine ⟨174259635878622816210409433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116173090585748544140272955 174259635878622816210409433)
              ·
                refine ⟨130694726908967112157807075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174259635878622816210409433 130694726908967112157807075)
                ·
                  refine ⟨196042090363450668236710613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130694726908967112157807075 196042090363450668236710613)
                  ·
                    refine ⟨4594736492893375036797905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 196042090363450668236710613 4594736492893375036797905)
                    ·
                      refine ⟨3446052369670031277598429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594736492893375036797905 3446052369670031277598429)
                      ·
                        rfl

theorem cell23_6711163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 7, 2].length) (baseStart_6711163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711163 prefixEnd_6711163 := by exact prefixLift 6711163
  have htrace : WordTrace (prefixWord ++ tailWord_6711163) baseStart_6711163 baseEnd_6711163 := by
    simpa [prefixWord, tailWord_6711163, baseEnd_6711163] using wordTrace_append hprefix tailTrace_6711163
  have hstable : (prefixWord ++ tailWord_6711163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711163).length < 2 ^ (prefixWord ++ tailWord_6711163).sum := by decide
  have hdescent : baseEnd_6711163 < baseStart_6711163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711173 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_6711173 : Nat := 118140960795 + 6711173 * 2 ^ 59
def prefixEnd_6711173 : Nat := 4983230072969 + 3 ^ 40 * 6711173 * 2
def baseEnd_6711173 : Nat := 1148685834825525412824461

theorem tailTrace_6711173 : CollatzResearch.WordTrace tailWord_6711173 prefixEnd_6711173 1148685834825525412824461 := by
  unfold tailWord_6711173
  simp only [CollatzResearch.WordTrace]
  refine ⟨244776588515573872941690173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163184392343715915294460115 244776588515573872941690173)
  ·
    refine ⟨91791220693340202353133815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244776588515573872941690173 91791220693340202353133815)
    ·
      refine ⟨137686831040010303529700723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91791220693340202353133815 137686831040010303529700723)
      ·
        refine ⟨206530246560015455294551085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137686831040010303529700723 206530246560015455294551085)
        ·
          refine ⟨77448842460005795735456657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206530246560015455294551085 77448842460005795735456657)
          ·
            refine ⟨58086631845004346801592493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77448842460005795735456657 58086631845004346801592493)
            ·
              refine ⟨21782486941876630050597185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58086631845004346801592493 21782486941876630050597185)
              ·
                refine ⟨16336865206407472537947889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21782486941876630050597185 16336865206407472537947889)
                ·
                  refine ⟨12252648904805604403460917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16336865206407472537947889 12252648904805604403460917)
                  ·
                    refine ⟨1148685834825525412824461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12252648904805604403460917 1148685834825525412824461)
                    ·
                      rfl

theorem cell23_6711173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_6711173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711173 prefixEnd_6711173 := by exact prefixLift 6711173
  have htrace : WordTrace (prefixWord ++ tailWord_6711173) baseStart_6711173 baseEnd_6711173 := by
    simpa [prefixWord, tailWord_6711173, baseEnd_6711173] using wordTrace_append hprefix tailTrace_6711173
  have hstable : (prefixWord ++ tailWord_6711173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711173).length < 2 ^ (prefixWord ++ tailWord_6711173).sum := by decide
  have hdescent : baseEnd_6711173 < baseStart_6711173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711203 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 5, 4]
def baseStart_6711203 : Nat := 118140960795 + 6711203 * 2 ^ 59
def prefixEnd_6711203 : Nat := 4983230072969 + 3 ^ 40 * 6711203 * 2
def baseEnd_6711203 : Nat := 1148690969632070373699415

theorem tailTrace_6711203 : CollatzResearch.WordTrace tailWord_6711203 prefixEnd_6711203 1148690969632070373699415 := by
  unfold tailWord_6711203
  simp only [CollatzResearch.WordTrace]
  refine ⟨244777682705465188065282263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163185121803643458710188175 244777682705465188065282263)
  ·
    refine ⟨367166524058197782097923395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244777682705465188065282263 367166524058197782097923395)
    ·
      refine ⟨550749786087296673146885093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367166524058197782097923395 550749786087296673146885093)
      ·
        refine ⟨103265584891368126215040955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 550749786087296673146885093 103265584891368126215040955)
        ·
          refine ⟨154898377337052189322561433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103265584891368126215040955 154898377337052189322561433)
          ·
            refine ⟨116173783002789141991921075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154898377337052189322561433 116173783002789141991921075)
            ·
              refine ⟨174260674504183712987881613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116173783002789141991921075 174260674504183712987881613)
              ·
                refine ⟨65347752939068892370455605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174260674504183712987881613 65347752939068892370455605)
                ·
                  refine ⟨6126351838037708659730213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65347752939068892370455605 6126351838037708659730213)
                  ·
                    refine ⟨1148690969632070373699415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6126351838037708659730213 1148690969632070373699415)
                    ·
                      rfl

theorem cell23_6711203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 4].length) (baseStart_6711203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711203 prefixEnd_6711203 := by exact prefixLift 6711203
  have htrace : WordTrace (prefixWord ++ tailWord_6711203) baseStart_6711203 baseEnd_6711203 := by
    simpa [prefixWord, tailWord_6711203, baseEnd_6711203] using wordTrace_append hprefix tailTrace_6711203
  have hstable : (prefixWord ++ tailWord_6711203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711203).length < 2 ^ (prefixWord ++ tailWord_6711203).sum := by decide
  have hdescent : baseEnd_6711203 < baseStart_6711203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711254 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_6711254 : Nat := 118140960795 + 6711254 * 2 ^ 59
def prefixEnd_6711254 : Nat := 4983230072969 + 3 ^ 40 * 6711254 * 2
def baseEnd_6711254 : Nat := 1148699698803196807186837

theorem tailTrace_6711254 : CollatzResearch.WordTrace tailWord_6711254 prefixEnd_6711254 1148699698803196807186837 := by
  unfold tailWord_6711254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15298721426767526485961801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163186361885520282516925877 15298721426767526485961801)
  ·
    refine ⟨11474041070075644864471351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15298721426767526485961801 11474041070075644864471351)
    ·
      refine ⟨17211061605113467296707027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11474041070075644864471351 17211061605113467296707027)
      ·
        refine ⟨25816592407670200945060541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17211061605113467296707027 25816592407670200945060541)
        ·
          refine ⟨9681222152876325354397703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25816592407670200945060541 9681222152876325354397703)
          ·
            refine ⟨14521833229314488031596555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9681222152876325354397703 14521833229314488031596555)
            ·
              refine ⟨21782749843971732047394833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14521833229314488031596555 21782749843971732047394833)
              ·
                refine ⟨16337062382978799035546125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21782749843971732047394833 16337062382978799035546125)
                ·
                  refine ⟨6126398393617049638329797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16337062382978799035546125 6126398393617049638329797)
                  ·
                    refine ⟨1148699698803196807186837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6126398393617049638329797 1148699698803196807186837)
                    ·
                      rfl

theorem cell23_6711254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_6711254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711254 prefixEnd_6711254 := by exact prefixLift 6711254
  have htrace : WordTrace (prefixWord ++ tailWord_6711254) baseStart_6711254 baseEnd_6711254 := by
    simpa [prefixWord, tailWord_6711254, baseEnd_6711254] using wordTrace_append hprefix tailTrace_6711254
  have hstable : (prefixWord ++ tailWord_6711254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711254).length < 2 ^ (prefixWord ++ tailWord_6711254).sum := by decide
  have hdescent : baseEnd_6711254 < baseStart_6711254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711293 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_6711293 : Nat := 118140960795 + 6711293 * 2 ^ 59
def prefixEnd_6711293 : Nat := 4983230072969 + 3 ^ 40 * 6711293 * 2
def baseEnd_6711293 : Nat := 1148706374051705256324277

theorem tailTrace_6711293 : CollatzResearch.WordTrace tailWord_6711293 prefixEnd_6711293 1148706374051705256324277 := by
  unfold tailWord_6711293
  simp only [CollatzResearch.WordTrace]
  refine ⟨244780965275139133436058533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163187310183426088957372355 244780965275139133436058533)
  ·
    refine ⟨45896430989088587519260975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244780965275139133436058533 45896430989088587519260975)
    ·
      refine ⟨68844646483632881278891463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45896430989088587519260975 68844646483632881278891463)
      ·
        refine ⟨103266969725449321918337195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68844646483632881278891463 103266969725449321918337195)
        ·
          refine ⟨154900454588173982877505793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103266969725449321918337195 154900454588173982877505793)
          ·
            refine ⟨116175340941130487158129345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154900454588173982877505793 116175340941130487158129345)
            ·
              refine ⟨87131505705847865368597009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116175340941130487158129345 87131505705847865368597009)
              ·
                refine ⟨65348629279385899026447757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87131505705847865368597009 65348629279385899026447757)
                ·
                  refine ⟨24505735979769712134917909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65348629279385899026447757 24505735979769712134917909)
                  ·
                    refine ⟨1148706374051705256324277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24505735979769712134917909 1148706374051705256324277)
                    ·
                      rfl

theorem cell23_6711293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_6711293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711293 prefixEnd_6711293 := by exact prefixLift 6711293
  have htrace : WordTrace (prefixWord ++ tailWord_6711293) baseStart_6711293 baseEnd_6711293 := by
    simpa [prefixWord, tailWord_6711293, baseEnd_6711293] using wordTrace_append hprefix tailTrace_6711293
  have hstable : (prefixWord ++ tailWord_6711293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711293).length < 2 ^ (prefixWord ++ tailWord_6711293).sum := by decide
  have hdescent : baseEnd_6711293 < baseStart_6711293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711294 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6711294 : Nat := 118140960795 + 6711294 * 2 ^ 59
def prefixEnd_6711294 : Nat := 4983230072969 + 3 ^ 40 * 6711294 * 2
def baseEnd_6711294 : Nat := 3446119635635770265060327

theorem tailTrace_6711294 : CollatzResearch.WordTrace tailWord_6711294 prefixEnd_6711294 3446119635635770265060327 := by
  unfold tailWord_6711294
  simp only [CollatzResearch.WordTrace]
  refine ⟨30597625218516938825855617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163187334498757007071229957 30597625218516938825855617)
  ·
    refine ⟨22948218913887704119391713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30597625218516938825855617 22948218913887704119391713)
    ·
      refine ⟨17211164185415778089543785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22948218913887704119391713 17211164185415778089543785)
      ·
        refine ⟨12908373139061833567157839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17211164185415778089543785 12908373139061833567157839)
        ·
          refine ⟨19362559708592750350736759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12908373139061833567157839 19362559708592750350736759)
          ·
            refine ⟨29043839562889125526105139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19362559708592750350736759 29043839562889125526105139)
            ·
              refine ⟨43565759344333688289157709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29043839562889125526105139 43565759344333688289157709)
              ·
                refine ⟨16337159754125133108434141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43565759344333688289157709 16337159754125133108434141)
                ·
                  refine ⟨6126434907796924915662803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16337159754125133108434141 6126434907796924915662803)
                  ·
                    refine ⟨9189652361695387373494205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6126434907796924915662803 9189652361695387373494205)
                    ·
                      refine ⟨3446119635635770265060327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9189652361695387373494205 3446119635635770265060327)
                      ·
                        rfl

theorem cell23_6711294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6711294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711294 prefixEnd_6711294 := by exact prefixLift 6711294
  have htrace : WordTrace (prefixWord ++ tailWord_6711294) baseStart_6711294 baseEnd_6711294 := by
    simpa [prefixWord, tailWord_6711294, baseEnd_6711294] using wordTrace_append hprefix tailTrace_6711294
  have hstable : (prefixWord ++ tailWord_6711294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711294).length < 2 ^ (prefixWord ++ tailWord_6711294).sum := by decide
  have hdescent : baseEnd_6711294 < baseStart_6711294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711330 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_6711330 : Nat := 118140960795 + 6711330 * 2 ^ 59
def prefixEnd_6711330 : Nat := 4983230072969 + 3 ^ 40 * 6711330 * 2
def baseEnd_6711330 : Nat := 3446138120939332124210161

theorem tailTrace_6711330 : CollatzResearch.WordTrace tailWord_6711330 prefixEnd_6711330 3446138120939332124210161 := by
  unfold tailWord_6711330
  simp only [CollatzResearch.WordTrace]
  refine ⟨61195578694001272188788861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163188209850670059170103629 61195578694001272188788861)
  ·
    refine ⟨22948342010250477070795823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61195578694001272188788861 22948342010250477070795823)
    ·
      refine ⟨34422513015375715606193735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22948342010250477070795823 34422513015375715606193735)
      ·
        refine ⟨51633769523063573409290603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34422513015375715606193735 51633769523063573409290603)
        ·
          refine ⟨77450654284595360113935905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51633769523063573409290603 77450654284595360113935905)
          ·
            refine ⟨58087990713446520085451929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77450654284595360113935905 58087990713446520085451929)
            ·
              refine ⟨43565993035084890064088947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58087990713446520085451929 43565993035084890064088947)
              ·
                refine ⟨65348989552627335096133421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43565993035084890064088947 65348989552627335096133421)
                ·
                  refine ⟨24505871082235250661050033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65348989552627335096133421 24505871082235250661050033)
                  ·
                    refine ⟨18379403311676437995787525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24505871082235250661050033 18379403311676437995787525)
                    ·
                      refine ⟨3446138120939332124210161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18379403311676437995787525 3446138120939332124210161)
                      ·
                        rfl

theorem cell23_6711330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_6711330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711330 prefixEnd_6711330 := by exact prefixLift 6711330
  have htrace : WordTrace (prefixWord ++ tailWord_6711330) baseStart_6711330 baseEnd_6711330 := by
    simpa [prefixWord, tailWord_6711330, baseEnd_6711330] using wordTrace_append hprefix tailTrace_6711330
  have hstable : (prefixWord ++ tailWord_6711330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711330).length < 2 ^ (prefixWord ++ tailWord_6711330).sum := by decide
  have hdescent : baseEnd_6711330 < baseStart_6711330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711361 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 2, 4]
def baseStart_6711361 : Nat := 118140960795 + 6711361 * 2 ^ 59
def prefixEnd_6711361 : Nat := 4983230072969 + 3 ^ 40 * 6711361 * 2
def baseEnd_6711361 : Nat := 1148718012946540500974173

theorem tailTrace_6711361 : CollatzResearch.WordTrace tailWord_6711361 prefixEnd_6711361 1148718012946540500974173 := by
  unfold tailWord_6711361
  simp only [CollatzResearch.WordTrace]
  refine ⟨244783445438892781049533937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163188963625928520699689291 244783445438892781049533937)
  ·
    refine ⟨183587584079169585787150453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244783445438892781049533937 183587584079169585787150453)
    ·
      refine ⟨17211336007422148667545355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183587584079169585787150453 17211336007422148667545355)
      ·
        refine ⟨25817004011133223001318033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17211336007422148667545355 25817004011133223001318033)
        ·
          refine ⟨19362753008349917250988525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25817004011133223001318033 19362753008349917250988525)
          ·
            refine ⟨7261032378131218969120697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19362753008349917250988525 7261032378131218969120697)
            ·
              refine ⟨5445774283598414226840523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7261032378131218969120697 5445774283598414226840523)
              ·
                refine ⟨8168661425397621340260785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445774283598414226840523 8168661425397621340260785)
                ·
                  refine ⟨6126496069048216005195589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8168661425397621340260785 6126496069048216005195589)
                  ·
                    refine ⟨1148718012946540500974173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6126496069048216005195589 1148718012946540500974173)
                    ·
                      rfl

theorem cell23_6711361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_6711361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711361 prefixEnd_6711361 := by exact prefixLift 6711361
  have htrace : WordTrace (prefixWord ++ tailWord_6711361) baseStart_6711361 baseEnd_6711361 := by
    simpa [prefixWord, tailWord_6711361, baseEnd_6711361] using wordTrace_append hprefix tailTrace_6711361
  have hstable : (prefixWord ++ tailWord_6711361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711361).length < 2 ^ (prefixWord ++ tailWord_6711361).sum := by decide
  have hdescent : baseEnd_6711361 < baseStart_6711361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711363 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 5]
def baseStart_6711363 : Nat := 118140960795 + 6711363 * 2 ^ 59
def prefixEnd_6711363 : Nat := 4983230072969 + 3 ^ 40 * 6711363 * 2
def baseEnd_6711363 : Nat := 3446155065800930495097509

theorem tailTrace_6711363 : CollatzResearch.WordTrace tailWord_6711363 prefixEnd_6711363 3446155065800930495097509 := by
  unfold tailWord_6711363
  simp only [CollatzResearch.WordTrace]
  refine ⟨244783518384885535391106743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163189012256590356927404495 244783518384885535391106743)
  ·
    refine ⟨367175277577328303086660115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244783518384885535391106743 367175277577328303086660115)
    ·
      refine ⟨550762916365992454629990173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367175277577328303086660115 550762916365992454629990173)
      ·
        refine ⟨206536093637247170486246315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550762916365992454629990173 206536093637247170486246315)
        ·
          refine ⟨309804140455870755729369473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206536093637247170486246315 309804140455870755729369473)
          ·
            refine ⟨232353105341903066797027105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309804140455870755729369473 232353105341903066797027105)
            ·
              refine ⟨174264829006427300097770329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232353105341903066797027105 174264829006427300097770329)
              ·
                refine ⟨130698621754820475073327747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174264829006427300097770329 130698621754820475073327747)
                ·
                  refine ⟨196047932632230712609991621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130698621754820475073327747 196047932632230712609991621)
                  ·
                    refine ⟨36758987368543258614373429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 196047932632230712609991621 36758987368543258614373429)
                    ·
                      refine ⟨3446155065800930495097509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36758987368543258614373429 3446155065800930495097509)
                      ·
                        rfl

theorem cell23_6711363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_6711363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711363 prefixEnd_6711363 := by exact prefixLift 6711363
  have htrace : WordTrace (prefixWord ++ tailWord_6711363) baseStart_6711363 baseEnd_6711363 := by
    simpa [prefixWord, tailWord_6711363, baseEnd_6711363] using wordTrace_append hprefix tailTrace_6711363
  have hstable : (prefixWord ++ tailWord_6711363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711363).length < 2 ^ (prefixWord ++ tailWord_6711363).sum := by decide
  have hdescent : baseEnd_6711363 < baseStart_6711363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711402 : List Nat := [3, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_6711402 : Nat := 118140960795 + 6711402 * 2 ^ 59
def prefixEnd_6711402 : Nat := 4983230072969 + 3 ^ 40 * 6711402 * 2
def baseEnd_6711402 : Nat := 3446175091546455842509831

theorem tailTrace_6711402 : CollatzResearch.WordTrace tailWord_6711402 prefixEnd_6711402 3446175091546455842509831 := by
  unfold tailWord_6711402
  simp only [CollatzResearch.WordTrace]
  refine ⟨61196235207936061262944115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163189960554496163367850973 61196235207936061262944115)
  ·
    refine ⟨91794352811904091894416173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61196235207936061262944115 91794352811904091894416173)
    ·
      refine ⟨34422882304464034460406065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91794352811904091894416173 34422882304464034460406065)
      ·
        refine ⟨25817161728348025845304549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34422882304464034460406065 25817161728348025845304549)
        ·
          refine ⟨4840717824065254845994603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25817161728348025845304549 4840717824065254845994603)
          ·
            refine ⟨7261076736097882268991905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4840717824065254845994603 7261076736097882268991905)
            ·
              refine ⟨5445807552073411701743929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7261076736097882268991905 5445807552073411701743929)
              ·
                refine ⟨4084355664055058776307947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5445807552073411701743929 4084355664055058776307947)
                ·
                  refine ⟨6126533496082588164461921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084355664055058776307947 6126533496082588164461921)
                  ·
                    refine ⟨4594900122061941123346441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6126533496082588164461921 4594900122061941123346441)
                    ·
                      refine ⟨3446175091546455842509831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594900122061941123346441 3446175091546455842509831)
                      ·
                        rfl

theorem cell23_6711402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_6711402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711402 prefixEnd_6711402 := by exact prefixLift 6711402
  have htrace : WordTrace (prefixWord ++ tailWord_6711402) baseStart_6711402 baseEnd_6711402 := by
    simpa [prefixWord, tailWord_6711402, baseEnd_6711402] using wordTrace_append hprefix tailTrace_6711402
  have hstable : (prefixWord ++ tailWord_6711402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711402).length < 2 ^ (prefixWord ++ tailWord_6711402).sum := by decide
  have hdescent : baseEnd_6711402 < baseStart_6711402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711420 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_6711420 : Nat := 118140960795 + 6711420 * 2 ^ 59
def prefixEnd_6711420 : Nat := 4983230072969 + 3 ^ 40 * 6711420 * 2
def baseEnd_6711420 : Nat := 3446184334198236772084747

theorem tailTrace_6711420 : CollatzResearch.WordTrace tailWord_6711420 prefixEnd_6711420 3446184334198236772084747 := by
  unfold tailWord_6711420
  simp only [CollatzResearch.WordTrace]
  refine ⟨122392798672839517062965857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163190398230452689417287809 122392798672839517062965857)
  ·
    refine ⟨91794599004629637797224393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122392798672839517062965857 91794599004629637797224393)
    ·
      refine ⟨68845949253472228347918295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91794599004629637797224393 68845949253472228347918295)
      ·
        refine ⟨103268923880208342521877443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68845949253472228347918295 103268923880208342521877443)
        ·
          refine ⟨154903385820312513782816165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103268923880208342521877443 154903385820312513782816165)
          ·
            refine ⟨29044384841308596334278031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154903385820312513782816165 29044384841308596334278031)
            ·
              refine ⟨43566577261962894501417047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29044384841308596334278031 43566577261962894501417047)
              ·
                refine ⟨65349865892944341752125571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43566577261962894501417047 65349865892944341752125571)
                ·
                  refine ⟨98024798839416512628188357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65349865892944341752125571 98024798839416512628188357)
                  ·
                    refine ⟨18379649782390596117785317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98024798839416512628188357 18379649782390596117785317)
                    ·
                      refine ⟨3446184334198236772084747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18379649782390596117785317 3446184334198236772084747)
                      ·
                        rfl

theorem cell23_6711420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_6711420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711420 prefixEnd_6711420 := by exact prefixLift 6711420
  have htrace : WordTrace (prefixWord ++ tailWord_6711420) baseStart_6711420 baseEnd_6711420 := by
    simpa [prefixWord, tailWord_6711420, baseEnd_6711420] using wordTrace_append hprefix tailTrace_6711420
  have hstable : (prefixWord ++ tailWord_6711420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711420).length < 2 ^ (prefixWord ++ tailWord_6711420).sum := by decide
  have hdescent : baseEnd_6711420 < baseStart_6711420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711440 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 3]
def baseStart_6711440 : Nat := 118140960795 + 6711440 * 2 ^ 59
def prefixEnd_6711440 : Nat := 4983230072969 + 3 ^ 40 * 6711440 * 2
def baseEnd_6711440 : Nat := 3446194603811326693834655

theorem tailTrace_6711440 : CollatzResearch.WordTrace tailWord_6711440 prefixEnd_6711440 3446194603811326693834655 := by
  unfold tailWord_6711440
  simp only [CollatzResearch.WordTrace]
  refine ⟨122393163402803288770829887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163190884537071051694439849 122393163402803288770829887)
  ·
    refine ⟨183589745104204933156244831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122393163402803288770829887 183589745104204933156244831)
    ·
      refine ⟨275384617656307399734367247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183589745104204933156244831 275384617656307399734367247)
      ·
        refine ⟨413076926484461099601550871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275384617656307399734367247 413076926484461099601550871)
        ·
          refine ⟨619615389726691649402326307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413076926484461099601550871 619615389726691649402326307)
          ·
            refine ⟨929423084590037474103489461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619615389726691649402326307 929423084590037474103489461)
            ·
              refine ⟨87133414180316013197202137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 929423084590037474103489461 87133414180316013197202137)
              ·
                refine ⟨65350060635237009897901603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87133414180316013197202137 65350060635237009897901603)
                ·
                  refine ⟨98025090952855514846852405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65350060635237009897901603 98025090952855514846852405)
                  ·
                    refine ⟨9189852276830204516892413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98025090952855514846852405 9189852276830204516892413)
                    ·
                      refine ⟨3446194603811326693834655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9189852276830204516892413 3446194603811326693834655)
                      ·
                        rfl

theorem cell23_6711440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_6711440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711440 prefixEnd_6711440 := by exact prefixLift 6711440
  have htrace : WordTrace (prefixWord ++ tailWord_6711440) baseStart_6711440 baseEnd_6711440 := by
    simpa [prefixWord, tailWord_6711440, baseEnd_6711440] using wordTrace_append hprefix tailTrace_6711440
  have hstable : (prefixWord ++ tailWord_6711440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711440).length < 2 ^ (prefixWord ++ tailWord_6711440).sum := by decide
  have hdescent : baseEnd_6711440 < baseStart_6711440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711457 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_6711457 : Nat := 118140960795 + 6711457 * 2 ^ 59
def prefixEnd_6711457 : Nat := 4983230072969 + 3 ^ 40 * 6711457 * 2
def baseEnd_6711457 : Nat := 3446203332982453127322077

theorem tailTrace_6711457 : CollatzResearch.WordTrace tailWord_6711457 prefixEnd_6711457 3446203332982453127322077 := by
  unfold tailWord_6711457
  simp only [CollatzResearch.WordTrace]
  refine ⟨244786946846544989445028625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163191297897696659630019083 244786946846544989445028625)
  ·
    refine ⟨183590210134908742083771469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244786946846544989445028625 183590210134908742083771469)
    ·
      refine ⟨68846328800590778281414301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183590210134908742083771469 68846328800590778281414301)
      ·
        refine ⟨25817373300221541855530363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68846328800590778281414301 25817373300221541855530363)
        ·
          refine ⟨38726059950332312783295545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25817373300221541855530363 38726059950332312783295545)
          ·
            refine ⟨29044544962749234587471659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38726059950332312783295545 29044544962749234587471659)
            ·
              refine ⟨43566817444123851881207489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29044544962749234587471659 43566817444123851881207489)
              ·
                refine ⟨32675113083092888910905617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43566817444123851881207489 32675113083092888910905617)
                ·
                  refine ⟨24506334812319666683179213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32675113083092888910905617 24506334812319666683179213)
                  ·
                    refine ⟨9189875554619875006192205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24506334812319666683179213 9189875554619875006192205)
                    ·
                      refine ⟨3446203332982453127322077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9189875554619875006192205 3446203332982453127322077)
                      ·
                        rfl

theorem cell23_6711457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_6711457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711457 prefixEnd_6711457 := by exact prefixLift 6711457
  have htrace : WordTrace (prefixWord ++ tailWord_6711457) baseStart_6711457 baseEnd_6711457 := by
    simpa [prefixWord, tailWord_6711457, baseEnd_6711457] using wordTrace_append hprefix tailTrace_6711457
  have hstable : (prefixWord ++ tailWord_6711457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711457).length < 2 ^ (prefixWord ++ tailWord_6711457).sum := by decide
  have hdescent : baseEnd_6711457 < baseStart_6711457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711458 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_6711458 : Nat := 118140960795 + 6711458 * 2 ^ 59
def prefixEnd_6711458 : Nat := 4983230072969 + 3 ^ 40 * 6711458 * 2
def baseEnd_6711458 : Nat := 3446203846463107623409573

theorem tailTrace_6711458 : CollatzResearch.WordTrace tailWord_6711458 prefixEnd_6711458 3446203846463107623409573 := by
  unfold tailWord_6711458
  simp only [CollatzResearch.WordTrace]
  refine ⟨61196745829885341653953757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163191322213027577743876685 61196745829885341653953757)
  ·
    refine ⟨22948779686207003120232659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61196745829885341653953757 22948779686207003120232659)
    ·
      refine ⟨34423169529310504680348989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22948779686207003120232659 34423169529310504680348989)
      ·
        refine ⟨12908688573491439255130871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34423169529310504680348989 12908688573491439255130871)
        ·
          refine ⟨19363032860237158882696307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12908688573491439255130871 19363032860237158882696307)
          ·
            refine ⟨29044549290355738324044461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19363032860237158882696307 29044549290355738324044461)
            ·
              refine ⟨10891705983883401871516673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29044549290355738324044461 10891705983883401871516673)
              ·
                refine ⟨8168779487912551403637505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10891705983883401871516673 8168779487912551403637505)
                ·
                  refine ⟨6126584615934413552728129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8168779487912551403637505 6126584615934413552728129)
                  ·
                    refine ⟨4594938461950810164546097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6126584615934413552728129 4594938461950810164546097)
                    ·
                      refine ⟨3446203846463107623409573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594938461950810164546097 3446203846463107623409573)
                      ·
                        rfl

theorem cell23_6711458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_6711458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711458 prefixEnd_6711458 := by exact prefixLift 6711458
  have htrace : WordTrace (prefixWord ++ tailWord_6711458) baseStart_6711458 baseEnd_6711458 := by
    simpa [prefixWord, tailWord_6711458, baseEnd_6711458] using wordTrace_append hprefix tailTrace_6711458
  have hstable : (prefixWord ++ tailWord_6711458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711458).length < 2 ^ (prefixWord ++ tailWord_6711458).sum := by decide
  have hdescent : baseEnd_6711458 < baseStart_6711458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711480 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_6711480 : Nat := 118140960795 + 6711480 * 2 ^ 59
def prefixEnd_6711480 : Nat := 4983230072969 + 3 ^ 40 * 6711480 * 2
def baseEnd_6711480 : Nat := 3446215143037506537334471

theorem tailTrace_6711480 : CollatzResearch.WordTrace tailWord_6711480 prefixEnd_6711480 3446215143037506537334471 := by
  unfold tailWord_6711480
  simp only [CollatzResearch.WordTrace]
  refine ⟨122393892862730832186557947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163191857150307776248743929 122393892862730832186557947)
  ·
    refine ⟨183590839294096248279836921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122393892862730832186557947 183590839294096248279836921)
    ·
      refine ⟨137693129470572186209877691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183590839294096248279836921 137693129470572186209877691)
      ·
        refine ⟨206539694205858279314816537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137693129470572186209877691 206539694205858279314816537)
        ·
          refine ⟨154904770654393709486112403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206539694205858279314816537 154904770654393709486112403)
          ·
            refine ⟨232357155981590564229168605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154904770654393709486112403 232357155981590564229168605)
            ·
              refine ⟨87133933493096461585938227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232357155981590564229168605 87133933493096461585938227)
              ·
                refine ⟨130700900239644692378907341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87133933493096461585938227 130700900239644692378907341)
                ·
                  refine ⟨49012837589866759642090253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130700900239644692378907341 49012837589866759642090253)
                  ·
                    refine ⟨18379814096200034865783845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49012837589866759642090253 18379814096200034865783845)
                    ·
                      refine ⟨3446215143037506537334471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18379814096200034865783845 3446215143037506537334471)
                      ·
                        rfl

theorem cell23_6711480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_6711480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711480 prefixEnd_6711480 := by exact prefixLift 6711480
  have htrace : WordTrace (prefixWord ++ tailWord_6711480) baseStart_6711480 baseEnd_6711480 := by
    simpa [prefixWord, tailWord_6711480, baseEnd_6711480] using wordTrace_append hprefix tailTrace_6711480
  have hstable : (prefixWord ++ tailWord_6711480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711480).length < 2 ^ (prefixWord ++ tailWord_6711480).sum := by decide
  have hdescent : baseEnd_6711480 < baseStart_6711480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711497 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 4, 4, 2]
def baseStart_6711497 : Nat := 118140960795 + 6711497 * 2 ^ 59
def prefixEnd_6711497 : Nat := 4983230072969 + 3 ^ 40 * 6711497 * 2
def baseEnd_6711497 : Nat := 3446223872208632970821893

theorem tailTrace_6711497 : CollatzResearch.WordTrace tailWord_6711497 prefixEnd_6711497 3446223872208632970821893 := by
  unfold tailWord_6711497
  simp only [CollatzResearch.WordTrace]
  refine ⟨244788405766400076276484745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163192270510933384184323163 244788405766400076276484745)
  ·
    refine ⟨183591304324800057207363559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244788405766400076276484745 183591304324800057207363559)
    ·
      refine ⟨275386956487200085811045339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183591304324800057207363559 275386956487200085811045339)
      ·
        refine ⟨413080434730800128716568009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275386956487200085811045339 413080434730800128716568009)
        ·
          refine ⟨309810326048100096537426007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413080434730800128716568009 309810326048100096537426007)
          ·
            refine ⟨464715489072150144806139011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309810326048100096537426007 464715489072150144806139011)
            ·
              refine ⟨697073233608225217209208517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464715489072150144806139011 697073233608225217209208517)
              ·
                refine ⟨130701231301542228226726597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697073233608225217209208517 130701231301542228226726597)
                ·
                  refine ⟨24506480869039167792511237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130701231301542228226726597 24506480869039167792511237)
                  ·
                    refine ⟨4594965162944843961095857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24506480869039167792511237 4594965162944843961095857)
                    ·
                      refine ⟨3446223872208632970821893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4594965162944843961095857 3446223872208632970821893)
                      ·
                        rfl

theorem cell23_6711497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 4, 2].length) (baseStart_6711497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711497 prefixEnd_6711497 := by exact prefixLift 6711497
  have htrace : WordTrace (prefixWord ++ tailWord_6711497) baseStart_6711497 baseEnd_6711497 := by
    simpa [prefixWord, tailWord_6711497, baseEnd_6711497] using wordTrace_append hprefix tailTrace_6711497
  have hstable : (prefixWord ++ tailWord_6711497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711497).length < 2 ^ (prefixWord ++ tailWord_6711497).sum := by decide
  have hdescent : baseEnd_6711497 < baseStart_6711497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711520 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 8]
def baseStart_6711520 : Nat := 118140960795 + 6711520 * 2 ^ 59
def prefixEnd_6711520 : Nat := 4983230072969 + 3 ^ 40 * 6711520 * 2
def baseEnd_6711520 : Nat := 382915075807076264537143

theorem tailTrace_6711520 : CollatzResearch.WordTrace tailWord_6711520 prefixEnd_6711520 382915075807076264537143 := by
  unfold tailWord_6711520
  simp only [CollatzResearch.WordTrace]
  refine ⟨122394622322658375602286007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163192829763544500803048009 122394622322658375602286007)
  ·
    refine ⟨183591933483987563403429011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122394622322658375602286007 183591933483987563403429011)
    ·
      refine ⟨275387900225981345105143517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183591933483987563403429011 275387900225981345105143517)
      ·
        refine ⟨103270462584743004414428819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275387900225981345105143517 103270462584743004414428819)
        ·
          refine ⟨154905693877114506621643229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103270462584743004414428819 154905693877114506621643229)
          ·
            refine ⟨58089635203917939983116211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154905693877114506621643229 58089635203917939983116211)
            ·
              refine ⟨87134452805876909974674317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58089635203917939983116211 87134452805876909974674317)
              ·
                refine ⟨32675419802203841240502869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87134452805876909974674317 32675419802203841240502869)
                ·
                  refine ⟨382915075807076264537143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32675419802203841240502869 382915075807076264537143)
                  ·
                    rfl

theorem cell23_6711520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 8].length) (baseStart_6711520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711520 prefixEnd_6711520 := by exact prefixLift 6711520
  have htrace : WordTrace (prefixWord ++ tailWord_6711520) baseStart_6711520 baseEnd_6711520 := by
    simpa [prefixWord, tailWord_6711520, baseEnd_6711520] using wordTrace_append hprefix tailTrace_6711520
  have hstable : (prefixWord ++ tailWord_6711520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711520).length < 2 ^ (prefixWord ++ tailWord_6711520).sum := by decide
  have hdescent : baseEnd_6711520 < baseStart_6711520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711567 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 1, 5]
def baseStart_6711567 : Nat := 118140960795 + 6711567 * 2 ^ 59
def prefixEnd_6711567 : Nat := 4983230072969 + 3 ^ 40 * 6711567 * 2
def baseEnd_6711567 : Nat := 1148753271951482565648857

theorem tailTrace_6711567 : CollatzResearch.WordTrace tailWord_6711567 prefixEnd_6711567 1148753271951482565648857 := by
  unfold tailWord_6711567
  simp only [CollatzResearch.WordTrace]
  refine ⟨244790958876146478231532955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163193972584097652154355303 244790958876146478231532955)
  ·
    refine ⟨367186438314219717347299433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244790958876146478231532955 367186438314219717347299433)
    ·
      refine ⟨275389828735664788010474575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367186438314219717347299433 275389828735664788010474575)
      ·
        refine ⟨413084743103497182015711863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275389828735664788010474575 413084743103497182015711863)
        ·
          refine ⟨619627114655245773023567795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413084743103497182015711863 619627114655245773023567795)
          ·
            refine ⟨929440671982868659535351693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619627114655245773023567795 929440671982868659535351693)
            ·
              refine ⟨348540251993575747325756885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 929440671982868659535351693 348540251993575747325756885)
              ·
                refine ⟨8168912156099431577947427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 348540251993575747325756885 8168912156099431577947427)
                ·
                  refine ⟨12253368234149147366921141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8168912156099431577947427 12253368234149147366921141)
                  ·
                    refine ⟨1148753271951482565648857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12253368234149147366921141 1148753271951482565648857)
                    ·
                      rfl

theorem cell23_6711567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 5].length) (baseStart_6711567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711567 prefixEnd_6711567 := by exact prefixLift 6711567
  have htrace : WordTrace (prefixWord ++ tailWord_6711567) baseStart_6711567 baseEnd_6711567 := by
    simpa [prefixWord, tailWord_6711567, baseEnd_6711567] using wordTrace_append hprefix tailTrace_6711567
  have hstable : (prefixWord ++ tailWord_6711567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711567).length < 2 ^ (prefixWord ++ tailWord_6711567).sum := by decide
  have hdescent : baseEnd_6711567 < baseStart_6711567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711587 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 4]
def baseStart_6711587 : Nat := 118140960795 + 6711587 * 2 ^ 59
def prefixEnd_6711587 : Nat := 4983230072969 + 3 ^ 40 * 6711587 * 2
def baseEnd_6711587 : Nat := 3446270085467537618696479

theorem tailTrace_6711587 : CollatzResearch.WordTrace tailWord_6711587 prefixEnd_6711587 3446270085467537618696479 := by
  unfold tailWord_6711587
  simp only [CollatzResearch.WordTrace]
  refine ⟨244791688336074021647261015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163194458890716014431507343 244791688336074021647261015)
  ·
    refine ⟨367187532504111032470891523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244791688336074021647261015 367187532504111032470891523)
    ·
      refine ⟨550781298756166548706337285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367187532504111032470891523 550781298756166548706337285)
      ·
        refine ⟨103271493516781227882438241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 550781298756166548706337285 103271493516781227882438241)
        ·
          refine ⟨77453620137585920911828681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103271493516781227882438241 77453620137585920911828681)
          ·
            refine ⟨58090215103189440683871511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77453620137585920911828681 58090215103189440683871511)
            ·
              refine ⟨87135322654784161025807267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58090215103189440683871511 87135322654784161025807267)
              ·
                refine ⟨130702983982176241538710901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87135322654784161025807267 130702983982176241538710901)
                ·
                  refine ⟨12253404748329022644254147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130702983982176241538710901 12253404748329022644254147)
                  ·
                    refine ⟨18380107122493533966381221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12253404748329022644254147 18380107122493533966381221)
                    ·
                      refine ⟨3446270085467537618696479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18380107122493533966381221 3446270085467537618696479)
                      ·
                        rfl

theorem cell23_6711587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_6711587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711587 prefixEnd_6711587 := by exact prefixLift 6711587
  have htrace : WordTrace (prefixWord ++ tailWord_6711587) baseStart_6711587 baseEnd_6711587 := by
    simpa [prefixWord, tailWord_6711587, baseEnd_6711587] using wordTrace_append hprefix tailTrace_6711587
  have hstable : (prefixWord ++ tailWord_6711587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711587).length < 2 ^ (prefixWord ++ tailWord_6711587).sum := by decide
  have hdescent : baseEnd_6711587 < baseStart_6711587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711614 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_6711614 : Nat := 118140960795 + 6711614 * 2 ^ 59
def prefixEnd_6711614 : Nat := 4983230072969 + 3 ^ 40 * 6711614 * 2
def baseEnd_6711614 : Nat := 1148761316481736337686285

theorem tailTrace_6711614 : CollatzResearch.WordTrace tailWord_6711614 prefixEnd_6711614 1148761316481736337686285 := by
  unfold tailWord_6711614
  simp only [CollatzResearch.WordTrace]
  refine ⟨30599084138372025657311737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163195115404650803505662597 30599084138372025657311737)
  ·
    refine ⟨22949313103779019242983803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30599084138372025657311737 22949313103779019242983803)
    ·
      refine ⟨34423969655668528864475705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22949313103779019242983803 34423969655668528864475705)
      ·
        refine ⟨25817977241751396648356779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34423969655668528864475705 25817977241751396648356779)
        ·
          refine ⟨38726965862627094972535169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25817977241751396648356779 38726965862627094972535169)
          ·
            refine ⟨29045224396970321229401377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38726965862627094972535169 29045224396970321229401377)
            ·
              refine ⟨21783918297727740922051033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29045224396970321229401377 21783918297727740922051033)
              ·
                refine ⟨16337938723295805691538275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21783918297727740922051033 16337938723295805691538275)
                ·
                  refine ⟨24506908084943708537307413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16337938723295805691538275 24506908084943708537307413)
                  ·
                    refine ⟨1148761316481736337686285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24506908084943708537307413 1148761316481736337686285)
                    ·
                      rfl

theorem cell23_6711614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_6711614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711614 prefixEnd_6711614 := by exact prefixLift 6711614
  have htrace : WordTrace (prefixWord ++ tailWord_6711614) baseStart_6711614 baseEnd_6711614 := by
    simpa [prefixWord, tailWord_6711614, baseEnd_6711614] using wordTrace_append hprefix tailTrace_6711614
  have hstable : (prefixWord ++ tailWord_6711614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711614).length < 2 ^ (prefixWord ++ tailWord_6711614).sum := by decide
  have hdescent : baseEnd_6711614 < baseStart_6711614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711648 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 2, 4]
def baseStart_6711648 : Nat := 118140960795 + 6711648 * 2 ^ 59
def prefixEnd_6711648 : Nat := 4983230072969 + 3 ^ 40 * 6711648 * 2
def baseEnd_6711648 : Nat := 1148767135929153960011233

theorem tailTrace_6711648 : CollatzResearch.WordTrace tailWord_6711648 prefixEnd_6711648 1148767135929153960011233 := by
  unfold tailWord_6711648
  simp only [CollatzResearch.WordTrace]
  refine ⟨122396956594426514532615799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163195942125902019376821065 122396956594426514532615799)
  ·
    refine ⟨183595434891639771798923699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122396956594426514532615799 183595434891639771798923699)
    ·
      refine ⟨275393152337459657698385549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183595434891639771798923699 275393152337459657698385549)
      ·
        refine ⟨103272432126547371636894581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275393152337459657698385549 103272432126547371636894581)
        ·
          refine ⟨9681790511863816090958867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103272432126547371636894581 9681790511863816090958867)
          ·
            refine ⟨14522685767795724136438301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9681790511863816090958867 14522685767795724136438301)
            ·
              refine ⟨5446007162923396551164363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14522685767795724136438301 5446007162923396551164363)
              ·
                refine ⟨8169010744385094826746545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5446007162923396551164363 8169010744385094826746545)
                ·
                  refine ⟨6126758058288821120059909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8169010744385094826746545 6126758058288821120059909)
                  ·
                    refine ⟨1148767135929153960011233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6126758058288821120059909 1148767135929153960011233)
                    ·
                      rfl

theorem cell23_6711648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 4].length) (baseStart_6711648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711648 prefixEnd_6711648 := by exact prefixLift 6711648
  have htrace : WordTrace (prefixWord ++ tailWord_6711648) baseStart_6711648 baseEnd_6711648 := by
    simpa [prefixWord, tailWord_6711648, baseEnd_6711648] using wordTrace_append hprefix tailTrace_6711648
  have hstable : (prefixWord ++ tailWord_6711648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711648).length < 2 ^ (prefixWord ++ tailWord_6711648).sum := by decide
  have hdescent : baseEnd_6711648 < baseStart_6711648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711658 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_6711658 : Nat := 118140960795 + 6711658 * 2 ^ 59
def prefixEnd_6711658 : Nat := 4983230072969 + 3 ^ 40 * 6711658 * 2
def baseEnd_6711658 : Nat := 3446306542594006840908653

theorem tailTrace_6711658 : CollatzResearch.WordTrace tailWord_6711658 prefixEnd_6711658 3446306542594006840908653 := by
  unfold tailWord_6711658
  simp only [CollatzResearch.WordTrace]
  refine ⟨61198569479704200193273907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163196185279211200515397085 61198569479704200193273907)
  ·
    refine ⟨91797854219556300289910861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61198569479704200193273907 91797854219556300289910861)
    ·
      refine ⟨34424195332333612608716573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91797854219556300289910861 34424195332333612608716573)
      ·
        refine ⟨12909073249625104728268715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34424195332333612608716573 12909073249625104728268715)
        ·
          refine ⟨19363609874437657092403073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12909073249625104728268715 19363609874437657092403073)
          ·
            refine ⟨14522707405828242819302305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19363609874437657092403073 14522707405828242819302305)
            ·
              refine ⟨10892030554371182114476729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14522707405828242819302305 10892030554371182114476729)
              ·
                refine ⟨8169022915778386585857547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10892030554371182114476729 8169022915778386585857547)
                ·
                  refine ⟨12253534373667579878786321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8169022915778386585857547 12253534373667579878786321)
                  ·
                    refine ⟨9190150780250684909089741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12253534373667579878786321 9190150780250684909089741)
                    ·
                      refine ⟨3446306542594006840908653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9190150780250684909089741 3446306542594006840908653)
                      ·
                        rfl

theorem cell23_6711658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_6711658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711658 prefixEnd_6711658 := by exact prefixLift 6711658
  have htrace : WordTrace (prefixWord ++ tailWord_6711658) baseStart_6711658 baseEnd_6711658 := by
    simpa [prefixWord, tailWord_6711658, baseEnd_6711658] using wordTrace_append hprefix tailTrace_6711658
  have hstable : (prefixWord ++ tailWord_6711658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711658).length < 2 ^ (prefixWord ++ tailWord_6711658).sum := by decide
  have hdescent : baseEnd_6711658 < baseStart_6711658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711697 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_6711697 : Nat := 118140960795 + 6711697 * 2 ^ 59
def prefixEnd_6711697 : Nat := 4983230072969 + 3 ^ 40 * 6711697 * 2
def baseEnd_6711697 : Nat := 3446326568339532188320973

theorem tailTrace_6711697 : CollatzResearch.WordTrace tailWord_6711697 prefixEnd_6711697 3446326568339532188320973 := by
  unfold tailWord_6711697
  simp only [CollatzResearch.WordTrace]
  refine ⟨244795700365675510433765345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163197133577117006955843563 244795700365675510433765345)
  ·
    refine ⟨183596775274256632825324009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244795700365675510433765345 183596775274256632825324009)
    ·
      refine ⟨137697581455692474618993007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183596775274256632825324009 137697581455692474618993007)
      ·
        refine ⟨206546372183538711928489511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137697581455692474618993007 206546372183538711928489511)
        ·
          refine ⟨309819558275308067892734267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206546372183538711928489511 309819558275308067892734267)
          ·
            refine ⟨464729337412962101839101401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309819558275308067892734267 464729337412962101839101401)
            ·
              refine ⟨348547003059721576379326051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464729337412962101839101401 348547003059721576379326051)
              ·
                refine ⟨522820504589582364568989077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348547003059721576379326051 522820504589582364568989077)
                ·
                  refine ⟨24507211152636673339171363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 522820504589582364568989077 24507211152636673339171363)
                  ·
                    refine ⟨36760816728955010008757045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24507211152636673339171363 36760816728955010008757045)
                    ·
                      refine ⟨3446326568339532188320973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36760816728955010008757045 3446326568339532188320973)
                      ·
                        rfl

theorem cell23_6711697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_6711697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711697 prefixEnd_6711697 := by exact prefixLift 6711697
  have htrace : WordTrace (prefixWord ++ tailWord_6711697) baseStart_6711697 baseEnd_6711697 := by
    simpa [prefixWord, tailWord_6711697, baseEnd_6711697] using wordTrace_append hprefix tailTrace_6711697
  have hstable : (prefixWord ++ tailWord_6711697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711697).length < 2 ^ (prefixWord ++ tailWord_6711697).sum := by decide
  have hdescent : baseEnd_6711697 < baseStart_6711697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711711 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 1, 4, 2]
def baseStart_6711711 : Nat := 118140960795 + 6711711 * 2 ^ 59
def prefixEnd_6711711 : Nat := 4983230072969 + 3 ^ 40 * 6711711 * 2
def baseEnd_6711711 : Nat := 3446333757068695133545909

theorem tailTrace_6711711 : CollatzResearch.WordTrace tailWord_6711711 prefixEnd_6711711 3446333757068695133545909 := by
  unfold tailWord_6711711
  simp only [CollatzResearch.WordTrace]
  refine ⟨244796210987624790824774987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163197473991749860549849991 244796210987624790824774987)
  ·
    refine ⟨367194316481437186237162481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244796210987624790824774987 367194316481437186237162481)
    ·
      refine ⟨275395737361077889677871861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367194316481437186237162481 275395737361077889677871861)
      ·
        refine ⟨25818350377601052157300487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275395737361077889677871861 25818350377601052157300487)
        ·
          refine ⟨38727525566401578235950731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25818350377601052157300487 38727525566401578235950731)
          ·
            refine ⟨58091288349602367353926097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38727525566401578235950731 58091288349602367353926097)
            ·
              refine ⟨43568466262201775515444573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58091288349602367353926097 43568466262201775515444573)
              ·
                refine ⟨16338174848325665818291715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43568466262201775515444573 16338174848325665818291715)
                ·
                  refine ⟨24507262272488498727437573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16338174848325665818291715 24507262272488498727437573)
                  ·
                    refine ⟨4595111676091593511394545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24507262272488498727437573 4595111676091593511394545)
                    ·
                      refine ⟨3446333757068695133545909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4595111676091593511394545 3446333757068695133545909)
                      ·
                        rfl

theorem cell23_6711711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_6711711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711711 prefixEnd_6711711 := by exact prefixLift 6711711
  have htrace : WordTrace (prefixWord ++ tailWord_6711711) baseStart_6711711 baseEnd_6711711 := by
    simpa [prefixWord, tailWord_6711711, baseEnd_6711711] using wordTrace_append hprefix tailTrace_6711711
  have hstable : (prefixWord ++ tailWord_6711711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711711).length < 2 ^ (prefixWord ++ tailWord_6711711).sum := by decide
  have hdescent : baseEnd_6711711 < baseStart_6711711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711714 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_6711714 : Nat := 118140960795 + 6711714 * 2 ^ 59
def prefixEnd_6711714 : Nat := 4983230072969 + 3 ^ 40 * 6711714 * 2
def baseEnd_6711714 : Nat := 3446335297510658621808395

theorem tailTrace_6711714 : CollatzResearch.WordTrace tailWord_6711714 prefixEnd_6711714 3446335297510658621808395 := by
  unfold tailWord_6711714
  simp only [CollatzResearch.WordTrace]
  refine ⟨61199080101653480584283549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163197546937742614891422797 61199080101653480584283549)
  ·
    refine ⟨22949655038120055219106331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61199080101653480584283549 22949655038120055219106331)
    ·
      refine ⟨34424482557180082828659497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22949655038120055219106331 34424482557180082828659497)
      ·
        refine ⟨25818361917885062121494623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34424482557180082828659497 25818361917885062121494623)
        ·
          refine ⟨38727542876827593182241935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25818361917885062121494623 38727542876827593182241935)
          ·
            refine ⟨58091314315241389773362903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38727542876827593182241935 58091314315241389773362903)
            ·
              refine ⟨87136971472862084660044355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58091314315241389773362903 87136971472862084660044355)
              ·
                refine ⟨130705457209293126990066533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87136971472862084660044355 130705457209293126990066533)
                ·
                  refine ⟨24507273226742461310637475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130705457209293126990066533 24507273226742461310637475)
                  ·
                    refine ⟨36760909840113691965956213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24507273226742461310637475 36760909840113691965956213)
                    ·
                      refine ⟨3446335297510658621808395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36760909840113691965956213 3446335297510658621808395)
                      ·
                        rfl

theorem cell23_6711714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_6711714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711714 prefixEnd_6711714 := by exact prefixLift 6711714
  have htrace : WordTrace (prefixWord ++ tailWord_6711714) baseStart_6711714 baseEnd_6711714 := by
    simpa [prefixWord, tailWord_6711714, baseEnd_6711714] using wordTrace_append hprefix tailTrace_6711714
  have hstable : (prefixWord ++ tailWord_6711714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711714).length < 2 ^ (prefixWord ++ tailWord_6711714).sum := by decide
  have hdescent : baseEnd_6711714 < baseStart_6711714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711717 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 9]
def baseStart_6711717 : Nat := 118140960795 + 6711717 * 2 ^ 59
def prefixEnd_6711717 : Nat := 4983230072969 + 3 ^ 40 * 6711717 * 2
def baseEnd_6711717 : Nat := 382926315328069123341209

theorem tailTrace_6711717 : CollatzResearch.WordTrace tailWord_6711717 prefixEnd_6711717 382926315328069123341209 := by
  unfold tailWord_6711717
  simp only [CollatzResearch.WordTrace]
  refine ⟨244796429825603053849493405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163197619883735369232995603 244796429825603053849493405)
  ·
    refine ⟨91798661184601145193560027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244796429825603053849493405 91798661184601145193560027)
    ·
      refine ⟨137697991776901717790340041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91798661184601145193560027 137697991776901717790340041)
      ·
        refine ⟨103273493832676288342755031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137697991776901717790340041 103273493832676288342755031)
        ·
          refine ⟨154910240749014432514132547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103273493832676288342755031 154910240749014432514132547)
          ·
            refine ⟨232365361123521648771198821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154910240749014432514132547 232365361123521648771198821)
            ·
              refine ⟨43568505210660309144599779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232365361123521648771198821 43568505210660309144599779)
              ·
                refine ⟨65352757815990463716899669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43568505210660309144599779 65352757815990463716899669)
                ·
                  refine ⟨382926315328069123341209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65352757815990463716899669 382926315328069123341209)
                  ·
                    rfl

theorem cell23_6711717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_6711717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711717 prefixEnd_6711717 := by exact prefixLift 6711717
  have htrace : WordTrace (prefixWord ++ tailWord_6711717) baseStart_6711717 baseEnd_6711717 := by
    simpa [prefixWord, tailWord_6711717, baseEnd_6711717] using wordTrace_append hprefix tailTrace_6711717
  have hstable : (prefixWord ++ tailWord_6711717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711717).length < 2 ^ (prefixWord ++ tailWord_6711717).sum := by decide
  have hdescent : baseEnd_6711717 < baseStart_6711717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711744 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 3]
def baseStart_6711744 : Nat := 118140960795 + 6711744 * 2 ^ 59
def prefixEnd_6711744 : Nat := 4983230072969 + 3 ^ 40 * 6711744 * 2
def baseEnd_6711744 : Nat := 3446350701930293504433257

theorem tailTrace_6711744 : CollatzResearch.WordTrace tailWord_6711744 prefixEnd_6711744 3446350701930293504433257 := by
  unfold tailWord_6711744
  simp only [CollatzResearch.WordTrace]
  refine ⟨122398707298252618730363143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163198276397670158307150857 122398707298252618730363143)
  ·
    refine ⟨183598060947378928095544715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122398707298252618730363143 183598060947378928095544715)
    ·
      refine ⟨275397091421068392143317073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183598060947378928095544715 275397091421068392143317073)
      ·
        refine ⟨206547818565801294107487805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275397091421068392143317073 206547818565801294107487805)
        ·
          refine ⟨77455431962175485290307927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206547818565801294107487805 77455431962175485290307927)
          ·
            refine ⟨116183147943263227935461891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77455431962175485290307927 116183147943263227935461891)
            ·
              refine ⟨174274721914894841903192837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116183147943263227935461891 174274721914894841903192837)
              ·
                refine ⟨32676510359042782856848657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174274721914894841903192837 32676510359042782856848657)
                ·
                  refine ⟨24507382769282087142636493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32676510359042782856848657 24507382769282087142636493)
                  ·
                    refine ⟨9190268538480782678488685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24507382769282087142636493 9190268538480782678488685)
                    ·
                      refine ⟨3446350701930293504433257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9190268538480782678488685 3446350701930293504433257)
                      ·
                        rfl

theorem cell23_6711744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_6711744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711744 prefixEnd_6711744 := by exact prefixLift 6711744
  have htrace : WordTrace (prefixWord ++ tailWord_6711744) baseStart_6711744 baseEnd_6711744 := by
    simpa [prefixWord, tailWord_6711744, baseEnd_6711744] using wordTrace_append hprefix tailTrace_6711744
  have hstable : (prefixWord ++ tailWord_6711744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711744).length < 2 ^ (prefixWord ++ tailWord_6711744).sum := by decide
  have hdescent : baseEnd_6711744 < baseStart_6711744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711747 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 3, 7]
def baseStart_6711747 : Nat := 118140960795 + 6711747 * 2 ^ 59
def prefixEnd_6711747 : Nat := 4983230072969 + 3 ^ 40 * 6711747 * 2
def baseEnd_6711747 : Nat := 1148784080790752330898581

theorem tailTrace_6711747 : CollatzResearch.WordTrace tailWord_6711747 prefixEnd_6711747 1148784080790752330898581 := by
  unfold tailWord_6711747
  simp only [CollatzResearch.WordTrace]
  refine ⟨244797524015494368973085495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163198349343662912648723663 244797524015494368973085495)
  ·
    refine ⟨367196286023241553459628243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244797524015494368973085495 367196286023241553459628243)
    ·
      refine ⟨550794429034862330189442365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367196286023241553459628243 550794429034862330189442365)
      ·
        refine ⟨206547910888073373821040887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550794429034862330189442365 206547910888073373821040887)
        ·
          refine ⟨309821866332110060731561331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206547910888073373821040887 309821866332110060731561331)
          ·
            refine ⟨464732799498165091097341997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309821866332110060731561331 464732799498165091097341997)
            ·
              refine ⟨174274799811811909161503249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464732799498165091097341997 174274799811811909161503249)
              ·
                refine ⟨130706099858858931871127437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174274799811811909161503249 130706099858858931871127437)
                ·
                  refine ⟨49014787447072099451672789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130706099858858931871127437 49014787447072099451672789)
                  ·
                    refine ⟨1148784080790752330898581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49014787447072099451672789 1148784080790752330898581)
                    ·
                      rfl

theorem cell23_6711747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 7].length) (baseStart_6711747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711747 prefixEnd_6711747 := by exact prefixLift 6711747
  have htrace : WordTrace (prefixWord ++ tailWord_6711747) baseStart_6711747 baseEnd_6711747 := by
    simpa [prefixWord, tailWord_6711747, baseEnd_6711747] using wordTrace_append hprefix tailTrace_6711747
  have hstable : (prefixWord ++ tailWord_6711747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711747).length < 2 ^ (prefixWord ++ tailWord_6711747).sum := by decide
  have hdescent : baseEnd_6711747 < baseStart_6711747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711751 : List Nat := [1, 1, 4, 1, 1, 5, 1, 4, 5]
def baseStart_6711751 : Nat := 118140960795 + 6711751 * 2 ^ 59
def prefixEnd_6711751 : Nat := 4983230072969 + 3 ^ 40 * 6711751 * 2
def baseEnd_6711751 : Nat := 382928255143874997449525

theorem tailTrace_6711751 : CollatzResearch.WordTrace tailWord_6711751 prefixEnd_6711751 382928255143874997449525 := by
  unfold tailWord_6711751
  simp only [CollatzResearch.WordTrace]
  refine ⟨244797669907479877656231107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163198446604986585104154071 244797669907479877656231107)
  ·
    refine ⟨367196504861219816484346661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244797669907479877656231107 367196504861219816484346661)
    ·
      refine ⟨68849344661478715590814999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367196504861219816484346661 68849344661478715590814999)
      ·
        refine ⟨103274016992218073386222499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68849344661478715590814999 103274016992218073386222499)
        ·
          refine ⟨154911025488327110079333749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103274016992218073386222499 154911025488327110079333749)
          ·
            refine ⟨14522908639530666569937539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154911025488327110079333749 14522908639530666569937539)
            ·
              refine ⟨21784362959295999854906309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14522908639530666569937539 21784362959295999854906309)
              ·
                refine ⟨4084568054867999972794933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21784362959295999854906309 4084568054867999972794933)
                ·
                  refine ⟨382928255143874997449525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4084568054867999972794933 382928255143874997449525)
                  ·
                    rfl

theorem cell23_6711751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 5].length) (baseStart_6711751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711751 prefixEnd_6711751 := by exact prefixLift 6711751
  have htrace : WordTrace (prefixWord ++ tailWord_6711751) baseStart_6711751 baseEnd_6711751 := by
    simpa [prefixWord, tailWord_6711751, baseEnd_6711751] using wordTrace_append hprefix tailTrace_6711751
  have hstable : (prefixWord ++ tailWord_6711751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711751).length < 2 ^ (prefixWord ++ tailWord_6711751).sum := by decide
  have hdescent : baseEnd_6711751 < baseStart_6711751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711781 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_6711781 : Nat := 118140960795 + 6711781 * 2 ^ 59
def prefixEnd_6711781 : Nat := 4983230072969 + 3 ^ 40 * 6711781 * 2
def baseEnd_6711781 : Nat := 1148789900238169953223529

theorem tailTrace_6711781 : CollatzResearch.WordTrace tailWord_6711781 prefixEnd_6711781 1148789900238169953223529 := by
  unfold tailWord_6711781
  simp only [CollatzResearch.WordTrace]
  refine ⟨244798764097371192779823197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163199176064914128519882131 244798764097371192779823197)
  ·
    refine ⟨91799536536514197292433699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244798764097371192779823197 91799536536514197292433699)
    ·
      refine ⟨137699304804771295938650549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91799536536514197292433699 137699304804771295938650549)
      ·
        refine ⟨12909309825447308994248489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137699304804771295938650549 12909309825447308994248489)
        ·
          refine ⟨9681982369085481745686367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12909309825447308994248489 9681982369085481745686367)
          ·
            refine ⟨14522973553628222618529551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9681982369085481745686367 14522973553628222618529551)
            ·
              refine ⟨21784460330442333927794327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14522973553628222618529551 21784460330442333927794327)
              ·
                refine ⟨32676690495663500891691491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21784460330442333927794327 32676690495663500891691491)
                ·
                  refine ⟨49015035743495251337537237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32676690495663500891691491 49015035743495251337537237)
                  ·
                    refine ⟨1148789900238169953223529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49015035743495251337537237 1148789900238169953223529)
                    ·
                      rfl

theorem cell23_6711781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_6711781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711781 prefixEnd_6711781 := by exact prefixLift 6711781
  have htrace : WordTrace (prefixWord ++ tailWord_6711781) baseStart_6711781 baseEnd_6711781 := by
    simpa [prefixWord, tailWord_6711781, baseEnd_6711781] using wordTrace_append hprefix tailTrace_6711781
  have hstable : (prefixWord ++ tailWord_6711781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711781).length < 2 ^ (prefixWord ++ tailWord_6711781).sum := by decide
  have hdescent : baseEnd_6711781 < baseStart_6711781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711801 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 2, 4, 2]
def baseStart_6711801 : Nat := 118140960795 + 6711801 * 2 ^ 59
def prefixEnd_6711801 : Nat := 4983230072969 + 3 ^ 40 * 6711801 * 2
def baseEnd_6711801 : Nat := 3446379970327599781420495

theorem tailTrace_6711801 : CollatzResearch.WordTrace tailWord_6711801 prefixEnd_6711801 3446379970327599781420495 := by
  unfold tailWord_6711801
  simp only [CollatzResearch.WordTrace]
  refine ⟨244799493557298736195551257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163199662371532490797034171 244799493557298736195551257)
  ·
    refine ⟨183599620167974052146663443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244799493557298736195551257 183599620167974052146663443)
    ·
      refine ⟨275399430251961078219995165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183599620167974052146663443 275399430251961078219995165)
      ·
        refine ⟨103274786344485404332498187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275399430251961078219995165 103274786344485404332498187)
        ·
          refine ⟨154912179516728106498747281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103274786344485404332498187 154912179516728106498747281)
          ·
            refine ⟨116184134637546079874060461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154912179516728106498747281 116184134637546079874060461)
            ·
              refine ⟨43569050489079779952772673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116184134637546079874060461 43569050489079779952772673)
              ·
                refine ⟨32676787866809834964579505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43569050489079779952772673 32676787866809834964579505)
                ·
                  refine ⟨24507590900107376223434629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32676787866809834964579505 24507590900107376223434629)
                  ·
                    refine ⟨4595173293770133041893993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24507590900107376223434629 4595173293770133041893993)
                    ·
                      refine ⟨3446379970327599781420495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4595173293770133041893993 3446379970327599781420495)
                      ·
                        rfl

theorem cell23_6711801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_6711801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711801 prefixEnd_6711801 := by exact prefixLift 6711801
  have htrace : WordTrace (prefixWord ++ tailWord_6711801) baseStart_6711801 baseEnd_6711801 := by
    simpa [prefixWord, tailWord_6711801, baseEnd_6711801] using wordTrace_append hprefix tailTrace_6711801
  have hstable : (prefixWord ++ tailWord_6711801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711801).length < 2 ^ (prefixWord ++ tailWord_6711801).sum := by decide
  have hdescent : baseEnd_6711801 < baseStart_6711801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711811 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 3, 4]
def baseStart_6711811 : Nat := 118140960795 + 6711811 * 2 ^ 59
def prefixEnd_6711811 : Nat := 4983230072969 + 3 ^ 40 * 6711811 * 2
def baseEnd_6711811 : Nat := 1148795035044714914098483

theorem tailTrace_6711811 : CollatzResearch.WordTrace tailWord_6711811 prefixEnd_6711811 1148795035044714914098483 := by
  unfold tailWord_6711811
  simp only [CollatzResearch.WordTrace]
  refine ⟨244799858287262507903415287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163199905524841671935610191 244799858287262507903415287)
  ·
    refine ⟨367199787430893761855122931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244799858287262507903415287 367199787430893761855122931)
    ·
      refine ⟨550799681146340642782684397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367199787430893761855122931 550799681146340642782684397)
      ·
        refine ⟨206549880429877741043506649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550799681146340642782684397 206549880429877741043506649)
        ·
          refine ⟨154912410322408305782629987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206549880429877741043506649 154912410322408305782629987)
          ·
            refine ⟨232368615483612458673944981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154912410322408305782629987 232368615483612458673944981)
            ·
              refine ⟨10892278850794334000341171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232368615483612458673944981 10892278850794334000341171)
              ·
                refine ⟨16338418276191501000511757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10892278850794334000341171 16338418276191501000511757)
                ·
                  refine ⟨6126906853571812875191909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16338418276191501000511757 6126906853571812875191909)
                  ·
                    refine ⟨1148795035044714914098483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6126906853571812875191909 1148795035044714914098483)
                    ·
                      rfl

theorem cell23_6711811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 4].length) (baseStart_6711811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711811 prefixEnd_6711811 := by exact prefixLift 6711811
  have htrace : WordTrace (prefixWord ++ tailWord_6711811) baseStart_6711811 baseEnd_6711811 := by
    simpa [prefixWord, tailWord_6711811, baseEnd_6711811] using wordTrace_append hprefix tailTrace_6711811
  have hstable : (prefixWord ++ tailWord_6711811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711811).length < 2 ^ (prefixWord ++ tailWord_6711811).sum := by decide
  have hdescent : baseEnd_6711811 < baseStart_6711811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711851 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 3]
def baseStart_6711851 : Nat := 118140960795 + 6711851 * 2 ^ 59
def prefixEnd_6711851 : Nat := 4983230072969 + 3 ^ 40 * 6711851 * 2
def baseEnd_6711851 : Nat := 3446405644360324585795265

theorem tailTrace_6711851 : CollatzResearch.WordTrace tailWord_6711851 prefixEnd_6711851 3446405644360324585795265 := by
  unfold tailWord_6711851
  simp only [CollatzResearch.WordTrace]
  refine ⟨244801317207117594734871407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163200878138078396489914271 244801317207117594734871407)
  ·
    refine ⟨367201975810676392102307111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244801317207117594734871407 367201975810676392102307111)
    ·
      refine ⟨550802963716014588153460667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367201975810676392102307111 550802963716014588153460667)
      ·
        refine ⟨826204445574021882230191001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550802963716014588153460667 826204445574021882230191001)
        ·
          refine ⟨619653334180516411672643251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826204445574021882230191001 619653334180516411672643251)
          ·
            refine ⟨929480001270774617508964877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619653334180516411672643251 929480001270774617508964877)
            ·
              refine ⟨348555000476540481565861829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 929480001270774617508964877 348555000476540481565861829)
              ·
                refine ⟨65354062589351340293599093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348555000476540481565861829 65354062589351340293599093)
                ·
                  refine ⟨6126943367751688152524915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65354062589351340293599093 6126943367751688152524915)
                  ·
                    refine ⟨9190415051627532228787373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6126943367751688152524915 9190415051627532228787373)
                    ·
                      refine ⟨3446405644360324585795265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9190415051627532228787373 3446405644360324585795265)
                      ·
                        rfl

theorem cell23_6711851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 3].length) (baseStart_6711851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711851 prefixEnd_6711851 := by exact prefixLift 6711851
  have htrace : WordTrace (prefixWord ++ tailWord_6711851) baseStart_6711851 baseEnd_6711851 := by
    simpa [prefixWord, tailWord_6711851, baseEnd_6711851] using wordTrace_append hprefix tailTrace_6711851
  have hstable : (prefixWord ++ tailWord_6711851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711851).length < 2 ^ (prefixWord ++ tailWord_6711851).sum := by decide
  have hdescent : baseEnd_6711851 < baseStart_6711851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6711962 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6711962 : Nat := 118140960795 + 6711962 * 2 ^ 59
def prefixEnd_6711962 : Nat := 4983230072969 + 3 ^ 40 * 6711962 * 2
def baseEnd_6711962 : Nat := 3446462640712973651507255

theorem tailTrace_6711962 : CollatzResearch.WordTrace tailWord_6711962 prefixEnd_6711962 3446462640712973651507255 := by
  unfold tailWord_6711962
  simp only [CollatzResearch.WordTrace]
  refine ⟨61201341427428865173040535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163203577139810307128108093 61201341427428865173040535)
  ·
    refine ⟨91802012141143297759560803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61201341427428865173040535 91802012141143297759560803)
    ·
      refine ⟨137703018211714946639341205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91802012141143297759560803 137703018211714946639341205)
      ·
        refine ⟨6454828978674138123719119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137703018211714946639341205 6454828978674138123719119)
        ·
          refine ⟨9682243468011207185578679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454828978674138123719119 9682243468011207185578679)
          ·
            refine ⟨14523365202016810778368019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9682243468011207185578679 14523365202016810778368019)
            ·
              refine ⟨21785047803025216167552029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14523365202016810778368019 21785047803025216167552029)
              ·
                refine ⟨8169392926134456062832011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21785047803025216167552029 8169392926134456062832011)
                ·
                  refine ⟨12254089389201684094248017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8169392926134456062832011 12254089389201684094248017)
                  ·
                    refine ⟨9190567041901263070686013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12254089389201684094248017 9190567041901263070686013)
                    ·
                      refine ⟨3446462640712973651507255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9190567041901263070686013 3446462640712973651507255)
                      ·
                        rfl

theorem cell23_6711962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6711962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6711962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6711962 prefixEnd_6711962 := by exact prefixLift 6711962
  have htrace : WordTrace (prefixWord ++ tailWord_6711962) baseStart_6711962 baseEnd_6711962 := by
    simpa [prefixWord, tailWord_6711962, baseEnd_6711962] using wordTrace_append hprefix tailTrace_6711962
  have hstable : (prefixWord ++ tailWord_6711962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6711962).length < 2 ^ (prefixWord ++ tailWord_6711962).sum := by decide
  have hdescent : baseEnd_6711962 < baseStart_6711962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6711962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712051 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 6, 5]
def baseStart_6712051 : Nat := 118140960795 + 6712051 * 2 ^ 59
def prefixEnd_6712051 : Nat := 4983230072969 + 3 ^ 40 * 6712051 * 2
def baseEnd_6712051 : Nat := 1148836113497074601098115

theorem tailTrace_6712051 : CollatzResearch.WordTrace tailWord_6712051 prefixEnd_6712051 1148836113497074601098115 := by
  unfold tailWord_6712051
  simp only [CollatzResearch.WordTrace]
  refine ⟨244808611806393028892152007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163205741204262019261434671 244808611806393028892152007)
  ·
    refine ⟨367212917709589543338228011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244808611806393028892152007 367212917709589543338228011)
    ·
      refine ⟨550819376564384315007342017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367212917709589543338228011 550819376564384315007342017)
      ·
        refine ⟨413114532423288236255506513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550819376564384315007342017 413114532423288236255506513)
        ·
          refine ⟨309835899317466177191629885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413114532423288236255506513 309835899317466177191629885)
          ·
            refine ⟨116188462244049816446861207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309835899317466177191629885 116188462244049816446861207)
            ·
              refine ⟨174282693366074724670291811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116188462244049816446861207 174282693366074724670291811)
              ·
                refine ⟨261424040049112087005437717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174282693366074724670291811 261424040049112087005437717)
                ·
                  refine ⟨12254251877302129078379893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261424040049112087005437717 12254251877302129078379893)
                  ·
                    refine ⟨1148836113497074601098115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12254251877302129078379893 1148836113497074601098115)
                    ·
                      rfl

theorem cell23_6712051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 5].length) (baseStart_6712051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712051 prefixEnd_6712051 := by exact prefixLift 6712051
  have htrace : WordTrace (prefixWord ++ tailWord_6712051) baseStart_6712051 baseEnd_6712051 := by
    simpa [prefixWord, tailWord_6712051, baseEnd_6712051] using wordTrace_append hprefix tailTrace_6712051
  have hstable : (prefixWord ++ tailWord_6712051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712051).length < 2 ^ (prefixWord ++ tailWord_6712051).sum := by decide
  have hdescent : baseEnd_6712051 < baseStart_6712051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712053 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6712053 : Nat := 118140960795 + 6712053 * 2 ^ 59
def prefixEnd_6712053 : Nat := 4983230072969 + 3 ^ 40 * 6712053 * 2
def baseEnd_6712053 : Nat := 3446509367452532795469337

theorem tailTrace_6712053 : CollatzResearch.WordTrace tailWord_6712053 prefixEnd_6712053 3446509367452532795469337 := by
  unfold tailWord_6712053
  simp only [CollatzResearch.WordTrace]
  refine ⟨244808684752385783233724813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163205789834923855489149875 244808684752385783233724813)
  ·
    refine ⟨91803256782144668712646805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244808684752385783233724813 91803256782144668712646805)
    ·
      refine ⟨4303277661663031345905319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91803256782144668712646805 4303277661663031345905319)
      ·
        refine ⟨6454916492494547018857979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4303277661663031345905319 6454916492494547018857979)
        ·
          refine ⟨9682374738741820528286969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454916492494547018857979 9682374738741820528286969)
          ·
            refine ⟨7261781054056365396215227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9682374738741820528286969 7261781054056365396215227)
            ·
              refine ⟨10892671581084548094322841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7261781054056365396215227 10892671581084548094322841)
              ·
                refine ⟨8169503685813411070742131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10892671581084548094322841 8169503685813411070742131)
                ·
                  refine ⟨12254255528720116606113197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8169503685813411070742131 12254255528720116606113197)
                  ·
                    refine ⟨4595345823270043727292449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12254255528720116606113197 4595345823270043727292449)
                    ·
                      refine ⟨3446509367452532795469337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4595345823270043727292449 3446509367452532795469337)
                      ·
                        rfl

theorem cell23_6712053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6712053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712053 prefixEnd_6712053 := by exact prefixLift 6712053
  have htrace : WordTrace (prefixWord ++ tailWord_6712053) baseStart_6712053 baseEnd_6712053 := by
    simpa [prefixWord, tailWord_6712053, baseEnd_6712053] using wordTrace_append hprefix tailTrace_6712053
  have hstable : (prefixWord ++ tailWord_6712053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712053).length < 2 ^ (prefixWord ++ tailWord_6712053).sum := by decide
  have hdescent : baseEnd_6712053 < baseStart_6712053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712061 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_6712061 : Nat := 118140960795 + 6712061 * 2 ^ 59
def prefixEnd_6712061 : Nat := 4983230072969 + 3 ^ 40 * 6712061 * 2
def baseEnd_6712061 : Nat := 3446513475297768764169299

theorem tailTrace_6712061 : CollatzResearch.WordTrace tailWord_6712061 prefixEnd_6712061 3446513475297768764169299 := by
  unfold tailWord_6712061
  simp only [CollatzResearch.WordTrace]
  refine ⟨244808976536356800600016037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163205984357571200400010691 244808976536356800600016037)
  ·
    refine ⟨45901683100566900112503007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244808976536356800600016037 45901683100566900112503007)
    ·
      refine ⟨68852524650850350168754511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45901683100566900112503007 68852524650850350168754511)
      ·
        refine ⟨103278786976275525253131767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68852524650850350168754511 103278786976275525253131767)
        ·
          refine ⟨154918180464413287879697651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103278786976275525253131767 154918180464413287879697651)
          ·
            refine ⟨232377270696619931819546477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154918180464413287879697651 232377270696619931819546477)
            ·
              refine ⟨87141476511232474432329929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232377270696619931819546477 87141476511232474432329929)
              ·
                refine ⟨65356107383424355824247447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87141476511232474432329929 65356107383424355824247447)
                ·
                  refine ⟨98034161075136533736371171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65356107383424355824247447 98034161075136533736371171)
                  ·
                    refine ⟨147051241612704800604556757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98034161075136533736371171 147051241612704800604556757)
                    ·
                      refine ⟨3446513475297768764169299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147051241612704800604556757 3446513475297768764169299)
                      ·
                        rfl

theorem cell23_6712061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_6712061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712061 prefixEnd_6712061 := by exact prefixLift 6712061
  have htrace : WordTrace (prefixWord ++ tailWord_6712061) baseStart_6712061 baseEnd_6712061 := by
    simpa [prefixWord, tailWord_6712061, baseEnd_6712061] using wordTrace_append hprefix tailTrace_6712061
  have hstable : (prefixWord ++ tailWord_6712061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712061).length < 2 ^ (prefixWord ++ tailWord_6712061).sum := by decide
  have hdescent : baseEnd_6712061 < baseStart_6712061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712108 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_6712108 : Nat := 118140960795 + 6712108 * 2 ^ 59
def prefixEnd_6712108 : Nat := 4983230072969 + 3 ^ 40 * 6712108 * 2
def baseEnd_6712108 : Nat := 3446537608888530080281583

theorem tailTrace_6712108 : CollatzResearch.WordTrace tailWord_6712108 prefixEnd_6712108 3446537608888530080281583 := by
  unfold tailWord_6712108
  simp only [CollatzResearch.WordTrace]
  refine ⟨122405345383593263813488489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163207127178124351751317985 122405345383593263813488489)
  ·
    refine ⟨91804009037694947860116367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122405345383593263813488489 91804009037694947860116367)
    ·
      refine ⟨137706013556542421790174551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91804009037694947860116367 137706013556542421790174551)
      ·
        refine ⟨206559020334813632685261827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137706013556542421790174551 206559020334813632685261827)
        ·
          refine ⟨309838530502220449027892741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206559020334813632685261827 309838530502220449027892741)
          ·
            refine ⟨58094724469166334192729889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309838530502220449027892741 58094724469166334192729889)
            ·
              refine ⟨43571043351874750644547417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58094724469166334192729889 43571043351874750644547417)
              ·
                refine ⟨32678282513906062983410563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43571043351874750644547417 32678282513906062983410563)
                ·
                  refine ⟨49017423770859094475115845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32678282513906062983410563 49017423770859094475115845)
                  ·
                    refine ⟨9190766957036080214084221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49017423770859094475115845 9190766957036080214084221)
                    ·
                      refine ⟨3446537608888530080281583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9190766957036080214084221 3446537608888530080281583)
                      ·
                        rfl

theorem cell23_6712108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_6712108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712108 prefixEnd_6712108 := by exact prefixLift 6712108
  have htrace : WordTrace (prefixWord ++ tailWord_6712108) baseStart_6712108 baseEnd_6712108 := by
    simpa [prefixWord, tailWord_6712108, baseEnd_6712108] using wordTrace_append hprefix tailTrace_6712108
  have hstable : (prefixWord ++ tailWord_6712108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712108).length < 2 ^ (prefixWord ++ tailWord_6712108).sum := by decide
  have hdescent : baseEnd_6712108 < baseStart_6712108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712115 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 3, 4]
def baseStart_6712115 : Nat := 118140960795 + 6712115 * 2 ^ 59
def prefixEnd_6712115 : Nat := 4983230072969 + 3 ^ 40 * 6712115 * 2
def baseEnd_6712115 : Nat := 1148847067751037184298017

theorem tailTrace_6712115 : CollatzResearch.WordTrace tailWord_6712115 prefixEnd_6712115 1148847067751037184298017 := by
  unfold tailWord_6712115
  simp only [CollatzResearch.WordTrace]
  refine ⟨244810946078161167822481799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163207297385440778548321199 244810946078161167822481799)
  ·
    refine ⟨367216419117241751733722699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244810946078161167822481799 367216419117241751733722699)
    ·
      refine ⟨550824628675862627600584049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367216419117241751733722699 550824628675862627600584049)
      ·
        refine ⟨413118471506896970700438037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550824628675862627600584049 413118471506896970700438037)
        ·
          refine ⟨19364928351885795501583033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 413118471506896970700438037 19364928351885795501583033)
          ·
            refine ⟨14523696263914346626187275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19364928351885795501583033 14523696263914346626187275)
            ·
              refine ⟨21785544395871519939280913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14523696263914346626187275 21785544395871519939280913)
              ·
                refine ⟨16339158296903639954460685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21785544395871519939280913 16339158296903639954460685)
                ·
                  refine ⟨6127184361338864982922757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16339158296903639954460685 6127184361338864982922757)
                  ·
                    refine ⟨1148847067751037184298017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6127184361338864982922757 1148847067751037184298017)
                    ·
                      rfl

theorem cell23_6712115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 4].length) (baseStart_6712115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712115 prefixEnd_6712115 := by exact prefixLift 6712115
  have htrace : WordTrace (prefixWord ++ tailWord_6712115) baseStart_6712115 baseEnd_6712115 := by
    simpa [prefixWord, tailWord_6712115, baseEnd_6712115] using wordTrace_append hprefix tailTrace_6712115
  have hstable : (prefixWord ++ tailWord_6712115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712115).length < 2 ^ (prefixWord ++ tailWord_6712115).sum := by decide
  have hdescent : baseEnd_6712115 < baseStart_6712115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712122 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4]
def baseStart_6712122 : Nat := 118140960795 + 6712122 * 2 ^ 59
def prefixEnd_6712122 : Nat := 4983230072969 + 3 ^ 40 * 6712122 * 2
def baseEnd_6712122 : Nat := 3446544797617693025506519

theorem tailTrace_6712122 : CollatzResearch.WordTrace tailWord_6712122 prefixEnd_6712122 3446544797617693025506519 := by
  unfold tailWord_6712122
  simp only [CollatzResearch.WordTrace]
  refine ⟨61202800347283952004496655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163207467592757205345324413 61202800347283952004496655)
  ·
    refine ⟨91804200520925928006744983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61202800347283952004496655 91804200520925928006744983)
    ·
      refine ⟨137706300781388892010117475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91804200520925928006744983 137706300781388892010117475)
      ·
        refine ⟨206559451172083338015176213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137706300781388892010117475 206559451172083338015176213)
        ·
          refine ⟨9682474273691406469461385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206559451172083338015176213 9682474273691406469461385)
          ·
            refine ⟨7261855705268554852096039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9682474273691406469461385 7261855705268554852096039)
            ·
              refine ⟨10892783557902832278144059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7261855705268554852096039 10892783557902832278144059)
              ·
                refine ⟨16339175336854248417216089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10892783557902832278144059 16339175336854248417216089)
                ·
                  refine ⟨12254381502640686312912067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16339175336854248417216089 12254381502640686312912067)
                  ·
                    refine ⟨18381572253961029469368101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12254381502640686312912067 18381572253961029469368101)
                    ·
                      refine ⟨3446544797617693025506519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18381572253961029469368101 3446544797617693025506519)
                      ·
                        rfl

theorem cell23_6712122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_6712122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712122 prefixEnd_6712122 := by exact prefixLift 6712122
  have htrace : WordTrace (prefixWord ++ tailWord_6712122) baseStart_6712122 baseEnd_6712122 := by
    simpa [prefixWord, tailWord_6712122, baseEnd_6712122] using wordTrace_append hprefix tailTrace_6712122
  have hstable : (prefixWord ++ tailWord_6712122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712122).length < 2 ^ (prefixWord ++ tailWord_6712122).sum := by decide
  have hdescent : baseEnd_6712122 < baseStart_6712122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712165 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 1, 5, 2]
def baseStart_6712165 : Nat := 118140960795 + 6712165 * 2 ^ 59
def prefixEnd_6712165 : Nat := 4983230072969 + 3 ^ 40 * 6712165 * 2
def baseEnd_6712165 : Nat := 3446566877285836357268821

theorem tailTrace_6712165 : CollatzResearch.WordTrace tailWord_6712165 prefixEnd_6712165 3446566877285836357268821 := by
  unfold tailWord_6712165
  simp only [CollatzResearch.WordTrace]
  refine ⟨244812769727980026361801949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163208513151986684241201299 244812769727980026361801949)
  ·
    refine ⟨91804788647992509885675731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244812769727980026361801949 91804788647992509885675731)
    ·
      refine ⟨137707182971988764828513597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91804788647992509885675731 137707182971988764828513597)
      ·
        refine ⟨51640193614495786810692599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137707182971988764828513597 51640193614495786810692599)
        ·
          refine ⟨77460290421743680216038899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51640193614495786810692599 77460290421743680216038899)
          ·
            refine ⟨116190435632615520324058349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77460290421743680216038899 116190435632615520324058349)
            ·
              refine ⟨43571413362230820121521881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116190435632615520324058349 43571413362230820121521881)
              ·
                refine ⟨32678560021673115091141411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43571413362230820121521881 32678560021673115091141411)
                ·
                  refine ⟨49017840032509672636712117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32678560021673115091141411 49017840032509672636712117)
                  ·
                    refine ⟨4595422503047781809691761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49017840032509672636712117 4595422503047781809691761)
                    ·
                      refine ⟨3446566877285836357268821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4595422503047781809691761 3446566877285836357268821)
                      ·
                        rfl

theorem cell23_6712165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_6712165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712165 prefixEnd_6712165 := by exact prefixLift 6712165
  have htrace : WordTrace (prefixWord ++ tailWord_6712165) baseStart_6712165 baseEnd_6712165 := by
    simpa [prefixWord, tailWord_6712165, baseEnd_6712165] using wordTrace_append hprefix tailTrace_6712165
  have hstable : (prefixWord ++ tailWord_6712165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712165).length < 2 ^ (prefixWord ++ tailWord_6712165).sum := by decide
  have hdescent : baseEnd_6712165 < baseStart_6712165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712188 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_6712188 : Nat := 118140960795 + 6712188 * 2 ^ 59
def prefixEnd_6712188 : Nat := 4983230072969 + 3 ^ 40 * 6712188 * 2
def baseEnd_6712188 : Nat := 1148859562446963255760405

theorem tailTrace_6712188 : CollatzResearch.WordTrace tailWord_6712188 prefixEnd_6712188 1148859562446963255760405 := by
  unfold tailWord_6712188
  simp only [CollatzResearch.WordTrace]
  refine ⟨122406804303448350644944609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163209072404597800859926145 122406804303448350644944609)
  ·
    refine ⟨91805103227586262983708457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122406804303448350644944609 91805103227586262983708457)
    ·
      refine ⟨68853827420689697237781343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91805103227586262983708457 68853827420689697237781343)
      ·
        refine ⟨103280741131034545856672015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68853827420689697237781343 103280741131034545856672015)
        ·
          refine ⟨154921111696551818785008023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103280741131034545856672015 154921111696551818785008023)
          ·
            refine ⟨232381667544827728177512035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154921111696551818785008023 232381667544827728177512035)
            ·
              refine ⟨348572501317241592266268053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232381667544827728177512035 348572501317241592266268053)
              ·
                refine ⟨16339335999245699637481315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 348572501317241592266268053 16339335999245699637481315)
                ·
                  refine ⟨24509003998868549456221973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16339335999245699637481315 24509003998868549456221973)
                  ·
                    refine ⟨1148859562446963255760405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24509003998868549456221973 1148859562446963255760405)
                    ·
                      rfl

theorem cell23_6712188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_6712188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712188 prefixEnd_6712188 := by exact prefixLift 6712188
  have htrace : WordTrace (prefixWord ++ tailWord_6712188) baseStart_6712188 baseEnd_6712188 := by
    simpa [prefixWord, tailWord_6712188, baseEnd_6712188] using wordTrace_append hprefix tailTrace_6712188
  have hstable : (prefixWord ++ tailWord_6712188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712188).length < 2 ^ (prefixWord ++ tailWord_6712188).sum := by decide
  have hdescent : baseEnd_6712188 < baseStart_6712188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712189 : List Nat := [1, 4, 1, 1, 2, 1, 5, 3, 1, 1, 3]
def baseStart_6712189 : Nat := 118140960795 + 6712189 * 2 ^ 59
def prefixEnd_6712189 : Nat := 4983230072969 + 3 ^ 40 * 6712189 * 2
def baseEnd_6712189 : Nat := 3446579200821544263368711

theorem tailTrace_6712189 : CollatzResearch.WordTrace tailWord_6712189 prefixEnd_6712189 3446579200821544263368711 := by
  unfold tailWord_6712189
  simp only [CollatzResearch.WordTrace]
  refine ⟨244813645079893078460675621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163209096719928718973783747 244813645079893078460675621)
  ·
    refine ⟨45902558452479952211376679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244813645079893078460675621 45902558452479952211376679)
    ·
      refine ⟨68853837678719928317065019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45902558452479952211376679 68853837678719928317065019)
      ·
        refine ⟨103280756518079892475597529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68853837678719928317065019 103280756518079892475597529)
        ·
          refine ⟨77460567388559919356698147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103280756518079892475597529 77460567388559919356698147)
          ·
            refine ⟨116190851082839879035047221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77460567388559919356698147 116190851082839879035047221)
            ·
              refine ⟨10892892289016238659535677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116190851082839879035047221 10892892289016238659535677)
              ·
                refine ⟨4084834608381089497325879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10892892289016238659535677 4084834608381089497325879)
                ·
                  refine ⟨6127251912571634245988819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084834608381089497325879 6127251912571634245988819)
                  ·
                    refine ⟨9190877868857451368983229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6127251912571634245988819 9190877868857451368983229)
                    ·
                      refine ⟨3446579200821544263368711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9190877868857451368983229 3446579200821544263368711)
                      ·
                        rfl

theorem cell23_6712189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_6712189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712189 prefixEnd_6712189 := by exact prefixLift 6712189
  have htrace : WordTrace (prefixWord ++ tailWord_6712189) baseStart_6712189 baseEnd_6712189 := by
    simpa [prefixWord, tailWord_6712189, baseEnd_6712189] using wordTrace_append hprefix tailTrace_6712189
  have hstable : (prefixWord ++ tailWord_6712189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712189).length < 2 ^ (prefixWord ++ tailWord_6712189).sum := by decide
  have hdescent : baseEnd_6712189 < baseStart_6712189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712195 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 4]
def baseStart_6712195 : Nat := 118140960795 + 6712195 * 2 ^ 59
def prefixEnd_6712195 : Nat := 4983230072969 + 3 ^ 40 * 6712195 * 2
def baseEnd_6712195 : Nat := 3446582281705471239893683

theorem tailTrace_6712195 : CollatzResearch.WordTrace tailWord_6712195 prefixEnd_6712195 3446582281705471239893683 := by
  unfold tailWord_6712195
  simp only [CollatzResearch.WordTrace]
  refine ⟨244813863917871341485394039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163209242611914227656929359 244813863917871341485394039)
  ·
    refine ⟨367220795876807012228091059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244813863917871341485394039 367220795876807012228091059)
    ·
      refine ⟨550831193815210518342136589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367220795876807012228091059 550831193815210518342136589)
      ·
        refine ⟨206561697680703944378301221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 550831193815210518342136589 206561697680703944378301221)
        ·
          refine ⟨38730318315131989570931479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206561697680703944378301221 38730318315131989570931479)
          ·
            refine ⟨58095477472697984356397219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38730318315131989570931479 58095477472697984356397219)
            ·
              refine ⟨87143216209046976534595829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58095477472697984356397219 87143216209046976534595829)
              ·
                refine ⟨8169676519598154050118359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87143216209046976534595829 8169676519598154050118359)
                ·
                  refine ⟨12254514779397231075177539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8169676519598154050118359 12254514779397231075177539)
                  ·
                    refine ⟨18381772169095846612766309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12254514779397231075177539 18381772169095846612766309)
                    ·
                      refine ⟨3446582281705471239893683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18381772169095846612766309 3446582281705471239893683)
                      ·
                        rfl

theorem cell23_6712195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_6712195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712195 prefixEnd_6712195 := by exact prefixLift 6712195
  have htrace : WordTrace (prefixWord ++ tailWord_6712195) baseStart_6712195 baseEnd_6712195 := by
    simpa [prefixWord, tailWord_6712195, baseEnd_6712195] using wordTrace_append hprefix tailTrace_6712195
  have hstable : (prefixWord ++ tailWord_6712195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712195).length < 2 ^ (prefixWord ++ tailWord_6712195).sum := by decide
  have hdescent : baseEnd_6712195 < baseStart_6712195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712215 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_6712215 : Nat := 118140960795 + 6712215 * 2 ^ 59
def prefixEnd_6712215 : Nat := 4983230072969 + 3 ^ 40 * 6712215 * 2
def baseEnd_6712215 : Nat := 3446592551318561161643591

theorem tailTrace_6712215 : CollatzResearch.WordTrace tailWord_6712215 prefixEnd_6712215 3446592551318561161643591 := by
  unfold tailWord_6712215
  simp only [CollatzResearch.WordTrace]
  refine ⟨244814593377798884901122099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163209728918532589934081399 244814593377798884901122099)
  ·
    refine ⟨367221890066698327351683149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244814593377798884901122099 367221890066698327351683149)
    ·
      refine ⟨137708208775011872756881181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367221890066698327351683149 137708208775011872756881181)
      ·
        refine ⟨51640578290629452283830443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137708208775011872756881181 51640578290629452283830443)
        ·
          refine ⟨77460867435944178425745665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51640578290629452283830443 77460867435944178425745665)
          ·
            refine ⟨58095650576958133819309249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77460867435944178425745665 58095650576958133819309249)
            ·
              refine ⟨43571737932718600364481937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58095650576958133819309249 43571737932718600364481937)
              ·
                refine ⟨32678803449538950273361453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43571737932718600364481937 32678803449538950273361453)
                ·
                  refine ⟨12254551293577106352510545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32678803449538950273361453 12254551293577106352510545)
                  ·
                    refine ⟨9190913470182829764382909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12254551293577106352510545 9190913470182829764382909)
                    ·
                      refine ⟨3446592551318561161643591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9190913470182829764382909 3446592551318561161643591)
                      ·
                        rfl

theorem cell23_6712215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_6712215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712215 prefixEnd_6712215 := by exact prefixLift 6712215
  have htrace : WordTrace (prefixWord ++ tailWord_6712215) baseStart_6712215 baseEnd_6712215 := by
    simpa [prefixWord, tailWord_6712215, baseEnd_6712215] using wordTrace_append hprefix tailTrace_6712215
  have hstable : (prefixWord ++ tailWord_6712215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712215).length < 2 ^ (prefixWord ++ tailWord_6712215).sum := by decide
  have hdescent : baseEnd_6712215 < baseStart_6712215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712225 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6712225 : Nat := 118140960795 + 6712225 * 2 ^ 59
def prefixEnd_6712225 : Nat := 4983230072969 + 3 ^ 40 * 6712225 * 2
def baseEnd_6712225 : Nat := 3446597686125106122518545

theorem tailTrace_6712225 : CollatzResearch.WordTrace tailWord_6712225 prefixEnd_6712225 3446597686125106122518545 := by
  unfold tailWord_6712225
  simp only [CollatzResearch.WordTrace]
  refine ⟨244814958107762656608986129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163209972071841771072657419 244814958107762656608986129)
  ·
    refine ⟨183611218580821992456739597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244814958107762656608986129 183611218580821992456739597)
    ·
      refine ⟨68854206967808247171277349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183611218580821992456739597 68854206967808247171277349)
      ·
        refine ⟨12910163806464046344614503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68854206967808247171277349 12910163806464046344614503)
        ·
          refine ⟨19365245709696069516921755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12910163806464046344614503 19365245709696069516921755)
          ·
            refine ⟨29047868564544104275382633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19365245709696069516921755 29047868564544104275382633)
            ·
              refine ⟨21785901423408078206536975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29047868564544104275382633 21785901423408078206536975)
              ·
                refine ⟨32678852135112117309805463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21785901423408078206536975 32678852135112117309805463)
                ·
                  refine ⟨49018278202668175964708195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32678852135112117309805463 49018278202668175964708195)
                  ·
                    refine ⟨73527417304002263947062293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49018278202668175964708195 73527417304002263947062293)
                    ·
                      refine ⟨3446597686125106122518545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73527417304002263947062293 3446597686125106122518545)
                      ·
                        rfl

theorem cell23_6712225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6712225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712225 prefixEnd_6712225 := by exact prefixLift 6712225
  have htrace : WordTrace (prefixWord ++ tailWord_6712225) baseStart_6712225 baseEnd_6712225 := by
    simpa [prefixWord, tailWord_6712225, baseEnd_6712225] using wordTrace_append hprefix tailTrace_6712225
  have hstable : (prefixWord ++ tailWord_6712225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712225).length < 2 ^ (prefixWord ++ tailWord_6712225).sum := by decide
  have hdescent : baseEnd_6712225 < baseStart_6712225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712249 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 1, 2, 3]
def baseStart_6712249 : Nat := 118140960795 + 6712249 * 2 ^ 59
def prefixEnd_6712249 : Nat := 4983230072969 + 3 ^ 40 * 6712249 * 2
def baseEnd_6712249 : Nat := 3446610009660814028618435

theorem tailTrace_6712249 : CollatzResearch.WordTrace tailWord_6712249 prefixEnd_6712249 3446610009660814028618435 := by
  unfold tailWord_6712249
  simp only [CollatzResearch.WordTrace]
  refine ⟨244815833459675708707859801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163210555639783805805239867 244815833459675708707859801)
  ·
    refine ⟨183611875094756781530894851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244815833459675708707859801 183611875094756781530894851)
    ·
      refine ⟨275417812642135172296342277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183611875094756781530894851 275417812642135172296342277)
      ·
        refine ⟨51640839870400344805564177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275417812642135172296342277 51640839870400344805564177)
        ·
          refine ⟨38730629902800258604173133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51640839870400344805564177 38730629902800258604173133)
          ·
            refine ⟨14523986213550096976564925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38730629902800258604173133 14523986213550096976564925)
            ·
              refine ⟨5446494830081286366211847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14523986213550096976564925 5446494830081286366211847)
              ·
                refine ⟨8169742245121929549317771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5446494830081286366211847 8169742245121929549317771)
                ·
                  refine ⟨12254613367682894323976657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8169742245121929549317771 12254613367682894323976657)
                  ·
                    refine ⟨9190960025762170742982493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12254613367682894323976657 9190960025762170742982493)
                    ·
                      refine ⟨3446610009660814028618435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9190960025762170742982493 3446610009660814028618435)
                      ·
                        rfl

theorem cell23_6712249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_6712249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712249 prefixEnd_6712249 := by exact prefixLift 6712249
  have htrace : WordTrace (prefixWord ++ tailWord_6712249) baseStart_6712249 baseEnd_6712249 := by
    simpa [prefixWord, tailWord_6712249, baseEnd_6712249] using wordTrace_append hprefix tailTrace_6712249
  have hstable : (prefixWord ++ tailWord_6712249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712249).length < 2 ^ (prefixWord ++ tailWord_6712249).sum := by decide
  have hdescent : baseEnd_6712249 < baseStart_6712249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712325 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 7]
def baseStart_6712325 : Nat := 118140960795 + 6712325 * 2 ^ 59
def prefixEnd_6712325 : Nat := 4983230072969 + 3 ^ 40 * 6712325 * 2
def baseEnd_6712325 : Nat := 382961003798950636807565

theorem tailTrace_6712325 : CollatzResearch.WordTrace tailWord_6712325 prefixEnd_6712325 382961003798950636807565 := by
  unfold tailWord_6712325
  simp only [CollatzResearch.WordTrace]
  refine ⟨244818605407400373687626429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163212403604933582458417619 244818605407400373687626429)
  ·
    refine ⟨91806977027775140132859911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244818605407400373687626429 91806977027775140132859911)
    ·
      refine ⟨137710465541662710199289867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91806977027775140132859911 137710465541662710199289867)
      ·
        refine ⟨206565698312494065298934801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137710465541662710199289867 206565698312494065298934801)
        ·
          refine ⟨154924273734370548974201101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206565698312494065298934801 154924273734370548974201101)
          ·
            refine ⟨58096602650388955865325413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154924273734370548974201101 58096602650388955865325413)
            ·
              refine ⟨10893112996947929224748515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58096602650388955865325413 10893112996947929224748515)
              ·
                refine ⟨16339669495421893837122773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10893112996947929224748515 16339669495421893837122773)
                ·
                  refine ⟨382961003798950636807565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16339669495421893837122773 382961003798950636807565)
                  ·
                    rfl

theorem cell23_6712325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_6712325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712325 prefixEnd_6712325 := by exact prefixLift 6712325
  have htrace : WordTrace (prefixWord ++ tailWord_6712325) baseStart_6712325 baseEnd_6712325 := by
    simpa [prefixWord, tailWord_6712325, baseEnd_6712325] using wordTrace_append hprefix tailTrace_6712325
  have hstable : (prefixWord ++ tailWord_6712325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712325).length < 2 ^ (prefixWord ++ tailWord_6712325).sum := by decide
  have hdescent : baseEnd_6712325 < baseStart_6712325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712355 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 1, 7]
def baseStart_6712355 : Nat := 118140960795 + 6712355 * 2 ^ 59
def prefixEnd_6712355 : Nat := 4983230072969 + 3 ^ 40 * 6712355 * 2
def baseEnd_6712355 : Nat := 1148888146203396871297649

theorem tailTrace_6712355 : CollatzResearch.WordTrace tailWord_6712355 prefixEnd_6712355 1148888146203396871297649 := by
  unfold tailWord_6712355
  simp only [CollatzResearch.WordTrace]
  refine ⟨244819699597291688811218519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163213133064861125874145679 244819699597291688811218519)
  ·
    refine ⟨367229549395937533216827779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244819699597291688811218519 367229549395937533216827779)
    ·
      refine ⟨550844324093906299825241669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367229549395937533216827779 550844324093906299825241669)
      ·
        refine ⟨103283310767607431217232813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 550844324093906299825241669 103283310767607431217232813)
        ·
          refine ⟨38731241537852786706462305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103283310767607431217232813 38731241537852786706462305)
          ·
            refine ⟨29048431153389590029846729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38731241537852786706462305 29048431153389590029846729)
            ·
              refine ⟨21786323365042192522385047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29048431153389590029846729 21786323365042192522385047)
              ·
                refine ⟨32679485047563288783577571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21786323365042192522385047 32679485047563288783577571)
                ·
                  refine ⟨49019227571344933175366357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32679485047563288783577571 49019227571344933175366357)
                  ·
                    refine ⟨1148888146203396871297649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49019227571344933175366357 1148888146203396871297649)
                    ·
                      rfl

theorem cell23_6712355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 7].length) (baseStart_6712355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712355 prefixEnd_6712355 := by exact prefixLift 6712355
  have htrace : WordTrace (prefixWord ++ tailWord_6712355) baseStart_6712355 baseEnd_6712355 := by
    simpa [prefixWord, tailWord_6712355, baseEnd_6712355] using wordTrace_append hprefix tailTrace_6712355
  have hstable : (prefixWord ++ tailWord_6712355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712355).length < 2 ^ (prefixWord ++ tailWord_6712355).sum := by decide
  have hdescent : baseEnd_6712355 < baseStart_6712355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712382 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_6712382 : Nat := 118140960795 + 6712382 * 2 ^ 59
def prefixEnd_6712382 : Nat := 4983230072969 + 3 ^ 40 * 6712382 * 2
def baseEnd_6712382 : Nat := 3446678302587862008255323

theorem tailTrace_6712382 : CollatzResearch.WordTrace tailWord_6712382 prefixEnd_6712382 3446678302587862008255323 := by
  unfold tailWord_6712382
  simp only [CollatzResearch.WordTrace]
  refine ⟨30602585546024234052806425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163213789578795914948300933 30602585546024234052806425)
  ·
    refine ⟨22951939159518175539604819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30602585546024234052806425 22951939159518175539604819)
    ·
      refine ⟨34427908739277263309407229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22951939159518175539604819 34427908739277263309407229)
      ·
        refine ⟨12910465777228973741027711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34427908739277263309407229 12910465777228973741027711)
        ·
          refine ⟨19365698665843460611541567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12910465777228973741027711 19365698665843460611541567)
          ·
            refine ⟨29048547998765190917312351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19365698665843460611541567 29048547998765190917312351)
            ·
              refine ⟨43572821998147786375968527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29048547998765190917312351 43572821998147786375968527)
              ·
                refine ⟨65359232997221679563952791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43572821998147786375968527 65359232997221679563952791)
                ·
                  refine ⟨98038849495832519345929187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65359232997221679563952791 98038849495832519345929187)
                  ·
                    refine ⟨147058274243748779018893781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98038849495832519345929187 147058274243748779018893781)
                    ·
                      refine ⟨3446678302587862008255323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147058274243748779018893781 3446678302587862008255323)
                      ·
                        rfl

theorem cell23_6712382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_6712382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712382 prefixEnd_6712382 := by exact prefixLift 6712382
  have htrace : WordTrace (prefixWord ++ tailWord_6712382) baseStart_6712382 baseEnd_6712382 := by
    simpa [prefixWord, tailWord_6712382, baseEnd_6712382] using wordTrace_append hprefix tailTrace_6712382
  have hstable : (prefixWord ++ tailWord_6712382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712382).length < 2 ^ (prefixWord ++ tailWord_6712382).sum := by decide
  have hdescent : baseEnd_6712382 < baseStart_6712382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712392 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_6712392 : Nat := 118140960795 + 6712392 * 2 ^ 59
def prefixEnd_6712392 : Nat := 4983230072969 + 3 ^ 40 * 6712392 * 2
def baseEnd_6712392 : Nat := 3446683437394406969130277

theorem tailTrace_6712392 : CollatzResearch.WordTrace tailWord_6712392 prefixEnd_6712392 3446683437394406969130277 := by
  unfold tailWord_6712392
  simp only [CollatzResearch.WordTrace]
  refine ⟨122410524549078822065157715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163214032732105096086876953 122410524549078822065157715)
  ·
    refine ⟨183615786823618233097736573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122410524549078822065157715 183615786823618233097736573)
    ·
      refine ⟨68855920058856837411651215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183615786823618233097736573 68855920058856837411651215)
      ·
        refine ⟨103283880088285256117476823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68855920058856837411651215 103283880088285256117476823)
        ·
          refine ⟨154925820132427884176215235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103283880088285256117476823 154925820132427884176215235)
          ·
            refine ⟨232388730198641826264322853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154925820132427884176215235 232388730198641826264322853)
            ·
              refine ⟨43572886912245342424560535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232388730198641826264322853 43572886912245342424560535)
              ·
                refine ⟨65359330368368013636840803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43572886912245342424560535 65359330368368013636840803)
                ·
                  refine ⟨98038995552552020455261205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65359330368368013636840803 98038995552552020455261205)
                  ·
                    refine ⟨4595577916525875958840369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98038995552552020455261205 4595577916525875958840369)
                    ·
                      refine ⟨3446683437394406969130277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4595577916525875958840369 3446683437394406969130277)
                      ·
                        rfl

theorem cell23_6712392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_6712392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712392 prefixEnd_6712392 := by exact prefixLift 6712392
  have htrace : WordTrace (prefixWord ++ tailWord_6712392) baseStart_6712392 baseEnd_6712392 := by
    simpa [prefixWord, tailWord_6712392, baseEnd_6712392] using wordTrace_append hprefix tailTrace_6712392
  have hstable : (prefixWord ++ tailWord_6712392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712392).length < 2 ^ (prefixWord ++ tailWord_6712392).sum := by decide
  have hdescent : baseEnd_6712392 < baseStart_6712392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712419 : List Nat := [1, 1, 1, 5, 1, 1, 1, 7, 1, 4]
def baseStart_6712419 : Nat := 118140960795 + 6712419 * 2 ^ 59
def prefixEnd_6712419 : Nat := 4983230072969 + 3 ^ 40 * 6712419 * 2
def baseEnd_6712419 : Nat := 1148899100457359454497551

theorem tailTrace_6712419 : CollatzResearch.WordTrace tailWord_6712419 prefixEnd_6712419 1148899100457359454497551 := by
  unfold tailWord_6712419
  simp only [CollatzResearch.WordTrace]
  refine ⟨244822033869059827741548311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163214689246039885161032207 244822033869059827741548311)
  ·
    refine ⟨367233050803589741612322467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244822033869059827741548311 367233050803589741612322467)
    ·
      refine ⟨550849576205384612418483701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367233050803589741612322467 550849576205384612418483701)
      ·
        refine ⟨51642147769254807414232847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 550849576205384612418483701 51642147769254807414232847)
        ·
          refine ⟨77463221653882211121349271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51642147769254807414232847 77463221653882211121349271)
          ·
            refine ⟨116194832480823316682023907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77463221653882211121349271 116194832480823316682023907)
            ·
              refine ⟨174292248721234975023035861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116194832480823316682023907 174292248721234975023035861)
              ·
                refine ⟨4084974579403944727102403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 174292248721234975023035861 4084974579403944727102403)
                ·
                  refine ⟨6127461869105917090653605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084974579403944727102403 6127461869105917090653605)
                  ·
                    refine ⟨1148899100457359454497551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6127461869105917090653605 1148899100457359454497551)
                    ·
                      rfl

theorem cell23_6712419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 4].length) (baseStart_6712419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712419 prefixEnd_6712419 := by exact prefixLift 6712419
  have htrace : WordTrace (prefixWord ++ tailWord_6712419) baseStart_6712419 baseEnd_6712419 := by
    simpa [prefixWord, tailWord_6712419, baseEnd_6712419] using wordTrace_append hprefix tailTrace_6712419
  have hstable : (prefixWord ++ tailWord_6712419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712419).length < 2 ^ (prefixWord ++ tailWord_6712419).sum := by decide
  have hdescent : baseEnd_6712419 < baseStart_6712419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712429 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_6712429 : Nat := 118140960795 + 6712429 * 2 ^ 59
def prefixEnd_6712429 : Nat := 4983230072969 + 3 ^ 40 * 6712429 * 2
def baseEnd_6712429 : Nat := 3446702436178623324367607

theorem tailTrace_6712429 : CollatzResearch.WordTrace tailWord_6712429 prefixEnd_6712429 3446702436178623324367607 := by
  unfold tailWord_6712429
  simp only [CollatzResearch.WordTrace]
  refine ⟨244822398599023599449412341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163214932399349066299608227 244822398599023599449412341)
  ·
    refine ⟨22952099868658462448382407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244822398599023599449412341 22952099868658462448382407)
    ·
      refine ⟨34428149802987693672573611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22952099868658462448382407 34428149802987693672573611)
      ·
        refine ⟨51642224704481540508860417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34428149802987693672573611 51642224704481540508860417)
        ·
          refine ⟨38731668528361155381645313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51642224704481540508860417 38731668528361155381645313)
          ·
            refine ⟨29048751396270866536233985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38731668528361155381645313 29048751396270866536233985)
            ·
              refine ⟨21786563547203149902175489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29048751396270866536233985 21786563547203149902175489)
              ·
                refine ⟨16339922660402362426631617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21786563547203149902175489 16339922660402362426631617)
                ·
                  refine ⟨12254941995301771819973713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16339922660402362426631617 12254941995301771819973713)
                  ·
                    refine ⟨9191206496476328864980285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12254941995301771819973713 9191206496476328864980285)
                    ·
                      refine ⟨3446702436178623324367607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9191206496476328864980285 3446702436178623324367607)
                      ·
                        rfl

theorem cell23_6712429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_6712429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712429 prefixEnd_6712429 := by exact prefixLift 6712429
  have htrace : WordTrace (prefixWord ++ tailWord_6712429) baseStart_6712429 baseEnd_6712429 := by
    simpa [prefixWord, tailWord_6712429, baseEnd_6712429] using wordTrace_append hprefix tailTrace_6712429
  have hstable : (prefixWord ++ tailWord_6712429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712429).length < 2 ^ (prefixWord ++ tailWord_6712429).sum := by decide
  have hdescent : baseEnd_6712429 < baseStart_6712429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712432 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 6]
def baseStart_6712432 : Nat := 118140960795 + 6712432 * 2 ^ 59
def prefixEnd_6712432 : Nat := 4983230072969 + 3 ^ 40 * 6712432 * 2
def baseEnd_6712432 : Nat := 382967108513398534736677

theorem tailTrace_6712432 : CollatzResearch.WordTrace tailWord_6712432 prefixEnd_6712432 382967108513398534736677 := by
  unfold tailWord_6712432
  simp only [CollatzResearch.WordTrace]
  refine ⟨122411254009006365480885775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163215005345341820641181033 122411254009006365480885775)
  ·
    refine ⟨183616881013509548221328663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122411254009006365480885775 183616881013509548221328663)
    ·
      refine ⟨275425321520264322331992995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183616881013509548221328663 275425321520264322331992995)
      ·
        refine ⟨413137982280396483497989493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275425321520264322331992995 413137982280396483497989493)
        ·
          refine ⟨38731685838787170327936515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 413137982280396483497989493 38731685838787170327936515)
          ·
            refine ⟨58097528758180755491904773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38731685838787170327936515 58097528758180755491904773)
            ·
              refine ⟨10893286642158891654732145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58097528758180755491904773 10893286642158891654732145)
              ·
                refine ⟨8169964981619168741049109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10893286642158891654732145 8169964981619168741049109)
                ·
                  refine ⟨382967108513398534736677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8169964981619168741049109 382967108513398534736677)
                  ·
                    rfl

theorem cell23_6712432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 6].length) (baseStart_6712432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712432 prefixEnd_6712432 := by exact prefixLift 6712432
  have htrace : WordTrace (prefixWord ++ tailWord_6712432) baseStart_6712432 baseEnd_6712432 := by
    simpa [prefixWord, tailWord_6712432, baseEnd_6712432] using wordTrace_append hprefix tailTrace_6712432
  have hstable : (prefixWord ++ tailWord_6712432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712432).length < 2 ^ (prefixWord ++ tailWord_6712432).sum := by decide
  have hdescent : baseEnd_6712432 < baseStart_6712432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712455 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_6712455 : Nat := 118140960795 + 6712455 * 2 ^ 59
def prefixEnd_6712455 : Nat := 4983230072969 + 3 ^ 40 * 6712455 * 2
def baseEnd_6712455 : Nat := 3446715786675640222642487

theorem tailTrace_6712455 : CollatzResearch.WordTrace tailWord_6712455 prefixEnd_6712455 3446715786675640222642487 := by
  unfold tailWord_6712455
  simp only [CollatzResearch.WordTrace]
  refine ⟨244823346896929405889858819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163215564597952937259905879 244823346896929405889858819)
  ·
    refine ⟨367235020345394108834788229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244823346896929405889858819 367235020345394108834788229)
    ·
      refine ⟨68856566314761395406522793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367235020345394108834788229 68856566314761395406522793)
      ·
        refine ⟨51642424736071046554892095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68856566314761395406522793 51642424736071046554892095)
        ·
          refine ⟨77463637104106569832338143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51642424736071046554892095 77463637104106569832338143)
          ·
            refine ⟨116195455656159854748507215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77463637104106569832338143 116195455656159854748507215)
            ·
              refine ⟨174293183484239782122760823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116195455656159854748507215 174293183484239782122760823)
              ·
                refine ⟨261439775226359673184141235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174293183484239782122760823 261439775226359673184141235)
                ·
                  refine ⟨392159662839539509776211853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261439775226359673184141235 392159662839539509776211853)
                  ·
                    refine ⟨147059873564827316166079445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 392159662839539509776211853 147059873564827316166079445)
                    ·
                      refine ⟨3446715786675640222642487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147059873564827316166079445 3446715786675640222642487)
                      ·
                        rfl

theorem cell23_6712455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_6712455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712455 prefixEnd_6712455 := by exact prefixLift 6712455
  have htrace : WordTrace (prefixWord ++ tailWord_6712455) baseStart_6712455 baseEnd_6712455 := by
    simpa [prefixWord, tailWord_6712455, baseEnd_6712455] using wordTrace_append hprefix tailTrace_6712455
  have hstable : (prefixWord ++ tailWord_6712455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712455).length < 2 ^ (prefixWord ++ tailWord_6712455).sum := by decide
  have hdescent : baseEnd_6712455 < baseStart_6712455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712469 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_6712469 : Nat := 118140960795 + 6712469 * 2 ^ 59
def prefixEnd_6712469 : Nat := 4983230072969 + 3 ^ 40 * 6712469 * 2
def baseEnd_6712469 : Nat := 3446722975404803167867423

theorem tailTrace_6712469 : CollatzResearch.WordTrace tailWord_6712469 prefixEnd_6712469 3446722975404803167867423 := by
  unfold tailWord_6712469
  simp only [CollatzResearch.WordTrace]
  refine ⟨244823857518878686280868461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163215905012585790853912307 244823857518878686280868461)
  ·
    refine ⟨91808946569579507355325673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244823857518878686280868461 91808946569579507355325673)
    ·
      refine ⟨68856709927184630516494255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91808946569579507355325673 68856709927184630516494255)
      ·
        refine ⟨103285064890776945774741383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68856709927184630516494255 103285064890776945774741383)
        ·
          refine ⟨154927597336165418662112075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103285064890776945774741383 154927597336165418662112075)
          ·
            refine ⟨232391396004248127993168113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154927597336165418662112075 232391396004248127993168113)
            ·
              refine ⟨174293547003186095994876085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232391396004248127993168113 174293547003186095994876085)
              ·
                refine ⟨16340020031548696499519633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174293547003186095994876085 16340020031548696499519633)
                ·
                  refine ⟨12255015023661522374639725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16340020031548696499519633 12255015023661522374639725)
                  ·
                    refine ⟨4595630633873070890489897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12255015023661522374639725 4595630633873070890489897)
                    ·
                      refine ⟨3446722975404803167867423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4595630633873070890489897 3446722975404803167867423)
                      ·
                        rfl

theorem cell23_6712469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_6712469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712469 prefixEnd_6712469 := by exact prefixLift 6712469
  have htrace : WordTrace (prefixWord ++ tailWord_6712469) baseStart_6712469 baseEnd_6712469 := by
    simpa [prefixWord, tailWord_6712469, baseEnd_6712469] using wordTrace_append hprefix tailTrace_6712469
  have hstable : (prefixWord ++ tailWord_6712469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712469).length < 2 ^ (prefixWord ++ tailWord_6712469).sum := by decide
  have hdescent : baseEnd_6712469 < baseStart_6712469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712493 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_6712493 : Nat := 118140960795 + 6712493 * 2 ^ 59
def prefixEnd_6712493 : Nat := 4983230072969 + 3 ^ 40 * 6712493 * 2
def baseEnd_6712493 : Nat := 3446735298940511073967313

theorem tailTrace_6712493 : CollatzResearch.WordTrace tailWord_6712493 prefixEnd_6712493 3446735298940511073967313 := by
  unfold tailWord_6712493
  simp only [CollatzResearch.WordTrace]
  refine ⟨244824732870791738379742133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163216488580527825586494755 244824732870791738379742133)
  ·
    refine ⟨22952318706636725473100825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244824732870791738379742133 22952318706636725473100825)
    ·
      refine ⟨17214239029977544104825619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22952318706636725473100825 17214239029977544104825619)
      ·
        refine ⟨25821358544966316157238429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17214239029977544104825619 25821358544966316157238429)
        ·
          refine ⟨9683009454362368558964411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25821358544966316157238429 9683009454362368558964411)
          ·
            refine ⟨14524514181543552838446617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9683009454362368558964411 14524514181543552838446617)
            ·
              refine ⟨10893385636157664628834963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14524514181543552838446617 10893385636157664628834963)
              ·
                refine ⟨16340078454236496943252445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10893385636157664628834963 16340078454236496943252445)
                ·
                  refine ⟨6127529420338686353719667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16340078454236496943252445 6127529420338686353719667)
                  ·
                    refine ⟨9191294130508029530579501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6127529420338686353719667 9191294130508029530579501)
                    ·
                      refine ⟨3446735298940511073967313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9191294130508029530579501 3446735298940511073967313)
                      ·
                        rfl

theorem cell23_6712493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_6712493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712493 prefixEnd_6712493 := by exact prefixLift 6712493
  have htrace : WordTrace (prefixWord ++ tailWord_6712493) baseStart_6712493 baseEnd_6712493 := by
    simpa [prefixWord, tailWord_6712493, baseEnd_6712493] using wordTrace_append hprefix tailTrace_6712493
  have hstable : (prefixWord ++ tailWord_6712493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712493).length < 2 ^ (prefixWord ++ tailWord_6712493).sum := by decide
  have hdescent : baseEnd_6712493 < baseStart_6712493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712509 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_6712509 : Nat := 118140960795 + 6712509 * 2 ^ 59
def prefixEnd_6712509 : Nat := 4983230072969 + 3 ^ 40 * 6712509 * 2
def baseEnd_6712509 : Nat := 1148914504876994337122413

theorem tailTrace_6712509 : CollatzResearch.WordTrace tailWord_6712509 prefixEnd_6712509 1148914504876994337122413 := by
  unfold tailWord_6712509
  simp only [CollatzResearch.WordTrace]
  refine ⟨244825316438733773112324581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163216877625822515408216387 244825316438733773112324581)
  ·
    refine ⟨45904746832262582458560859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244825316438733773112324581 45904746832262582458560859)
    ·
      refine ⟨68857120248393873687841289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45904746832262582458560859 68857120248393873687841289)
      ·
        refine ⟨51642840186295405265880967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68857120248393873687841289 51642840186295405265880967)
        ·
          refine ⟨77464260279443107898821451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51642840186295405265880967 77464260279443107898821451)
          ·
            refine ⟨116196390419164661848232177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77464260279443107898821451 116196390419164661848232177)
            ·
              refine ⟨87147292814373496386174133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116196390419164661848232177 87147292814373496386174133)
              ·
                refine ⟨8170058701347515286203825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87147292814373496386174133 8170058701347515286203825)
                ·
                  refine ⟨6127544026010636464652869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8170058701347515286203825 6127544026010636464652869)
                  ·
                    refine ⟨1148914504876994337122413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6127544026010636464652869 1148914504876994337122413)
                    ·
                      rfl

theorem cell23_6712509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_6712509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712509 prefixEnd_6712509 := by exact prefixLift 6712509
  have htrace : WordTrace (prefixWord ++ tailWord_6712509) baseStart_6712509 baseEnd_6712509 := by
    simpa [prefixWord, tailWord_6712509, baseEnd_6712509] using wordTrace_append hprefix tailTrace_6712509
  have hstable : (prefixWord ++ tailWord_6712509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712509).length < 2 ^ (prefixWord ++ tailWord_6712509).sum := by decide
  have hdescent : baseEnd_6712509 < baseStart_6712509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712522 : List Nat := [3, 1, 2, 1, 3, 3, 1, 9]
def baseStart_6712522 : Nat := 118140960795 + 6712522 * 2 ^ 59
def prefixEnd_6712522 : Nat := 4983230072969 + 3 ^ 40 * 6712522 * 2
def baseEnd_6712522 : Nat := 127657414439981165203877

theorem tailTrace_6712522 : CollatzResearch.WordTrace tailWord_6712522 prefixEnd_6712522 127657414439981165203877 := by
  unfold tailWord_6712522
  simp only [CollatzResearch.WordTrace]
  refine ⟨61206447646921669083136955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163217193725124450888365213 61206447646921669083136955)
  ·
    refine ⟨91809671470382503624705433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61206447646921669083136955 91809671470382503624705433)
    ·
      refine ⟨68857253602786877718529075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91809671470382503624705433 68857253602786877718529075)
      ·
        refine ⟨103285880404180316577793613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68857253602786877718529075 103285880404180316577793613)
        ·
          refine ⟨38732205151567618716672605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103285880404180316577793613 38732205151567618716672605)
          ·
            refine ⟨14524576931837857018752227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38732205151567618716672605 14524576931837857018752227)
            ·
              refine ⟨21786865397756785528128341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14524576931837857018752227 21786865397756785528128341)
              ·
                refine ⟨127657414439981165203877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21786865397756785528128341 127657414439981165203877)
                ·
                  rfl

theorem cell23_6712522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 9].length) (baseStart_6712522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712522 prefixEnd_6712522 := by exact prefixLift 6712522
  have htrace : WordTrace (prefixWord ++ tailWord_6712522) baseStart_6712522 baseEnd_6712522 := by
    simpa [prefixWord, tailWord_6712522, baseEnd_6712522] using wordTrace_append hprefix tailTrace_6712522
  have hstable : (prefixWord ++ tailWord_6712522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712522).length < 2 ^ (prefixWord ++ tailWord_6712522).sum := by decide
  have hdescent : baseEnd_6712522 < baseStart_6712522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712552 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 2, 7]
def baseStart_6712552 : Nat := 118140960795 + 6712552 * 2 ^ 59
def prefixEnd_6712552 : Nat := 4983230072969 + 3 ^ 40 * 6712552 * 2
def baseEnd_6712552 : Nat := 1148921864766375447709847

theorem tailTrace_6712552 : CollatzResearch.WordTrace tailWord_6712552 prefixEnd_6712552 1148921864766375447709847 := by
  unfold tailWord_6712552
  simp only [CollatzResearch.WordTrace]
  refine ⟨122413442388788995728069955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163217923185051994304093273 122413442388788995728069955)
  ·
    refine ⟨183620163583183493592104933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122413442388788995728069955 183620163583183493592104933)
    ·
      refine ⟨34428780671846905048519675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183620163583183493592104933 34428780671846905048519675)
      ·
        refine ⟨51643171007770357572779513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34428780671846905048519675 51643171007770357572779513)
        ·
          refine ⟨38732378255827768179584635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51643171007770357572779513 38732378255827768179584635)
          ·
            refine ⟨58098567383741652269376953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38732378255827768179584635 58098567383741652269376953)
            ·
              refine ⟨43573925537806239202032715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58098567383741652269376953 43573925537806239202032715)
              ·
                refine ⟨65360888306709358803049073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43573925537806239202032715 65360888306709358803049073)
                ·
                  refine ⟨49020666230032019102286805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65360888306709358803049073 49020666230032019102286805)
                  ·
                    refine ⟨1148921864766375447709847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49020666230032019102286805 1148921864766375447709847)
                    ·
                      rfl

theorem cell23_6712552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_6712552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712552 prefixEnd_6712552 := by exact prefixLift 6712552
  have htrace : WordTrace (prefixWord ++ tailWord_6712552) baseStart_6712552 baseEnd_6712552 := by
    simpa [prefixWord, tailWord_6712552, baseEnd_6712552] using wordTrace_append hprefix tailTrace_6712552
  have hstable : (prefixWord ++ tailWord_6712552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712552).length < 2 ^ (prefixWord ++ tailWord_6712552).sum := by decide
  have hdescent : baseEnd_6712552 < baseStart_6712552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712593 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 1, 3, 2]
def baseStart_6712593 : Nat := 118140960795 + 6712593 * 2 ^ 59
def prefixEnd_6712593 : Nat := 4983230072969 + 3 ^ 40 * 6712593 * 2
def baseEnd_6712593 : Nat := 3446786647005960682716853

theorem tailTrace_6712593 : CollatzResearch.WordTrace tailWord_6712593 prefixEnd_6712593 3446786647005960682716853 := by
  unfold tailWord_6712593
  simp only [CollatzResearch.WordTrace]
  refine ⟨244828380170429455458382433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163218920113619636972254955 244828380170429455458382433)
  ·
    refine ⟨183621285127822091593786825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244828380170429455458382433 183621285127822091593786825)
    ·
      refine ⟨137715963845866568695340119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183621285127822091593786825 137715963845866568695340119)
      ·
        refine ⟨206573945768799853043010179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137715963845866568695340119 206573945768799853043010179)
        ·
          refine ⟨309860918653199779564515269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206573945768799853043010179 309860918653199779564515269)
          ·
            refine ⟨58098922247474958668346613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309860918653199779564515269 58098922247474958668346613)
            ·
              refine ⟨5446773960700777375157495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58098922247474958668346613 5446773960700777375157495)
              ·
                refine ⟨8170160941051166062736243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5446773960700777375157495 8170160941051166062736243)
                ·
                  refine ⟨12255241411576749094104365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8170160941051166062736243 12255241411576749094104365)
                  ·
                    refine ⟨4595715529341280910289137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12255241411576749094104365 4595715529341280910289137)
                    ·
                      refine ⟨3446786647005960682716853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4595715529341280910289137 3446786647005960682716853)
                      ·
                        rfl

theorem cell23_6712593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_6712593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712593 prefixEnd_6712593 := by exact prefixLift 6712593
  have htrace : WordTrace (prefixWord ++ tailWord_6712593) baseStart_6712593 baseEnd_6712593 := by
    simpa [prefixWord, tailWord_6712593, baseEnd_6712593] using wordTrace_append hprefix tailTrace_6712593
  have hstable : (prefixWord ++ tailWord_6712593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712593).length < 2 ^ (prefixWord ++ tailWord_6712593).sum := by decide
  have hdescent : baseEnd_6712593 < baseStart_6712593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712629 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 7]
def baseStart_6712629 : Nat := 118140960795 + 6712629 * 2 ^ 59
def prefixEnd_6712629 : Nat := 4983230072969 + 3 ^ 40 * 6712629 * 2
def baseEnd_6712629 : Nat := 382978348034391393540743

theorem tailTrace_6712629 : CollatzResearch.WordTrace tailWord_6712629 prefixEnd_6712629 382978348034391393540743 := by
  unfold tailWord_6712629
  simp only [CollatzResearch.WordTrace]
  refine ⟨244829693198299033606692941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163219795465532689071128627 244829693198299033606692941)
  ·
    refine ⟨91811134949362137602509853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244829693198299033606692941 91811134949362137602509853)
    ·
      refine ⟨34429175606010801600941195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91811134949362137602509853 34429175606010801600941195)
      ·
        refine ⟨51643763409016202401411793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34429175606010801600941195 51643763409016202401411793)
        ·
          refine ⟨38732822556762151801058845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51643763409016202401411793 38732822556762151801058845)
          ·
            refine ⟨14524808458785806925397067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38732822556762151801058845 14524808458785806925397067)
            ·
              refine ⟨21787212688178710388095601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14524808458785806925397067 21787212688178710388095601)
              ·
                refine ⟨16340409516134032791071701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21787212688178710388095601 16340409516134032791071701)
                ·
                  refine ⟨382978348034391393540743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16340409516134032791071701 382978348034391393540743)
                  ·
                    rfl

theorem cell23_6712629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_6712629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712629 prefixEnd_6712629 := by exact prefixLift 6712629
  have htrace : WordTrace (prefixWord ++ tailWord_6712629) baseStart_6712629 baseEnd_6712629 := by
    simpa [prefixWord, tailWord_6712629, baseEnd_6712629] using wordTrace_append hprefix tailTrace_6712629
  have hstable : (prefixWord ++ tailWord_6712629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712629).length < 2 ^ (prefixWord ++ tailWord_6712629).sum := by decide
  have hdescent : baseEnd_6712629 < baseStart_6712629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712699 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 3]
def baseStart_6712699 : Nat := 118140960795 + 6712699 * 2 ^ 59
def prefixEnd_6712699 : Nat := 4983230072969 + 3 ^ 40 * 6712699 * 2
def baseEnd_6712699 : Nat := 3446841075955337267991365

theorem tailTrace_6712699 : CollatzResearch.WordTrace tailWord_6712699 prefixEnd_6712699 3446841075955337267991365 := by
  unfold tailWord_6712699
  simp only [CollatzResearch.WordTrace]
  refine ⟨244832246308045435561741151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163221497538696957041160767 244832246308045435561741151)
  ·
    refine ⟨367248369462068153342611727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244832246308045435561741151 367248369462068153342611727)
    ·
      refine ⟨550872554193102230013917591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367248369462068153342611727 550872554193102230013917591)
      ·
        refine ⟨826308831289653345020876387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550872554193102230013917591 826308831289653345020876387)
        ·
          refine ⟨1239463246934480017531314581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826308831289653345020876387 1239463246934480017531314581)
          ·
            refine ⟨58099839700053750821780371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1239463246934480017531314581 58099839700053750821780371)
            ·
              refine ⟨87149759550080626232670557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58099839700053750821780371 87149759550080626232670557)
              ·
                refine ⟨32681159831280234837251459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87149759550080626232670557 32681159831280234837251459)
                ·
                  refine ⟨49021739746920352255877189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32681159831280234837251459 49021739746920352255877189)
                  ·
                    refine ⟨9191576202547566047976973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49021739746920352255877189 9191576202547566047976973)
                    ·
                      refine ⟨3446841075955337267991365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9191576202547566047976973 3446841075955337267991365)
                      ·
                        rfl

theorem cell23_6712699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 3].length) (baseStart_6712699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712699 prefixEnd_6712699 := by exact prefixLift 6712699
  have htrace : WordTrace (prefixWord ++ tailWord_6712699) baseStart_6712699 baseEnd_6712699 := by
    simpa [prefixWord, tailWord_6712699, baseEnd_6712699] using wordTrace_append hprefix tailTrace_6712699
  have hstable : (prefixWord ++ tailWord_6712699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712699).length < 2 ^ (prefixWord ++ tailWord_6712699).sum := by decide
  have hdescent : baseEnd_6712699 < baseStart_6712699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712716 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_6712716 : Nat := 118140960795 + 6712716 * 2 ^ 59
def prefixEnd_6712716 : Nat := 4983230072969 + 3 ^ 40 * 6712716 * 2
def baseEnd_6712716 : Nat := 3446849805126463701478787

theorem tailTrace_6712716 : CollatzResearch.WordTrace tailWord_6712716 prefixEnd_6712716 3446849805126463701478787 := by
  unfold tailWord_6712716
  simp only [CollatzResearch.WordTrace]
  refine ⟨122416433174491923732555001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163221910899322564976740001 122416433174491923732555001)
  ·
    refine ⟨91812324880868942799416251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122416433174491923732555001 91812324880868942799416251)
    ·
      refine ⟨137718487321303414199124377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91812324880868942799416251 137718487321303414199124377)
      ·
        refine ⟨103288865490977560649343283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137718487321303414199124377 103288865490977560649343283)
        ·
          refine ⟨154933298236466340974014925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103288865490977560649343283 154933298236466340974014925)
          ·
            refine ⟨58099986838674877865255597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154933298236466340974014925 58099986838674877865255597)
            ·
              refine ⟨21787495064503079199470849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58099986838674877865255597 21787495064503079199470849)
              ·
                refine ⟨16340621298377309399603137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21787495064503079199470849 16340621298377309399603137)
                ·
                  refine ⟨12255465973782982049702353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16340621298377309399603137 12255465973782982049702353)
                  ·
                    refine ⟨9191599480337236537276765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12255465973782982049702353 9191599480337236537276765)
                    ·
                      refine ⟨3446849805126463701478787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9191599480337236537276765 3446849805126463701478787)
                      ·
                        rfl

theorem cell23_6712716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_6712716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712716 prefixEnd_6712716 := by exact prefixLift 6712716
  have htrace : WordTrace (prefixWord ++ tailWord_6712716) baseStart_6712716 baseEnd_6712716 := by
    simpa [prefixWord, tailWord_6712716, baseEnd_6712716] using wordTrace_append hprefix tailTrace_6712716
  have hstable : (prefixWord ++ tailWord_6712716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712716).length < 2 ^ (prefixWord ++ tailWord_6712716).sum := by decide
  have hdescent : baseEnd_6712716 < baseStart_6712716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712816 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_6712816 : Nat := 118140960795 + 6712816 * 2 ^ 59
def prefixEnd_6712816 : Nat := 4983230072969 + 3 ^ 40 * 6712816 * 2
def baseEnd_6712816 : Nat := 3446901153191913310228327

theorem tailTrace_6712816 : CollatzResearch.WordTrace tailWord_6712816 prefixEnd_6712816 3446901153191913310228327 := by
  unfold tailWord_6712816
  simp only [CollatzResearch.WordTrace]
  refine ⟨122418256824310782271875151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163224342432414376362500201 122418256824310782271875151)
  ·
    refine ⟨183627385236466173407812727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122418256824310782271875151 183627385236466173407812727)
    ·
      refine ⟨275441077854699260111719091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183627385236466173407812727 275441077854699260111719091)
      ·
        refine ⟨413161616782048890167578637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275441077854699260111719091 413161616782048890167578637)
        ·
          refine ⟨154935606293268333812841989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413161616782048890167578637 154935606293268333812841989)
          ·
            refine ⟨29050426179987812589907873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154935606293268333812841989 29050426179987812589907873)
            ·
              refine ⟨21787819634990859442430905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29050426179987812589907873 21787819634990859442430905)
              ·
                refine ⟨16340864726243144581823179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21787819634990859442430905 16340864726243144581823179)
                ·
                  refine ⟨24511297089364716872734769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16340864726243144581823179 24511297089364716872734769)
                  ·
                    refine ⟨18383472817023537654551077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24511297089364716872734769 18383472817023537654551077)
                    ·
                      refine ⟨3446901153191913310228327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18383472817023537654551077 3446901153191913310228327)
                      ·
                        rfl

theorem cell23_6712816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_6712816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712816 prefixEnd_6712816 := by exact prefixLift 6712816
  have htrace : WordTrace (prefixWord ++ tailWord_6712816) baseStart_6712816 baseEnd_6712816 := by
    simpa [prefixWord, tailWord_6712816, baseEnd_6712816] using wordTrace_append hprefix tailTrace_6712816
  have hstable : (prefixWord ++ tailWord_6712816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712816).length < 2 ^ (prefixWord ++ tailWord_6712816).sum := by decide
  have hdescent : baseEnd_6712816 < baseStart_6712816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712853 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_6712853 : Nat := 118140960795 + 6712853 * 2 ^ 59
def prefixEnd_6712853 : Nat := 4983230072969 + 3 ^ 40 * 6712853 * 2
def baseEnd_6712853 : Nat := 3446920151976129665465657

theorem tailTrace_6712853 : CollatzResearch.WordTrace tailWord_6712853 prefixEnd_6712853 3446920151976129665465657 := by
  unfold tailWord_6712853
  simp only [CollatzResearch.WordTrace]
  refine ⟨244837863149487519862847213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163225242099658346575231475 244837863149487519862847213)
  ·
    refine ⟨91814198681057819948567705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244837863149487519862847213 91814198681057819948567705)
    ·
      refine ⟨68860649010793364961425779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91814198681057819948567705 68860649010793364961425779)
      ·
        refine ⟨103290973516190047442138669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68860649010793364961425779 103290973516190047442138669)
        ·
          refine ⟨38734115068571267790802001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103290973516190047442138669 38734115068571267790802001)
          ·
            refine ⟨29050586301428450843101501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38734115068571267790802001 29050586301428450843101501)
            ·
              refine ⟨10893969863035669066163063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29050586301428450843101501 10893969863035669066163063)
              ·
                refine ⟨16340954794553503599244595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10893969863035669066163063 16340954794553503599244595)
                ·
                  refine ⟨24511432191830255398866893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16340954794553503599244595 24511432191830255398866893)
                  ·
                    refine ⟨9191787071936345774575085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24511432191830255398866893 9191787071936345774575085)
                    ·
                      refine ⟨3446920151976129665465657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9191787071936345774575085 3446920151976129665465657)
                      ·
                        rfl

theorem cell23_6712853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_6712853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712853 prefixEnd_6712853 := by exact prefixLift 6712853
  have htrace : WordTrace (prefixWord ++ tailWord_6712853) baseStart_6712853 baseEnd_6712853 := by
    simpa [prefixWord, tailWord_6712853, baseEnd_6712853] using wordTrace_append hprefix tailTrace_6712853
  have hstable : (prefixWord ++ tailWord_6712853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712853).length < 2 ^ (prefixWord ++ tailWord_6712853).sum := by decide
  have hdescent : baseEnd_6712853 < baseStart_6712853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712863 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 3, 3, 2]
def baseStart_6712863 : Nat := 118140960795 + 6712863 * 2 ^ 59
def prefixEnd_6712863 : Nat := 4983230072969 + 3 ^ 40 * 6712863 * 2
def baseEnd_6712863 : Nat := 3446925286782674626340611

theorem tailTrace_6712863 : CollatzResearch.WordTrace tailWord_6712863 prefixEnd_6712863 3446925286782674626340611 := by
  unfold tailWord_6712863
  simp only [CollatzResearch.WordTrace]
  refine ⟨244838227879451291570711243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163225485252967527713807495 244838227879451291570711243)
  ·
    refine ⟨367257341819176937356066865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244838227879451291570711243 367257341819176937356066865)
    ·
      refine ⟨275443006364382703017050149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367257341819176937356066865 275443006364382703017050149)
      ·
        refine ⟨51645563693321756815696903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275443006364382703017050149 51645563693321756815696903)
        ·
          refine ⟨77468345539982635223545355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51645563693321756815696903 77468345539982635223545355)
          ·
            refine ⟨116202518309973952835318033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77468345539982635223545355 116202518309973952835318033)
            ·
              refine ⟨87151888732480464626488525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116202518309973952835318033 87151888732480464626488525)
              ·
                refine ⟨32681958274680174234933197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87151888732480464626488525 32681958274680174234933197)
                ·
                  refine ⟨12255734353005065338099949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32681958274680174234933197 12255734353005065338099949)
                  ·
                    refine ⟨4595900382376899501787481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12255734353005065338099949 4595900382376899501787481)
                    ·
                      refine ⟨3446925286782674626340611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4595900382376899501787481 3446925286782674626340611)
                      ·
                        rfl

theorem cell23_6712863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_6712863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712863 prefixEnd_6712863 := by exact prefixLift 6712863
  have htrace : WordTrace (prefixWord ++ tailWord_6712863) baseStart_6712863 baseEnd_6712863 := by
    simpa [prefixWord, tailWord_6712863, baseEnd_6712863] using wordTrace_append hprefix tailTrace_6712863
  have hstable : (prefixWord ++ tailWord_6712863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712863).length < 2 ^ (prefixWord ++ tailWord_6712863).sum := by decide
  have hdescent : baseEnd_6712863 < baseStart_6712863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712866 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_6712866 : Nat := 118140960795 + 6712866 * 2 ^ 59
def prefixEnd_6712866 : Nat := 4983230072969 + 3 ^ 40 * 6712866 * 2
def baseEnd_6712866 : Nat := 3446926827224638114603097

theorem tailTrace_6712866 : CollatzResearch.WordTrace tailWord_6712866 prefixEnd_6712866 3446926827224638114603097 := by
  unfold tailWord_6712866
  simp only [CollatzResearch.WordTrace]
  refine ⟨61209584324610105770767613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163225558198960282055380301 61209584324610105770767613)
  ·
    refine ⟨22953594121728789664037855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61209584324610105770767613 22953594121728789664037855)
    ·
      refine ⟨34430391182593184496056783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22953594121728789664037855 34430391182593184496056783)
      ·
        refine ⟨51645586773889776744085175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34430391182593184496056783 51645586773889776744085175)
        ·
          refine ⟨77468380160834665116127763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51645586773889776744085175 77468380160834665116127763)
          ·
            refine ⟨116202570241251997674191645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77468380160834665116127763 116202570241251997674191645)
            ·
              refine ⟨43575963840469499127821867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116202570241251997674191645 43575963840469499127821867)
              ·
                refine ⟨65363945760704248691732801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43575963840469499127821867 65363945760704248691732801)
                ·
                  refine ⟨49022959320528186518799601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65363945760704248691732801 49022959320528186518799601)
                  ·
                    refine ⟨36767219490396139889099701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49022959320528186518799601 36767219490396139889099701)
                    ·
                      refine ⟨3446926827224638114603097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36767219490396139889099701 3446926827224638114603097)
                      ·
                        rfl

theorem cell23_6712866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_6712866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712866 prefixEnd_6712866 := by exact prefixLift 6712866
  have htrace : WordTrace (prefixWord ++ tailWord_6712866) baseStart_6712866 baseEnd_6712866 := by
    simpa [prefixWord, tailWord_6712866, baseEnd_6712866] using wordTrace_append hprefix tailTrace_6712866
  have hstable : (prefixWord ++ tailWord_6712866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712866).length < 2 ^ (prefixWord ++ tailWord_6712866).sum := by decide
  have hdescent : baseEnd_6712866 < baseStart_6712866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712896 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 3]
def baseStart_6712896 : Nat := 118140960795 + 6712896 * 2 ^ 59
def prefixEnd_6712896 : Nat := 4983230072969 + 3 ^ 40 * 6712896 * 2
def baseEnd_6712896 : Nat := 3446942231644272997227959

theorem tailTrace_6712896 : CollatzResearch.WordTrace tailWord_6712896 prefixEnd_6712896 3446942231644272997227959 := by
  unfold tailWord_6712896
  simp only [CollatzResearch.WordTrace]
  refine ⟨122419715744165869103331271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163226287658887825471108361 122419715744165869103331271)
  ·
    refine ⟨183629573616248803654996907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122419715744165869103331271 183629573616248803654996907)
    ·
      refine ⟨275444360424373205482495361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183629573616248803654996907 275444360424373205482495361)
      ·
        refine ⟨206583270318279904111871521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275444360424373205482495361 206583270318279904111871521)
        ·
          refine ⟨154937452738709928083903641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206583270318279904111871521 154937452738709928083903641)
          ·
            refine ⟨116203089554032446062927731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154937452738709928083903641 116203089554032446062927731)
            ·
              refine ⟨174304634331048669094391597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116203089554032446062927731 174304634331048669094391597)
              ·
                refine ⟨65364237874143250910396849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174304634331048669094391597 65364237874143250910396849)
                ·
                  refine ⟨49023178405607438182797637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65364237874143250910396849 49023178405607438182797637)
                  ·
                    refine ⟨9191845951051394659274557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49023178405607438182797637 9191845951051394659274557)
                    ·
                      refine ⟨3446942231644272997227959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9191845951051394659274557 3446942231644272997227959)
                      ·
                        rfl

theorem cell23_6712896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_6712896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712896 prefixEnd_6712896 := by exact prefixLift 6712896
  have htrace : WordTrace (prefixWord ++ tailWord_6712896) baseStart_6712896 baseEnd_6712896 := by
    simpa [prefixWord, tailWord_6712896, baseEnd_6712896] using wordTrace_append hprefix tailTrace_6712896
  have hstable : (prefixWord ++ tailWord_6712896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712896).length < 2 ^ (prefixWord ++ tailWord_6712896).sum := by decide
  have hdescent : baseEnd_6712896 < baseStart_6712896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712906 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_6712906 : Nat := 118140960795 + 6712906 * 2 ^ 59
def prefixEnd_6712906 : Nat := 4983230072969 + 3 ^ 40 * 6712906 * 2
def baseEnd_6712906 : Nat := 3446947366450817958102913

theorem tailTrace_6712906 : CollatzResearch.WordTrace tailWord_6712906 prefixEnd_6712906 3446947366450817958102913 := by
  unfold tailWord_6712906
  simp only [CollatzResearch.WordTrace]
  refine ⟨61209949054573877478631643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163226530812197006609684381 61209949054573877478631643)
  ·
    refine ⟨91814923581860816217947465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61209949054573877478631643 91814923581860816217947465)
    ·
      refine ⟨68861192686395612163460599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91814923581860816217947465 68861192686395612163460599)
      ·
        refine ⟨103291789029593418245190899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68861192686395612163460599 103291789029593418245190899)
        ·
          refine ⟨154937683544390127367786349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103291789029593418245190899 154937683544390127367786349)
          ·
            refine ⟨58101631329146297762919881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154937683544390127367786349 58101631329146297762919881)
            ·
              refine ⟨43576223496859723322189911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58101631329146297762919881 43576223496859723322189911)
              ·
                refine ⟨65364335245289584983284867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43576223496859723322189911 65364335245289584983284867)
                ·
                  refine ⟨98046502867934377474927301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65364335245289584983284867 98046502867934377474927301)
                  ·
                    refine ⟨18383719287737695776548869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98046502867934377474927301 18383719287737695776548869)
                    ·
                      refine ⟨3446947366450817958102913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18383719287737695776548869 3446947366450817958102913)
                      ·
                        rfl

theorem cell23_6712906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_6712906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712906 prefixEnd_6712906 := by exact prefixLift 6712906
  have htrace : WordTrace (prefixWord ++ tailWord_6712906) baseStart_6712906 baseEnd_6712906 := by
    simpa [prefixWord, tailWord_6712906, baseEnd_6712906] using wordTrace_append hprefix tailTrace_6712906
  have hstable : (prefixWord ++ tailWord_6712906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712906).length < 2 ^ (prefixWord ++ tailWord_6712906).sum := by decide
  have hdescent : baseEnd_6712906 < baseStart_6712906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712916 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 9]
def baseStart_6712916 : Nat := 118140960795 + 6712916 * 2 ^ 59
def prefixEnd_6712916 : Nat := 4983230072969 + 3 ^ 40 * 6712916 * 2
def baseEnd_6712916 : Nat := 382994722361929213219763

theorem tailTrace_6712916 : CollatzResearch.WordTrace tailWord_6712916 prefixEnd_6712916 382994722361929213219763 := by
  unfold tailWord_6712916
  simp only [CollatzResearch.WordTrace]
  refine ⟨122420080474129640811195301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163226773965506187748260401 122420080474129640811195301)
  ·
    refine ⟨22953765088899307652099119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122420080474129640811195301 22953765088899307652099119)
    ·
      refine ⟨34430647633348961478148679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22953765088899307652099119 34430647633348961478148679)
      ·
        refine ⟨51645971450023442217223019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34430647633348961478148679 51645971450023442217223019)
        ·
          refine ⟨77468957175035163325834529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51645971450023442217223019 77468957175035163325834529)
          ·
            refine ⟨58101717881276372494375897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77468957175035163325834529 58101717881276372494375897)
            ·
              refine ⟨43576288410957279370781923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58101717881276372494375897 43576288410957279370781923)
              ·
                refine ⟨65364432616435919056172885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43576288410957279370781923 65364432616435919056172885)
                ·
                  refine ⟨382994722361929213219763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65364432616435919056172885 382994722361929213219763)
                  ·
                    rfl

theorem cell23_6712916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_6712916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712916 prefixEnd_6712916 := by exact prefixLift 6712916
  have htrace : WordTrace (prefixWord ++ tailWord_6712916) baseStart_6712916 baseEnd_6712916 := by
    simpa [prefixWord, tailWord_6712916, baseEnd_6712916] using wordTrace_append hprefix tailTrace_6712916
  have hstable : (prefixWord ++ tailWord_6712916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712916).length < 2 ^ (prefixWord ++ tailWord_6712916).sum := by decide
  have hdescent : baseEnd_6712916 < baseStart_6712916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712953 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 1, 7, 2]
def baseStart_6712953 : Nat := 118140960795 + 6712953 * 2 ^ 59
def prefixEnd_6712953 : Nat := 4983230072969 + 3 ^ 40 * 6712953 * 2
def baseEnd_6712953 : Nat := 3446971500041579274215197

theorem tailTrace_6712953 : CollatzResearch.WordTrace tailWord_6712953 prefixEnd_6712953 3446971500041579274215197 := by
  unfold tailWord_6712953
  simp only [CollatzResearch.WordTrace]
  refine ⟨244841510449125236941487513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163227673632750157960991675 244841510449125236941487513)
  ·
    refine ⟨183631132836843927706115635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244841510449125236941487513 183631132836843927706115635)
    ·
      refine ⟨275446699255265891559173453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183631132836843927706115635 275446699255265891559173453)
      ·
        refine ⟨103292512220724709334690045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275446699255265891559173453 103292512220724709334690045)
        ·
          refine ⟨38734692082771766000508767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103292512220724709334690045 38734692082771766000508767)
          ·
            refine ⟨58102038124157649000763151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38734692082771766000508767 58102038124157649000763151)
            ·
              refine ⟨87153057186236473501144727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58102038124157649000763151 87153057186236473501144727)
              ·
                refine ⟨130729585779354710251717091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87153057186236473501144727 130729585779354710251717091)
                ·
                  refine ⟨196094378669032065377575637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130729585779354710251717091 196094378669032065377575637)
                  ·
                    refine ⟨4595962000055439032286929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 196094378669032065377575637 4595962000055439032286929)
                    ·
                      refine ⟨3446971500041579274215197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4595962000055439032286929 3446971500041579274215197)
                      ·
                        rfl

theorem cell23_6712953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_6712953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712953 prefixEnd_6712953 := by exact prefixLift 6712953
  have htrace : WordTrace (prefixWord ++ tailWord_6712953) baseStart_6712953 baseEnd_6712953 := by
    simpa [prefixWord, tailWord_6712953, baseEnd_6712953] using wordTrace_append hprefix tailTrace_6712953
  have hstable : (prefixWord ++ tailWord_6712953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712953).length < 2 ^ (prefixWord ++ tailWord_6712953).sum := by decide
  have hdescent : baseEnd_6712953 < baseStart_6712953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712980 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_6712980 : Nat := 118140960795 + 6712980 * 2 ^ 59
def prefixEnd_6712980 : Nat := 4983230072969 + 3 ^ 40 * 6712980 * 2
def baseEnd_6712980 : Nat := 1148995121339750222859191

theorem tailTrace_6712980 : CollatzResearch.WordTrace tailWord_6712980 prefixEnd_6712980 1148995121339750222859191 := by
  unfold tailWord_6712980
  simp only [CollatzResearch.WordTrace]
  refine ⟨122421247610013710276360197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163228330146684947035146929 122421247610013710276360197)
  ·
    refine ⟨22953983926877570676817537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122421247610013710276360197 22953983926877570676817537)
    ·
      refine ⟨17215487945158178007613153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22953983926877570676817537 17215487945158178007613153)
      ·
        refine ⟨12911615958868633505709865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17215487945158178007613153 12911615958868633505709865)
        ·
          refine ⟨9683711969151475129282399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12911615958868633505709865 9683711969151475129282399)
          ·
            refine ⟨14525567953727212693923599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9683711969151475129282399 14525567953727212693923599)
            ·
              refine ⟨21788351930590819040885399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14525567953727212693923599 21788351930590819040885399)
              ·
                refine ⟨32682527895886228561328099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21788351930590819040885399 32682527895886228561328099)
                ·
                  refine ⟨49023791843829342841992149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32682527895886228561328099 49023791843829342841992149)
                  ·
                    refine ⟨1148995121339750222859191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49023791843829342841992149 1148995121339750222859191)
                    ·
                      rfl

theorem cell23_6712980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_6712980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712980 prefixEnd_6712980 := by exact prefixLift 6712980
  have htrace : WordTrace (prefixWord ++ tailWord_6712980) baseStart_6712980 baseEnd_6712980 := by
    simpa [prefixWord, tailWord_6712980, baseEnd_6712980] using wordTrace_append hprefix tailTrace_6712980
  have hstable : (prefixWord ++ tailWord_6712980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712980).length < 2 ^ (prefixWord ++ tailWord_6712980).sum := by decide
  have hdescent : baseEnd_6712980 < baseStart_6712980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6712983 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_6712983 : Nat := 118140960795 + 6712983 * 2 ^ 59
def prefixEnd_6712983 : Nat := 4983230072969 + 3 ^ 40 * 6712983 * 2
def baseEnd_6712983 : Nat := 3446986904461214156840059

theorem tailTrace_6712983 : CollatzResearch.WordTrace tailWord_6712983 prefixEnd_6712983 3446986904461214156840059 := by
  unfold tailWord_6712983
  simp only [CollatzResearch.WordTrace]
  refine ⟨244842604639016552065079603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163228403092677701376719735 244842604639016552065079603)
  ·
    refine ⟨367263906958524828097619405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244842604639016552065079603 367263906958524828097619405)
    ·
      refine ⟨137723965109446810536607277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367263906958524828097619405 137723965109446810536607277)
      ·
        refine ⟨51646486916042553951227729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137723965109446810536607277 51646486916042553951227729)
        ·
          refine ⟨38734865187031915463420797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51646486916042553951227729 38734865187031915463420797)
          ·
            refine ⟨14525574445136968298782799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38734865187031915463420797 14525574445136968298782799)
            ·
              refine ⟨21788361667705452448174199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14525574445136968298782799 21788361667705452448174199)
              ·
                refine ⟨32682542501558178672261299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21788361667705452448174199 32682542501558178672261299)
                ·
                  refine ⟨49023813752337268008391949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32682542501558178672261299 49023813752337268008391949)
                  ·
                    refine ⟨18383930157126475503146981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49023813752337268008391949 18383930157126475503146981)
                    ·
                      refine ⟨3446986904461214156840059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18383930157126475503146981 3446986904461214156840059)
                      ·
                        rfl

theorem cell23_6712983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_6712983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6712983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6712983 prefixEnd_6712983 := by exact prefixLift 6712983
  have htrace : WordTrace (prefixWord ++ tailWord_6712983) baseStart_6712983 baseEnd_6712983 := by
    simpa [prefixWord, tailWord_6712983, baseEnd_6712983] using wordTrace_append hprefix tailTrace_6712983
  have hstable : (prefixWord ++ tailWord_6712983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6712983).length < 2 ^ (prefixWord ++ tailWord_6712983).sum := by decide
  have hdescent : baseEnd_6712983 < baseStart_6712983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6712983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713037 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_6713037 : Nat := 118140960795 + 6713037 * 2 ^ 59
def prefixEnd_6713037 : Nat := 4983230072969 + 3 ^ 40 * 6713037 * 2
def baseEnd_6713037 : Nat := 3447014632416556945564811

theorem tailTrace_6713037 : CollatzResearch.WordTrace tailWord_6713037 prefixEnd_6713037 3447014632416556945564811 := by
  unfold tailWord_6713037
  simp only [CollatzResearch.WordTrace]
  refine ⟨244844574180820919287545365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163229716120547279525030243 244844574180820919287545365)
  ·
    refine ⟨11477089414725980591603689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 244844574180820919287545365 11477089414725980591603689)
    ·
      refine ⟨8607817061044485443702767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11477089414725980591603689 8607817061044485443702767)
      ·
        refine ⟨12911725591566728165554151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8607817061044485443702767 12911725591566728165554151)
        ·
          refine ⟨19367588387350092248331227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12911725591566728165554151 19367588387350092248331227)
          ·
            refine ⟨29051382581025138372496841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19367588387350092248331227 29051382581025138372496841)
            ·
              refine ⟨21788536935768853779372631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29051382581025138372496841 21788536935768853779372631)
              ·
                refine ⟨32682805403653280669058947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21788536935768853779372631 32682805403653280669058947)
                ·
                  refine ⟨49024208105479921003588421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32682805403653280669058947 49024208105479921003588421)
                  ·
                    refine ⟨9192039019777485188172829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49024208105479921003588421 9192039019777485188172829)
                    ·
                      refine ⟨3447014632416556945564811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9192039019777485188172829 3447014632416556945564811)
                      ·
                        rfl

theorem cell23_6713037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_6713037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713037 prefixEnd_6713037 := by exact prefixLift 6713037
  have htrace : WordTrace (prefixWord ++ tailWord_6713037) baseStart_6713037 baseEnd_6713037 := by
    simpa [prefixWord, tailWord_6713037, baseEnd_6713037] using wordTrace_append hprefix tailTrace_6713037
  have hstable : (prefixWord ++ tailWord_6713037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713037).length < 2 ^ (prefixWord ++ tailWord_6713037).sum := by decide
  have hdescent : baseEnd_6713037 < baseStart_6713037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713044 : List Nat := [2, 4, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_6713044 : Nat := 118140960795 + 6713044 * 2 ^ 59
def prefixEnd_6713044 : Nat := 4983230072969 + 3 ^ 40 * 6713044 * 2
def baseEnd_6713044 : Nat := 1149006075593712806059093

theorem tailTrace_6713044 : CollatzResearch.WordTrace tailWord_6713044 prefixEnd_6713044 1149006075593712806059093 := by
  unfold tailWord_6713044
  simp only [CollatzResearch.WordTrace]
  refine ⟨122422414745897779741525093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163229886327863706322033457 122422414745897779741525093)
  ·
    refine ⟨22954202764855833701535955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122422414745897779741525093 22954202764855833701535955)
    ·
      refine ⟨34431304147283750552303933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22954202764855833701535955 34431304147283750552303933)
      ·
        refine ⟨12911739055231406457113975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34431304147283750552303933 12911739055231406457113975)
        ·
          refine ⟨19367608582847109685670963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12911739055231406457113975 19367608582847109685670963)
          ·
            refine ⟨29051412874270664528506445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19367608582847109685670963 29051412874270664528506445)
            ·
              refine ⟨10894279827851499198189917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29051412874270664528506445 10894279827851499198189917)
              ·
                refine ⟨4085354935444312199321219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10894279827851499198189917 4085354935444312199321219)
                ·
                  refine ⟨6128032403166468298981829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085354935444312199321219 6128032403166468298981829)
                  ·
                    refine ⟨1149006075593712806059093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6128032403166468298981829 1149006075593712806059093)
                    ·
                      rfl

theorem cell23_6713044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_6713044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713044 prefixEnd_6713044 := by exact prefixLift 6713044
  have htrace : WordTrace (prefixWord ++ tailWord_6713044) baseStart_6713044 baseEnd_6713044 := by
    simpa [prefixWord, tailWord_6713044, baseEnd_6713044] using wordTrace_append hprefix tailTrace_6713044
  have hstable : (prefixWord ++ tailWord_6713044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713044).length < 2 ^ (prefixWord ++ tailWord_6713044).sum := by decide
  have hdescent : baseEnd_6713044 < baseStart_6713044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713067 : List Nat := [1, 1, 1, 1, 2, 4, 2, 6, 1, 1, 3]
def baseStart_6713067 : Nat := 118140960795 + 6713067 * 2 ^ 59
def prefixEnd_6713067 : Nat := 4983230072969 + 3 ^ 40 * 6713067 * 2
def baseEnd_6713067 : Nat := 3447030036836191828189673

theorem tailTrace_6713067 : CollatzResearch.WordTrace tailWord_6713067 prefixEnd_6713067 3447030036836191828189673 := by
  unfold tailWord_6713067
  simp only [CollatzResearch.WordTrace]
  refine ⟨244845668370712234411137455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163230445580474822940758303 244845668370712234411137455)
  ·
    refine ⟨367268502556068351616706183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244845668370712234411137455 367268502556068351616706183)
    ·
      refine ⟨550902753834102527425059275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367268502556068351616706183 550902753834102527425059275)
      ·
        refine ⟨826354130751153791137588913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550902753834102527425059275 826354130751153791137588913)
        ·
          refine ⟨619765598063365343353191685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826354130751153791137588913 619765598063365343353191685)
          ·
            refine ⟨116206049636881001878723441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 619765598063365343353191685 116206049636881001878723441)
            ·
              refine ⟨87154537227660751409042581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116206049636881001878723441 87154537227660751409042581)
              ·
                refine ⟨4085368932546597722298871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87154537227660751409042581 4085368932546597722298871)
                ·
                  refine ⟨6128053398819896583448307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085368932546597722298871 6128053398819896583448307)
                  ·
                    refine ⟨9192080098229844875172461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6128053398819896583448307 9192080098229844875172461)
                    ·
                      refine ⟨3447030036836191828189673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9192080098229844875172461 3447030036836191828189673)
                      ·
                        rfl

theorem cell23_6713067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 1, 3].length) (baseStart_6713067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713067 prefixEnd_6713067 := by exact prefixLift 6713067
  have htrace : WordTrace (prefixWord ++ tailWord_6713067) baseStart_6713067 baseEnd_6713067 := by
    simpa [prefixWord, tailWord_6713067, baseEnd_6713067] using wordTrace_append hprefix tailTrace_6713067
  have hstable : (prefixWord ++ tailWord_6713067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713067).length < 2 ^ (prefixWord ++ tailWord_6713067).sum := by decide
  have hdescent : baseEnd_6713067 < baseStart_6713067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713083 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 6, 4]
def baseStart_6713083 : Nat := 118140960795 + 6713083 * 2 ^ 59
def prefixEnd_6713083 : Nat := 4983230072969 + 3 ^ 40 * 6713083 * 2
def baseEnd_6713083 : Nat := 1149012750842221255196533

theorem tailTrace_6713083 : CollatzResearch.WordTrace tailWord_6713083 prefixEnd_6713083 1149012750842221255196533 := by
  unfold tailWord_6713083
  simp only [CollatzResearch.WordTrace]
  refine ⟨244846251938654269143719903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163230834625769512762479935 244846251938654269143719903)
  ·
    refine ⟨367269377907981403715579855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244846251938654269143719903 367269377907981403715579855)
    ·
      refine ⟨550904066861972105573369783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367269377907981403715579855 550904066861972105573369783)
      ·
        refine ⟨826356100292958158360054675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550904066861972105573369783 826356100292958158360054675)
        ·
          refine ⟨1239534150439437237540082013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826356100292958158360054675 1239534150439437237540082013)
          ·
            refine ⟨464825306414788964077530755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1239534150439437237540082013 464825306414788964077530755)
            ·
              refine ⟨697237959622183446116296133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464825306414788964077530755 697237959622183446116296133)
              ·
                refine ⟨130732117429159396146805525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697237959622183446116296133 130732117429159396146805525)
                ·
                  refine ⟨6128068004491846694381509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130732117429159396146805525 6128068004491846694381509)
                  ·
                    refine ⟨1149012750842221255196533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6128068004491846694381509 1149012750842221255196533)
                    ·
                      rfl

theorem cell23_6713083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 4].length) (baseStart_6713083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713083 prefixEnd_6713083 := by exact prefixLift 6713083
  have htrace : WordTrace (prefixWord ++ tailWord_6713083) baseStart_6713083 baseEnd_6713083 := by
    simpa [prefixWord, tailWord_6713083, baseEnd_6713083] using wordTrace_append hprefix tailTrace_6713083
  have hstable : (prefixWord ++ tailWord_6713083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713083).length < 2 ^ (prefixWord ++ tailWord_6713083).sum := by decide
  have hdescent : baseEnd_6713083 < baseStart_6713083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713158 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6713158 : Nat := 118140960795 + 6713158 * 2 ^ 59
def prefixEnd_6713158 : Nat := 4983230072969 + 3 ^ 40 * 6713158 * 2
def baseEnd_6713158 : Nat := 3447076763575750972151755

theorem tailTrace_6713158 : CollatzResearch.WordTrace tailWord_6713158 prefixEnd_6713158 3447076763575750972151755 := by
  unfold tailWord_6713158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7651530856668204904771879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163232658275588371301800085 7651530856668204904771879)
  ·
    refine ⟨11477296285002307357157819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7651530856668204904771879 11477296285002307357157819)
    ·
      refine ⟨17215944427503461035736729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11477296285002307357157819 17215944427503461035736729)
      ·
        refine ⟨12911958320627595776802547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17215944427503461035736729 12911958320627595776802547)
        ·
          refine ⟨19367937480941393665203821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12911958320627595776802547 19367937480941393665203821)
          ·
            refine ⟨7262976555353022624451433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19367937480941393665203821 7262976555353022624451433)
            ·
              refine ⟨5447232416514766968338575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7262976555353022624451433 5447232416514766968338575)
              ·
                refine ⟨8170848624772150452507863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5447232416514766968338575 8170848624772150452507863)
                ·
                  refine ⟨12256272937158225678761795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8170848624772150452507863 12256272937158225678761795)
                  ·
                    refine ⟨18384409405737338518142693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12256272937158225678761795 18384409405737338518142693)
                    ·
                      refine ⟨3447076763575750972151755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18384409405737338518142693 3447076763575750972151755)
                      ·
                        rfl

theorem cell23_6713158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6713158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713158 prefixEnd_6713158 := by exact prefixLift 6713158
  have htrace : WordTrace (prefixWord ++ tailWord_6713158) baseStart_6713158 baseEnd_6713158 := by
    simpa [prefixWord, tailWord_6713158, baseEnd_6713158] using wordTrace_append hprefix tailTrace_6713158
  have hstable : (prefixWord ++ tailWord_6713158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713158).length < 2 ^ (prefixWord ++ tailWord_6713158).sum := by decide
  have hdescent : baseEnd_6713158 < baseStart_6713158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713287 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_6713287 : Nat := 118140960795 + 6713287 * 2 ^ 59
def prefixEnd_6713287 : Nat := 4983230072969 + 3 ^ 40 * 6713287 * 2
def baseEnd_6713287 : Nat := 3447143002580180967438661

theorem tailTrace_6713287 : CollatzResearch.WordTrace tailWord_6713287 prefixEnd_6713287 3447143002580180967438661 := by
  unfold tailWord_6713287
  simp only [CollatzResearch.WordTrace]
  refine ⟨244853692429915211984146115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163235794953276807989430743 244853692429915211984146115)
  ·
    refine ⟨367280538644872817976219173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244853692429915211984146115 367280538644872817976219173)
    ·
      refine ⟨68865100995913653370541095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367280538644872817976219173 68865100995913653370541095)
      ·
        refine ⟨103297651493870480055811643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68865100995913653370541095 103297651493870480055811643)
        ·
          refine ⟨154946477240805720083717465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103297651493870480055811643 154946477240805720083717465)
          ·
            refine ⟨116209857930604290062788099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154946477240805720083717465 116209857930604290062788099)
            ·
              refine ⟨174314786895906435094182149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116209857930604290062788099 174314786895906435094182149)
              ·
                refine ⟨32684022542982456580159153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174314786895906435094182149 32684022542982456580159153)
                ·
                  refine ⟨24513016907236842435119365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32684022542982456580159153 24513016907236842435119365)
                  ·
                    refine ⟨4596190670106907956584881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24513016907236842435119365 4596190670106907956584881)
                    ·
                      refine ⟨3447143002580180967438661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4596190670106907956584881 3447143002580180967438661)
                      ·
                        rfl

theorem cell23_6713287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_6713287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713287 prefixEnd_6713287 := by exact prefixLift 6713287
  have htrace : WordTrace (prefixWord ++ tailWord_6713287) baseStart_6713287 baseEnd_6713287 := by
    simpa [prefixWord, tailWord_6713287, baseEnd_6713287] using wordTrace_append hprefix tailTrace_6713287
  have hstable : (prefixWord ++ tailWord_6713287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713287).length < 2 ^ (prefixWord ++ tailWord_6713287).sum := by decide
  have hdescent : baseEnd_6713287 < baseStart_6713287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713394 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_6713394 : Nat := 118140960795 + 6713394 * 2 ^ 59
def prefixEnd_6713394 : Nat := 4983230072969 + 3 ^ 40 * 6713394 * 2
def baseEnd_6713394 : Nat := 3447197945010212048800669

theorem tailTrace_6713394 : CollatzResearch.WordTrace tailWord_6713394 prefixEnd_6713394 3447197945010212048800669 := by
  unfold tailWord_6713394
  simp only [CollatzResearch.WordTrace]
  refine ⟨61214398760131892314572809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163238396693685046172194157 61214398760131892314572809)
  ·
    refine ⟨45910799070098919235929607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61214398760131892314572809 45910799070098919235929607)
    ·
      refine ⟨68866198605148378853894411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45910799070098919235929607 68866198605148378853894411)
      ·
        refine ⟨103299297907722568280841617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68866198605148378853894411 103299297907722568280841617)
        ·
          refine ⟨77474473430791926210631213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103299297907722568280841617 77474473430791926210631213)
          ·
            refine ⟨29052927536546972328986705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77474473430791926210631213 29052927536546972328986705)
            ·
              refine ⟨21789695652410229246740029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29052927536546972328986705 21789695652410229246740029)
              ·
                refine ⟨8171135869653835967527511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21789695652410229246740029 8171135869653835967527511)
                ·
                  refine ⟨12256703804480753951291267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8171135869653835967527511 12256703804480753951291267)
                  ·
                    refine ⟨18385055706721130926936901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12256703804480753951291267 18385055706721130926936901)
                    ·
                      refine ⟨3447197945010212048800669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18385055706721130926936901 3447197945010212048800669)
                      ·
                        rfl

theorem cell23_6713394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_6713394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713394 prefixEnd_6713394 := by exact prefixLift 6713394
  have htrace : WordTrace (prefixWord ++ tailWord_6713394) baseStart_6713394 baseEnd_6713394 := by
    simpa [prefixWord, tailWord_6713394, baseEnd_6713394] using wordTrace_append hprefix tailTrace_6713394
  have hstable : (prefixWord ++ tailWord_6713394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713394).length < 2 ^ (prefixWord ++ tailWord_6713394).sum := by decide
  have hdescent : baseEnd_6713394 < baseStart_6713394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713397 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_6713397 : Nat := 118140960795 + 6713397 * 2 ^ 59
def prefixEnd_6713397 : Nat := 4983230072969 + 3 ^ 40 * 6713397 * 2
def baseEnd_6713397 : Nat := 3447199485452175537063155

theorem tailTrace_6713397 : CollatzResearch.WordTrace tailWord_6713397 prefixEnd_6713397 3447199485452175537063155 := by
  unfold tailWord_6713397
  simp only [CollatzResearch.WordTrace]
  refine ⟨244857704459516700770650445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163238469639677800513766963 244857704459516700770650445)
  ·
    refine ⟨91821639172318762788993917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244857704459516700770650445 91821639172318762788993917)
    ·
      refine ⟨34433114689619536045872719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91821639172318762788993917 34433114689619536045872719)
      ·
        refine ⟨51649672034429304068809079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34433114689619536045872719 51649672034429304068809079)
        ·
          refine ⟨77474508051643956103213619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51649672034429304068809079 77474508051643956103213619)
          ·
            refine ⟨116211762077465934154820429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77474508051643956103213619 116211762077465934154820429)
            ·
              refine ⟨43579410779049725308057661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116211762077465934154820429 43579410779049725308057661)
              ·
                refine ⟨16342279042143646990521623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43579410779049725308057661 16342279042143646990521623)
                ·
                  refine ⟨24513418563215470485782435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16342279042143646990521623 24513418563215470485782435)
                  ·
                    refine ⟨36770127844823205728673653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24513418563215470485782435 36770127844823205728673653)
                    ·
                      refine ⟨3447199485452175537063155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36770127844823205728673653 3447199485452175537063155)
                      ·
                        rfl

theorem cell23_6713397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_6713397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713397 prefixEnd_6713397 := by exact prefixLift 6713397
  have htrace : WordTrace (prefixWord ++ tailWord_6713397) baseStart_6713397 baseEnd_6713397 := by
    simpa [prefixWord, tailWord_6713397, baseEnd_6713397] using wordTrace_append hprefix tailTrace_6713397
  have hstable : (prefixWord ++ tailWord_6713397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713397).length < 2 ^ (prefixWord ++ tailWord_6713397).sum := by decide
  have hdescent : baseEnd_6713397 < baseStart_6713397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713404 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_6713404 : Nat := 118140960795 + 6713404 * 2 ^ 59
def prefixEnd_6713404 : Nat := 4983230072969 + 3 ^ 40 * 6713404 * 2
def baseEnd_6713404 : Nat := 1149067693272252336558541

theorem tailTrace_6713404 : CollatzResearch.WordTrace tailWord_6713404 prefixEnd_6713404 1149067693272252336558541 := by
  unfold tailWord_6713404
  simp only [CollatzResearch.WordTrace]
  refine ⟨122428979885245670483077633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163238639846994227310770177 122428979885245670483077633)
  ·
    refine ⟨91821734913934252862308225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122428979885245670483077633 91821734913934252862308225)
    ·
      refine ⟨68866301185450689646731169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91821734913934252862308225 68866301185450689646731169)
      ·
        refine ⟨51649725889088017235048377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68866301185450689646731169 51649725889088017235048377)
        ·
          refine ⟨38737294416816012926286283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51649725889088017235048377 38737294416816012926286283)
          ·
            refine ⟨58105941625224019389429425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38737294416816012926286283 58105941625224019389429425)
            ·
              refine ⟨43579456218918014542072069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58105941625224019389429425 43579456218918014542072069)
              ·
                refine ⟨8171148041047127726638513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43579456218918014542072069 8171148041047127726638513)
                ·
                  refine ⟨6128361030785345794978885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8171148041047127726638513 6128361030785345794978885)
                  ·
                    refine ⟨1149067693272252336558541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6128361030785345794978885 1149067693272252336558541)
                    ·
                      rfl

theorem cell23_6713404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_6713404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713404 prefixEnd_6713404 := by exact prefixLift 6713404
  have htrace : WordTrace (prefixWord ++ tailWord_6713404) baseStart_6713404 baseEnd_6713404 := by
    simpa [prefixWord, tailWord_6713404, baseEnd_6713404] using wordTrace_append hprefix tailTrace_6713404
  have hstable : (prefixWord ++ tailWord_6713404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713404).length < 2 ^ (prefixWord ++ tailWord_6713404).sum := by decide
  have hdescent : baseEnd_6713404 < baseStart_6713404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713421 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_6713421 : Nat := 118140960795 + 6713421 * 2 ^ 59
def prefixEnd_6713421 : Nat := 4983230072969 + 3 ^ 40 * 6713421 * 2
def baseEnd_6713421 : Nat := 1149070602995961147721015

theorem tailTrace_6713421 : CollatzResearch.WordTrace tailWord_6713421 prefixEnd_6713421 1149070602995961147721015 := by
  unfold tailWord_6713421
  simp only [CollatzResearch.WordTrace]
  refine ⟨244858579811429752869524117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163239053207619835246349411 244858579811429752869524117)
  ·
    refine ⟨11477745928660769665758943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 244858579811429752869524117 11477745928660769665758943)
    ·
      refine ⟨17216618892991154498638415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11477745928660769665758943 17216618892991154498638415)
      ·
        refine ⟨25824928339486731747957623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17216618892991154498638415 25824928339486731747957623)
        ·
          refine ⟨38737392509230097621936435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25824928339486731747957623 38737392509230097621936435)
          ·
            refine ⟨58106088763845146432904653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38737392509230097621936435 58106088763845146432904653)
            ·
              refine ⟨21789783286441929912339245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58106088763845146432904653 21789783286441929912339245)
              ·
                refine ⟨8171168732415723717127217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21789783286441929912339245 8171168732415723717127217)
                ·
                  refine ⟨6128376549311792787845413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8171168732415723717127217 6128376549311792787845413)
                  ·
                    refine ⟨1149070602995961147721015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6128376549311792787845413 1149070602995961147721015)
                    ·
                      rfl

theorem cell23_6713421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_6713421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713421 prefixEnd_6713421 := by exact prefixLift 6713421
  have htrace : WordTrace (prefixWord ++ tailWord_6713421) baseStart_6713421 baseEnd_6713421 := by
    simpa [prefixWord, tailWord_6713421, baseEnd_6713421] using wordTrace_append hprefix tailTrace_6713421
  have hstable : (prefixWord ++ tailWord_6713421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713421).length < 2 ^ (prefixWord ++ tailWord_6713421).sum := by decide
  have hdescent : baseEnd_6713421 < baseStart_6713421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713438 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_6713438 : Nat := 118140960795 + 6713438 * 2 ^ 59
def prefixEnd_6713438 : Nat := 4983230072969 + 3 ^ 40 * 6713438 * 2
def baseEnd_6713438 : Nat := 1149073512719669958883489

theorem tailTrace_6713438 : CollatzResearch.WordTrace tailWord_6713438 prefixEnd_6713438 1149073512719669958883489 := by
  unfold tailWord_6713438
  simp only [CollatzResearch.WordTrace]
  refine ⟨30607399981546020596611621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163239466568245443181928645 30607399981546020596611621)
  ·
    refine ⟨5738887496539878861864679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30607399981546020596611621 5738887496539878861864679)
    ·
      refine ⟨8608331244809818292797019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738887496539878861864679 8608331244809818292797019)
      ·
        refine ⟨12912496867214727439195529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8608331244809818292797019 12912496867214727439195529)
        ·
          refine ⟨9684372650411045579396647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12912496867214727439195529 9684372650411045579396647)
          ·
            refine ⟨14526558975616568369094971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9684372650411045579396647 14526558975616568369094971)
            ·
              refine ⟨21789838463424852553642457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14526558975616568369094971 21789838463424852553642457)
              ·
                refine ⟨16342378847568639415231843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21789838463424852553642457 16342378847568639415231843)
                ·
                  refine ⟨24513568271352959122847765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16342378847568639415231843 24513568271352959122847765)
                  ·
                    refine ⟨1149073512719669958883489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24513568271352959122847765 1149073512719669958883489)
                    ·
                      rfl

theorem cell23_6713438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_6713438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713438 prefixEnd_6713438 := by exact prefixLift 6713438
  have htrace : WordTrace (prefixWord ++ tailWord_6713438) baseStart_6713438 baseEnd_6713438 := by
    simpa [prefixWord, tailWord_6713438, baseEnd_6713438] using wordTrace_append hprefix tailTrace_6713438
  have hstable : (prefixWord ++ tailWord_6713438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713438).length < 2 ^ (prefixWord ++ tailWord_6713438).sum := by decide
  have hdescent : baseEnd_6713438 < baseStart_6713438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713444 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_6713444 : Nat := 118140960795 + 6713444 * 2 ^ 59
def prefixEnd_6713444 : Nat := 4983230072969 + 3 ^ 40 * 6713444 * 2
def baseEnd_6713444 : Nat := 3447223619042936853175439

theorem tailTrace_6713444 : CollatzResearch.WordTrace tailWord_6713444 prefixEnd_6713444 3447223619042936853175439 := by
  unfold tailWord_6713444
  simp only [CollatzResearch.WordTrace]
  refine ⟨122429709345173213898805693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163239612460230951865074257 122429709345173213898805693)
  ·
    refine ⟨45911141004439955212052135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122429709345173213898805693 45911141004439955212052135)
    ·
      refine ⟨68866711506659932818078203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45911141004439955212052135 68866711506659932818078203)
      ·
        refine ⟨103300067259989899227117305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68866711506659932818078203 103300067259989899227117305)
        ·
          refine ⟨77475050444992424420337979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103300067259989899227117305 77475050444992424420337979)
          ·
            refine ⟨116212575667488636630506969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77475050444992424420337979 116212575667488636630506969)
            ·
              refine ⟨87159431750616477472880227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116212575667488636630506969 87159431750616477472880227)
              ·
                refine ⟨130739147625924716209320341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87159431750616477472880227 130739147625924716209320341)
                ·
                  refine ⟨6128397544965221072311891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130739147625924716209320341 6128397544965221072311891)
                  ·
                    refine ⟨9192596317447831608467837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6128397544965221072311891 9192596317447831608467837)
                    ·
                      refine ⟨3447223619042936853175439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9192596317447831608467837 3447223619042936853175439)
                      ·
                        rfl

theorem cell23_6713444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_6713444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713444 prefixEnd_6713444 := by exact prefixLift 6713444
  have htrace : WordTrace (prefixWord ++ tailWord_6713444) baseStart_6713444 baseEnd_6713444 := by
    simpa [prefixWord, tailWord_6713444, baseEnd_6713444] using wordTrace_append hprefix tailTrace_6713444
  have hstable : (prefixWord ++ tailWord_6713444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713444).length < 2 ^ (prefixWord ++ tailWord_6713444).sum := by decide
  have hdescent : baseEnd_6713444 < baseStart_6713444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713462 : List Nat := [5, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_6713462 : Nat := 118140960795 + 6713462 * 2 ^ 59
def prefixEnd_6713462 : Nat := 4983230072969 + 3 ^ 40 * 6713462 * 2
def baseEnd_6713462 : Nat := 3447232861694717782750357

theorem tailTrace_6713462 : CollatzResearch.WordTrace tailWord_6713462 prefixEnd_6713462 3447232861694717782750357 := by
  unfold tailWord_6713462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15303754700267576054485415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163240050136187477914511093 15303754700267576054485415)
  ·
    refine ⟨22955632050401364081728123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15303754700267576054485415 22955632050401364081728123)
    ·
      refine ⟨34433448075602046122592185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22955632050401364081728123 34433448075602046122592185)
      ·
        refine ⟨25825086056701534591944139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34433448075602046122592185 25825086056701534591944139)
        ·
          refine ⟨38737629085052301887916209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25825086056701534591944139 38737629085052301887916209)
          ·
            refine ⟨29053221813789226415937157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38737629085052301887916209 29053221813789226415937157)
            ·
              refine ⟨5447479090085479952988217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29053221813789226415937157 5447479090085479952988217)
              ·
                refine ⟨4085609317564109964741163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447479090085479952988217 4085609317564109964741163)
                ·
                  refine ⟨6128413976346164947111745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085609317564109964741163 6128413976346164947111745)
                  ·
                    refine ⟨4596310482259623710333809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6128413976346164947111745 4596310482259623710333809)
                    ·
                      refine ⟨3447232861694717782750357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4596310482259623710333809 3447232861694717782750357)
                      ·
                        rfl

theorem cell23_6713462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_6713462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713462 prefixEnd_6713462 := by exact prefixLift 6713462
  have htrace : WordTrace (prefixWord ++ tailWord_6713462) baseStart_6713462 baseEnd_6713462 := by
    simpa [prefixWord, tailWord_6713462, baseEnd_6713462] using wordTrace_append hprefix tailTrace_6713462
  have hstable : (prefixWord ++ tailWord_6713462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713462).length < 2 ^ (prefixWord ++ tailWord_6713462).sum := by decide
  have hdescent : baseEnd_6713462 < baseStart_6713462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713477 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_6713477 : Nat := 118140960795 + 6713477 * 2 ^ 59
def prefixEnd_6713477 : Nat := 4983230072969 + 3 ^ 40 * 6713477 * 2
def baseEnd_6713477 : Nat := 1149080187968178408020929

theorem tailTrace_6713477 : CollatzResearch.WordTrace tailWord_6713477 prefixEnd_6713477 1149080187968178408020929 := by
  unfold tailWord_6713477
  simp only [CollatzResearch.WordTrace]
  refine ⟨244860622299226874433562685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163240414866151249622375123 244860622299226874433562685)
  ·
    refine ⟨91822733362210077912586007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244860622299226874433562685 91822733362210077912586007)
    ·
      refine ⟨137734100043315116868879011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91822733362210077912586007 137734100043315116868879011)
      ·
        refine ⟨206601150064972675303318517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137734100043315116868879011 206601150064972675303318517)
        ·
          refine ⟨19368857818591188309686111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206601150064972675303318517 19368857818591188309686111)
          ·
            refine ⟨29053286727886782464529167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19368857818591188309686111 29053286727886782464529167)
            ·
              refine ⟨43579930091830173696793751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29053286727886782464529167 43579930091830173696793751)
              ·
                refine ⟨65369895137745260545190627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43579930091830173696793751 65369895137745260545190627)
                ·
                  refine ⟨98054842706617890817785941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65369895137745260545190627 98054842706617890817785941)
                  ·
                    refine ⟨1149080187968178408020929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98054842706617890817785941 1149080187968178408020929)
                    ·
                      rfl

theorem cell23_6713477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_6713477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713477 prefixEnd_6713477 := by exact prefixLift 6713477
  have htrace : WordTrace (prefixWord ++ tailWord_6713477) baseStart_6713477 baseEnd_6713477 := by
    simpa [prefixWord, tailWord_6713477, baseEnd_6713477] using wordTrace_append hprefix tailTrace_6713477
  have hstable : (prefixWord ++ tailWord_6713477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713477).length < 2 ^ (prefixWord ++ tailWord_6713477).sum := by decide
  have hdescent : baseEnd_6713477 < baseStart_6713477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713501 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_6713501 : Nat := 118140960795 + 6713501 * 2 ^ 59
def prefixEnd_6713501 : Nat := 4983230072969 + 3 ^ 40 * 6713501 * 2
def baseEnd_6713501 : Nat := 3447252887440243130162677

theorem tailTrace_6713501 : CollatzResearch.WordTrace tailWord_6713501 prefixEnd_6713501 3447252887440243130162677 := by
  unfold tailWord_6713501
  simp only [CollatzResearch.WordTrace]
  refine ⟨244861497651139926532436357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163240998434093284354957571 244861497651139926532436357)
  ·
    refine ⟨45911530809588736224831817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244861497651139926532436357 45911530809588736224831817)
    ·
      refine ⟨34433648107191552168623863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45911530809588736224831817 34433648107191552168623863)
      ·
        refine ⟨51650472160787328252935795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34433648107191552168623863 51650472160787328252935795)
        ·
          refine ⟨77475708241180992379403693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51650472160787328252935795 77475708241180992379403693)
          ·
            refine ⟨29053390590442872142276385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77475708241180992379403693 29053390590442872142276385)
            ·
              refine ⟨21790042942832154106707289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29053390590442872142276385 21790042942832154106707289)
              ·
                refine ⟨16342532207124115580030467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21790042942832154106707289 16342532207124115580030467)
                ·
                  refine ⟨24513798310686173370045701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16342532207124115580030467 24513798310686173370045701)
                  ·
                    refine ⟨4596337183253657506883569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24513798310686173370045701 4596337183253657506883569)
                    ·
                      refine ⟨3447252887440243130162677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4596337183253657506883569 3447252887440243130162677)
                      ·
                        rfl

theorem cell23_6713501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_6713501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713501 prefixEnd_6713501 := by exact prefixLift 6713501
  have htrace : WordTrace (prefixWord ++ tailWord_6713501) baseStart_6713501 baseEnd_6713501 := by
    simpa [prefixWord, tailWord_6713501, baseEnd_6713501] using wordTrace_append hprefix tailTrace_6713501
  have hstable : (prefixWord ++ tailWord_6713501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713501).length < 2 ^ (prefixWord ++ tailWord_6713501).sum := by decide
  have hdescent : baseEnd_6713501 < baseStart_6713501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713505 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_6713505 : Nat := 118140960795 + 6713505 * 2 ^ 59
def prefixEnd_6713505 : Nat := 4983230072969 + 3 ^ 40 * 6713505 * 2
def baseEnd_6713505 : Nat := 3447254941362861114512659

theorem tailTrace_6713505 : CollatzResearch.WordTrace tailWord_6713505 prefixEnd_6713505 3447254941362861114512659 := by
  unfold tailWord_6713505
  simp only [CollatzResearch.WordTrace]
  refine ⟨244861643543125435215581969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163241095695416956810387979 244861643543125435215581969)
  ·
    refine ⟨183646232657344076411686477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244861643543125435215581969 183646232657344076411686477)
    ·
      refine ⟨68867337246504028654382429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183646232657344076411686477 68867337246504028654382429)
      ·
        refine ⟨25825251467439010745393411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68867337246504028654382429 25825251467439010745393411)
        ·
          refine ⟨38737877201158516118090117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25825251467439010745393411 38737877201158516118090117)
          ·
            refine ⟨7263351975217221772141897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38737877201158516118090117 7263351975217221772141897)
            ·
              refine ⟨5447513981412916329106423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7263351975217221772141897 5447513981412916329106423)
              ·
                refine ⟨8171270972119374493659635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5447513981412916329106423 8171270972119374493659635)
                ·
                  refine ⟨12256906458179061740489453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8171270972119374493659635 12256906458179061740489453)
                  ·
                    refine ⟨4596339921817148152683545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12256906458179061740489453 4596339921817148152683545)
                    ·
                      refine ⟨3447254941362861114512659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4596339921817148152683545 3447254941362861114512659)
                      ·
                        rfl

theorem cell23_6713505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_6713505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713505 prefixEnd_6713505 := by exact prefixLift 6713505
  have htrace : WordTrace (prefixWord ++ tailWord_6713505) baseStart_6713505 baseEnd_6713505 := by
    simpa [prefixWord, tailWord_6713505, baseEnd_6713505] using wordTrace_append hprefix tailTrace_6713505
  have hstable : (prefixWord ++ tailWord_6713505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713505).length < 2 ^ (prefixWord ++ tailWord_6713505).sum := by decide
  have hdescent : baseEnd_6713505 < baseStart_6713505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713554 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_6713554 : Nat := 118140960795 + 6713554 * 2 ^ 59
def prefixEnd_6713554 : Nat := 4983230072969 + 3 ^ 40 * 6713554 * 2
def baseEnd_6713554 : Nat := 1149093367304977140933311

theorem tailTrace_6713554 : CollatzResearch.WordTrace tailWord_6713554 prefixEnd_6713554 1149093367304977140933311 := by
  unfold tailWord_6713554
  simp only [CollatzResearch.WordTrace]
  refine ⟨61215857679986979146028929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163242287146631944389410477 61215857679986979146028929)
  ·
    refine ⟨45911893259990234359521697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61215857679986979146028929 45911893259990234359521697)
    ·
      refine ⟨34433919944992675769641273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45911893259990234359521697 34433919944992675769641273)
      ·
        refine ⟨25825439958744506827230955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34433919944992675769641273 25825439958744506827230955)
        ·
          refine ⟨38738159938116760240846433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25825439958744506827230955 38738159938116760240846433)
          ·
            refine ⟨29053619953587570180634825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38738159938116760240846433 29053619953587570180634825)
            ·
              refine ⟨21790214965190677635476119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29053619953587570180634825 21790214965190677635476119)
              ·
                refine ⟨32685322447786016453214179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21790214965190677635476119 32685322447786016453214179)
                ·
                  refine ⟨49027983671679024679821269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32685322447786016453214179 49027983671679024679821269)
                  ·
                    refine ⟨1149093367304977140933311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49027983671679024679821269 1149093367304977140933311)
                    ·
                      rfl

theorem cell23_6713554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_6713554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713554 prefixEnd_6713554 := by exact prefixLift 6713554
  have htrace : WordTrace (prefixWord ++ tailWord_6713554) baseStart_6713554 baseEnd_6713554 := by
    simpa [prefixWord, tailWord_6713554, baseEnd_6713554] using wordTrace_append hprefix tailTrace_6713554
  have hstable : (prefixWord ++ tailWord_6713554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713554).length < 2 ^ (prefixWord ++ tailWord_6713554).sum := by decide
  have hdescent : baseEnd_6713554 < baseStart_6713554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713577 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_6713577 : Nat := 118140960795 + 6713577 * 2 ^ 59
def prefixEnd_6713577 : Nat := 4983230072969 + 3 ^ 40 * 6713577 * 2
def baseEnd_6713577 : Nat := 3447291911969984832812327

theorem tailTrace_6713577 : CollatzResearch.WordTrace tailWord_6713577 prefixEnd_6713577 3447291911969984832812327 := by
  unfold tailWord_6713577
  simp only [CollatzResearch.WordTrace]
  refine ⟨244864269598864591512202985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163242846399243061008135323 244864269598864591512202985)
  ·
    refine ⟨183648202199148443634152239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244864269598864591512202985 183648202199148443634152239)
    ·
      refine ⟨275472303298722665451228359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183648202199148443634152239 275472303298722665451228359)
      ·
        refine ⟨413208454948083998176842539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275472303298722665451228359 413208454948083998176842539)
        ·
          refine ⟨619812682422125997265263809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413208454948083998176842539 619812682422125997265263809)
          ·
            refine ⟨464859511816594497948947857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619812682422125997265263809 464859511816594497948947857)
            ·
              refine ⟨348644633862445873461710893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464859511816594497948947857 348644633862445873461710893)
              ·
                refine ⟨130741737698417202548141585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348644633862445873461710893 130741737698417202548141585)
                ·
                  refine ⟨98056303273812901911106189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130741737698417202548141585 98056303273812901911106189)
                  ·
                    refine ⟨36771113727679838216664821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98056303273812901911106189 36771113727679838216664821)
                    ·
                      refine ⟨3447291911969984832812327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36771113727679838216664821 3447291911969984832812327)
                      ·
                        rfl

theorem cell23_6713577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_6713577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713577 prefixEnd_6713577 := by exact prefixLift 6713577
  have htrace : WordTrace (prefixWord ++ tailWord_6713577) baseStart_6713577 baseEnd_6713577 := by
    simpa [prefixWord, tailWord_6713577, baseEnd_6713577] using wordTrace_append hprefix tailTrace_6713577
  have hstable : (prefixWord ++ tailWord_6713577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713577).length < 2 ^ (prefixWord ++ tailWord_6713577).sum := by decide
  have hdescent : baseEnd_6713577 < baseStart_6713577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713581 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_6713581 : Nat := 118140960795 + 6713581 * 2 ^ 59
def prefixEnd_6713581 : Nat := 4983230072969 + 3 ^ 40 * 6713581 * 2
def baseEnd_6713581 : Nat := 3447293965892602817162309

theorem tailTrace_6713581 : CollatzResearch.WordTrace tailWord_6713581 prefixEnd_6713581 3447293965892602817162309 := by
  unfold tailWord_6713581
  simp only [CollatzResearch.WordTrace]
  refine ⟨244864415490850100195348597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163242943660566733463565731 244864415490850100195348597)
  ·
    refine ⟨22956038952267196893313931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244864415490850100195348597 22956038952267196893313931)
    ·
      refine ⟨34434058428400795339970897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22956038952267196893313931 34434058428400795339970897)
      ·
        refine ⟨25825543821300596504978173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34434058428400795339970897 25825543821300596504978173)
        ·
          refine ⟨9684578932987723689366815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25825543821300596504978173 9684578932987723689366815)
          ·
            refine ⟨14526868399481585534050223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9684578932987723689366815 14526868399481585534050223)
            ·
              refine ⟨21790302599222378301075335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14526868399481585534050223 21790302599222378301075335)
              ·
                refine ⟨32685453898833567451613003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21790302599222378301075335 32685453898833567451613003)
                ·
                  refine ⟨49028180848250351177419505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32685453898833567451613003 49028180848250351177419505)
                  ·
                    refine ⟨36771135636187763383064629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49028180848250351177419505 36771135636187763383064629)
                    ·
                      refine ⟨3447293965892602817162309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36771135636187763383064629 3447293965892602817162309)
                      ·
                        rfl

theorem cell23_6713581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_6713581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713581 prefixEnd_6713581 := by exact prefixLift 6713581
  have htrace : WordTrace (prefixWord ++ tailWord_6713581) baseStart_6713581 baseEnd_6713581 := by
    simpa [prefixWord, tailWord_6713581, baseEnd_6713581] using wordTrace_append hprefix tailTrace_6713581
  have hstable : (prefixWord ++ tailWord_6713581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713581).length < 2 ^ (prefixWord ++ tailWord_6713581).sum := by decide
  have hdescent : baseEnd_6713581 < baseStart_6713581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713611 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 3]
def baseStart_6713611 : Nat := 118140960795 + 6713611 * 2 ^ 59
def prefixEnd_6713611 : Nat := 4983230072969 + 3 ^ 40 * 6713611 * 2
def baseEnd_6713611 : Nat := 3447309370312237699787171

theorem tailTrace_6713611 : CollatzResearch.WordTrace tailWord_6713611 prefixEnd_6713611 3447309370312237699787171 := by
  unfold tailWord_6713611
  simp only [CollatzResearch.WordTrace]
  refine ⟨244865509680741415318940687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163243673120494276879293791 244865509680741415318940687)
  ·
    refine ⟨367298264521112122978411031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244865509680741415318940687 367298264521112122978411031)
    ·
      refine ⟨550947396781668184467616547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367298264521112122978411031 550947396781668184467616547)
      ·
        refine ⟨826421095172502276701424821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550947396781668184467616547 826421095172502276701424821)
        ·
          refine ⟨77476977672422088440758577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 826421095172502276701424821 77476977672422088440758577)
          ·
            refine ⟨58107733254316566330568933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77476977672422088440758577 58107733254316566330568933)
            ·
              refine ⟨10895199985184356186981675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58107733254316566330568933 10895199985184356186981675)
              ·
                refine ⟨16342799977776534280472513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10895199985184356186981675 16342799977776534280472513)
                ·
                  refine ⟨12257099983332400710354385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16342799977776534280472513 12257099983332400710354385)
                  ·
                    refine ⟨9192824987499300532765789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12257099983332400710354385 9192824987499300532765789)
                    ·
                      refine ⟨3447309370312237699787171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9192824987499300532765789 3447309370312237699787171)
                      ·
                        rfl

theorem cell23_6713611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 3].length) (baseStart_6713611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713611 prefixEnd_6713611 := by exact prefixLift 6713611
  have htrace : WordTrace (prefixWord ++ tailWord_6713611) baseStart_6713611 baseEnd_6713611 := by
    simpa [prefixWord, tailWord_6713611, baseEnd_6713611] using wordTrace_append hprefix tailTrace_6713611
  have hstable : (prefixWord ++ tailWord_6713611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713611).length < 2 ^ (prefixWord ++ tailWord_6713611).sum := by decide
  have hdescent : baseEnd_6713611 < baseStart_6713611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713631 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 6]
def baseStart_6713631 : Nat := 118140960795 + 6713631 * 2 ^ 59
def prefixEnd_6713631 : Nat := 4983230072969 + 3 ^ 40 * 6713631 * 2
def baseEnd_6713631 : Nat := 383035515547258624615231

theorem tailTrace_6713631 : CollatzResearch.WordTrace tailWord_6713631 prefixEnd_6713631 383035515547258624615231 := by
  unfold tailWord_6713631
  simp only [CollatzResearch.WordTrace]
  refine ⟨244866239140668958734668747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163244159427112639156445831 244866239140668958734668747)
  ·
    refine ⟨367299358711003438102003121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244866239140668958734668747 367299358711003438102003121)
    ·
      refine ⟨275474519033252578576502341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367299358711003438102003121 275474519033252578576502341)
      ·
        refine ⟨51651472318734858483094189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275474519033252578576502341 51651472318734858483094189)
        ·
          refine ⟨19369302119525571931160321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51651472318734858483094189 19369302119525571931160321)
          ·
            refine ⟨14526976589644178948370241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19369302119525571931160321 14526976589644178948370241)
            ·
              refine ⟨10895232442233134211277681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14526976589644178948370241 10895232442233134211277681)
              ·
                refine ⟨8171424331674850658458261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10895232442233134211277681 8171424331674850658458261)
                ·
                  refine ⟨383035515547258624615231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8171424331674850658458261 383035515547258624615231)
                  ·
                    rfl

theorem cell23_6713631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 6].length) (baseStart_6713631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713631 prefixEnd_6713631 := by exact prefixLift 6713631
  have htrace : WordTrace (prefixWord ++ tailWord_6713631) baseStart_6713631 baseEnd_6713631 := by
    simpa [prefixWord, tailWord_6713631, baseEnd_6713631] using wordTrace_append hprefix tailTrace_6713631
  have hstable : (prefixWord ++ tailWord_6713631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713631).length < 2 ^ (prefixWord ++ tailWord_6713631).sum := by decide
  have hdescent : baseEnd_6713631 < baseStart_6713631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713644 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_6713644 : Nat := 118140960795 + 6713644 * 2 ^ 59
def prefixEnd_6713644 : Nat := 4983230072969 + 3 ^ 40 * 6713644 * 2
def baseEnd_6713644 : Nat := 1149108771724612023558173

theorem tailTrace_6713644 : CollatzResearch.WordTrace tailWord_6713644 prefixEnd_6713644 1149108771724612023558173 := by
  unfold tailWord_6713644
  simp only [CollatzResearch.WordTrace]
  refine ⟨122433356644810930977445993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163244475526414574636594657 122433356644810930977445993)
  ·
    refine ⟨91825017483608198233084495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122433356644810930977445993 91825017483608198233084495)
    ·
      refine ⟨137737526225412297349626743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91825017483608198233084495 137737526225412297349626743)
      ·
        refine ⟨206606289338118446024440115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137737526225412297349626743 206606289338118446024440115)
        ·
          refine ⟨309909434007177669036660173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206606289338118446024440115 309909434007177669036660173)
          ·
            refine ⟨116216037752691625888747565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309909434007177669036660173 116216037752691625888747565)
            ·
              refine ⟨43581014157259359708280337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116216037752691625888747565 43581014157259359708280337)
              ·
                refine ⟨32685760617944519781210253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43581014157259359708280337 32685760617944519781210253)
                ·
                  refine ⟨12257160231729194917953845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32685760617944519781210253 12257160231729194917953845)
                  ·
                    refine ⟨1149108771724612023558173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12257160231729194917953845 1149108771724612023558173)
                    ·
                      rfl

theorem cell23_6713644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_6713644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713644 prefixEnd_6713644 := by exact prefixLift 6713644
  have htrace : WordTrace (prefixWord ++ tailWord_6713644) baseStart_6713644 baseEnd_6713644 := by
    simpa [prefixWord, tailWord_6713644, baseEnd_6713644] using wordTrace_append hprefix tailTrace_6713644
  have hstable : (prefixWord ++ tailWord_6713644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713644).length < 2 ^ (prefixWord ++ tailWord_6713644).sum := by decide
  have hdescent : baseEnd_6713644 < baseStart_6713644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713651 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 1, 5, 2]
def baseStart_6713651 : Nat := 118140960795 + 6713651 * 2 ^ 59
def prefixEnd_6713651 : Nat := 4983230072969 + 3 ^ 40 * 6713651 * 2
def baseEnd_6713651 : Nat := 3447329909538417543286987

theorem tailTrace_6713651 : CollatzResearch.WordTrace tailWord_6713651 prefixEnd_6713651 3447329909538417543286987 := by
  unfold tailWord_6713651
  simp only [CollatzResearch.WordTrace]
  refine ⟨244866968600596502150396807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163244645733731001433597871 244866968600596502150396807)
  ·
    refine ⟨367300452900894753225595211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244866968600596502150396807 367300452900894753225595211)
    ·
      refine ⟨550950679351342129838392817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367300452900894753225595211 550950679351342129838392817)
      ·
        refine ⟨413213009513506597378794613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550950679351342129838392817 413213009513506597378794613)
        ·
          refine ⟨38738719641891243504261995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 413213009513506597378794613 38738719641891243504261995)
          ·
            refine ⟨58108079462836865256392993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38738719641891243504261995 58108079462836865256392993)
            ·
              refine ⟨43581059597127648942294745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58108079462836865256392993 43581059597127648942294745)
              ·
                refine ⟨32685794697845736706721059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43581059597127648942294745 32685794697845736706721059)
                ·
                  refine ⟨49028692046768605060081589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32685794697845736706721059 49028692046768605060081589)
                  ·
                    refine ⟨4596439879384556724382649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49028692046768605060081589 4596439879384556724382649)
                    ·
                      refine ⟨3447329909538417543286987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4596439879384556724382649 3447329909538417543286987)
                      ·
                        rfl

theorem cell23_6713651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 5, 2].length) (baseStart_6713651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713651 prefixEnd_6713651 := by exact prefixLift 6713651
  have htrace : WordTrace (prefixWord ++ tailWord_6713651) baseStart_6713651 baseEnd_6713651 := by
    simpa [prefixWord, tailWord_6713651, baseEnd_6713651] using wordTrace_append hprefix tailTrace_6713651
  have hstable : (prefixWord ++ tailWord_6713651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713651).length < 2 ^ (prefixWord ++ tailWord_6713651).sum := by decide
  have hdescent : baseEnd_6713651 < baseStart_6713651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713658 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3]
def baseStart_6713658 : Nat := 118140960795 + 6713658 * 2 ^ 59
def prefixEnd_6713658 : Nat := 4983230072969 + 3 ^ 40 * 6713658 * 2
def baseEnd_6713658 : Nat := 3447333503902999015899455

theorem tailTrace_6713658 : CollatzResearch.WordTrace tailWord_6713658 prefixEnd_6713658 3447333503902999015899455 := by
  unfold tailWord_6713658
  simp only [CollatzResearch.WordTrace]
  refine ⟨61216805977892785586475407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163244815941047428230601085 61216805977892785586475407)
  ·
    refine ⟨91825208966839178379713111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61216805977892785586475407 91825208966839178379713111)
    ·
      refine ⟨137737813450258767569569667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91825208966839178379713111 137737813450258767569569667)
      ·
        refine ⟨206606720175388151354354501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137737813450258767569569667 206606720175388151354354501)
        ·
          refine ⟨38738760032885278378941469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206606720175388151354354501 38738760032885278378941469)
          ·
            refine ⟨14527035012331979392103051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38738760032885278378941469 14527035012331979392103051)
            ·
              refine ⟨21790552518497969088154577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14527035012331979392103051 21790552518497969088154577)
              ·
                refine ⟨16342914388873476816115933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21790552518497969088154577 16342914388873476816115933)
                ·
                  refine ⟨6128592895827553806043475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16342914388873476816115933 6128592895827553806043475)
                  ·
                    refine ⟨9192889343741330709065213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6128592895827553806043475 9192889343741330709065213)
                    ·
                      refine ⟨3447333503902999015899455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9192889343741330709065213 3447333503902999015899455)
                      ·
                        rfl

theorem cell23_6713658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_6713658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713658 prefixEnd_6713658 := by exact prefixLift 6713658
  have htrace : WordTrace (prefixWord ++ tailWord_6713658) baseStart_6713658 baseEnd_6713658 := by
    simpa [prefixWord, tailWord_6713658, baseEnd_6713658] using wordTrace_append hprefix tailTrace_6713658
  have hstable : (prefixWord ++ tailWord_6713658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713658).length < 2 ^ (prefixWord ++ tailWord_6713658).sum := by decide
  have hdescent : baseEnd_6713658 < baseStart_6713658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713692 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6713692 : Nat := 118140960795 + 6713692 * 2 ^ 59
def prefixEnd_6713692 : Nat := 4983230072969 + 3 ^ 40 * 6713692 * 2
def baseEnd_6713692 : Nat := 3447350962245251882874299

theorem tailTrace_6713692 : CollatzResearch.WordTrace tailWord_6713692 prefixEnd_6713692 3447350962245251882874299 := by
  unfold tailWord_6713692
  simp only [CollatzResearch.WordTrace]
  refine ⟨122434231996723983076319665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163245642662298644101759553 122434231996723983076319665)
  ·
    refine ⟨91825673997542987307239749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122434231996723983076319665 91825673997542987307239749)
    ·
      refine ⟨17217313874539310120107453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91825673997542987307239749 17217313874539310120107453)
      ·
        refine ⟨6456492702952241295040295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17217313874539310120107453 6456492702952241295040295)
        ·
          refine ⟨9684739054428361942560443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6456492702952241295040295 9684739054428361942560443)
          ·
            refine ⟨14527108581642542913840665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9684739054428361942560443 14527108581642542913840665)
            ·
              refine ⟨10895331436231907185380499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14527108581642542913840665 10895331436231907185380499)
              ·
                refine ⟨16342997154347860778070749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10895331436231907185380499 16342997154347860778070749)
                ·
                  refine ⟨6128623932880447791776531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16342997154347860778070749 6128623932880447791776531)
                  ·
                    refine ⟨9192935899320671687664797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6128623932880447791776531 9192935899320671687664797)
                    ·
                      refine ⟨3447350962245251882874299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9192935899320671687664797 3447350962245251882874299)
                      ·
                        rfl

theorem cell23_6713692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6713692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713692 prefixEnd_6713692 := by exact prefixLift 6713692
  have htrace : WordTrace (prefixWord ++ tailWord_6713692) baseStart_6713692 baseEnd_6713692 := by
    simpa [prefixWord, tailWord_6713692, baseEnd_6713692] using wordTrace_append hprefix tailTrace_6713692
  have hstable : (prefixWord ++ tailWord_6713692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713692).length < 2 ^ (prefixWord ++ tailWord_6713692).sum := by decide
  have hdescent : baseEnd_6713692 < baseStart_6713692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713701 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_6713701 : Nat := 118140960795 + 6713701 * 2 ^ 59
def prefixEnd_6713701 : Nat := 4983230072969 + 3 ^ 40 * 6713701 * 2
def baseEnd_6713701 : Nat := 3447355583571142347661757

theorem tailTrace_6713701 : CollatzResearch.WordTrace tailWord_6713701 prefixEnd_6713701 3447355583571142347661757 := by
  unfold tailWord_6713701
  simp only [CollatzResearch.WordTrace]
  refine ⟨244868792250415360689716957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163245861500276907126477971 244868792250415360689716957)
  ·
    refine ⟨91825797093905760258643859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244868792250415360689716957 91825797093905760258643859)
    ·
      refine ⟨137738695640858640387965789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91825797093905760258643859 137738695640858640387965789)
      ·
        refine ⟨51652010865321990145487171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137738695640858640387965789 51652010865321990145487171)
        ·
          refine ⟨77478016297982985218230757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51652010865321990145487171 77478016297982985218230757)
          ·
            refine ⟨14527128055871809728418267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77478016297982985218230757 14527128055871809728418267)
            ·
              refine ⟨21790692083807714592627401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14527128055871809728418267 21790692083807714592627401)
              ·
                refine ⟨16343019062855785944470551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21790692083807714592627401 16343019062855785944470551)
                ·
                  refine ⟨24514528594283678916705827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16343019062855785944470551 24514528594283678916705827)
                  ·
                    refine ⟨36771792891425518375058741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24514528594283678916705827 36771792891425518375058741)
                    ·
                      refine ⟨3447355583571142347661757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36771792891425518375058741 3447355583571142347661757)
                      ·
                        rfl

theorem cell23_6713701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_6713701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713701 prefixEnd_6713701 := by exact prefixLift 6713701
  have htrace : WordTrace (prefixWord ++ tailWord_6713701) baseStart_6713701 baseEnd_6713701 := by
    simpa [prefixWord, tailWord_6713701, baseEnd_6713701] using wordTrace_append hprefix tailTrace_6713701
  have hstable : (prefixWord ++ tailWord_6713701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713701).length < 2 ^ (prefixWord ++ tailWord_6713701).sum := by decide
  have hdescent : baseEnd_6713701 < baseStart_6713701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713708 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_6713708 : Nat := 118140960795 + 6713708 * 2 ^ 59
def prefixEnd_6713708 : Nat := 4983230072969 + 3 ^ 40 * 6713708 * 2
def baseEnd_6713708 : Nat := 1149119725978574606758075

theorem tailTrace_6713708 : CollatzResearch.WordTrace tailWord_6713708 prefixEnd_6713708 1149119725978574606758075 := by
  unfold tailWord_6713708
  simp only [CollatzResearch.WordTrace]
  refine ⟨122434523780695000442610889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163246031707593333923481185 122434523780695000442610889)
  ·
    refine ⟨91825892835521250331958167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122434523780695000442610889 91825892835521250331958167)
    ·
      refine ⟨137738839253281875497937251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91825892835521250331958167 137738839253281875497937251)
      ·
        refine ⟨206608258879922813246905877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137738839253281875497937251 206608258879922813246905877)
        ·
          refine ⟨9684762134996381870948713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206608258879922813246905877 9684762134996381870948713)
          ·
            refine ⟨7263571601247286403211535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9684762134996381870948713 7263571601247286403211535)
            ·
              refine ⟨10895357401870929604817303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7263571601247286403211535 10895357401870929604817303)
              ·
                refine ⟨16343036102806394407225955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10895357401870929604817303 16343036102806394407225955)
                ·
                  refine ⟨24514554154209591610838933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16343036102806394407225955 24514554154209591610838933)
                  ·
                    refine ⟨1149119725978574606758075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24514554154209591610838933 1149119725978574606758075)
                    ·
                      rfl

theorem cell23_6713708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_6713708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713708 prefixEnd_6713708 := by exact prefixLift 6713708
  have htrace : WordTrace (prefixWord ++ tailWord_6713708) baseStart_6713708 baseEnd_6713708 := by
    simpa [prefixWord, tailWord_6713708, baseEnd_6713708] using wordTrace_append hprefix tailTrace_6713708
  have hstable : (prefixWord ++ tailWord_6713708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713708).length < 2 ^ (prefixWord ++ tailWord_6713708).sum := by decide
  have hdescent : baseEnd_6713708 < baseStart_6713708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713738 : List Nat := [3, 1, 2, 5, 1, 2, 9]
def baseStart_6713738 : Nat := 118140960795 + 6713738 * 2 ^ 59
def prefixEnd_6713738 : Nat := 4983230072969 + 3 ^ 40 * 6713738 * 2
def baseEnd_6713738 : Nat := 42560180029078502504927

theorem tailTrace_6713738 : CollatzResearch.WordTrace tailWord_6713738 prefixEnd_6713738 42560180029078502504927 := by
  unfold tailWord_6713738
  simp only [CollatzResearch.WordTrace]
  refine ⟨61217535437820329002203467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163246761167520877339209245 61217535437820329002203467)
  ·
    refine ⟨91826303156730493503305201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61217535437820329002203467 91826303156730493503305201)
    ·
      refine ⟨68869727367547870127478901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91826303156730493503305201 68869727367547870127478901)
      ·
        refine ⟨6456536940707612824451147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68869727367547870127478901 6456536940707612824451147)
        ·
          refine ⟨9684805411061419236676721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6456536940707612824451147 9684805411061419236676721)
          ·
            refine ⟨7263604058296064427507541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9684805411061419236676721 7263604058296064427507541)
            ·
              refine ⟨42560180029078502504927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7263604058296064427507541 42560180029078502504927)
              ·
                rfl

theorem cell23_6713738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 9].length) (baseStart_6713738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713738 prefixEnd_6713738 := by exact prefixLift 6713738
  have htrace : WordTrace (prefixWord ++ tailWord_6713738) baseStart_6713738 baseEnd_6713738 := by
    simpa [prefixWord, tailWord_6713738, baseEnd_6713738] using wordTrace_append hprefix tailTrace_6713738
  have hstable : (prefixWord ++ tailWord_6713738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713738).length < 2 ^ (prefixWord ++ tailWord_6713738).sum := by decide
  have hdescent : baseEnd_6713738 < baseStart_6713738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713771 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 10, 2]
def baseStart_6713771 : Nat := 118140960795 + 6713771 * 2 ^ 59
def prefixEnd_6713771 : Nat := 4983230072969 + 3 ^ 40 * 6713771 * 2
def baseEnd_6713771 : Nat := 3447391527216957073786435

theorem tailTrace_6713771 : CollatzResearch.WordTrace tailWord_6713771 prefixEnd_6713771 3447391527216957073786435 := by
  unfold tailWord_6713771
  simp only [CollatzResearch.WordTrace]
  refine ⟨244871345360161762644765167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163247563573441175096510111 244871345360161762644765167)
  ·
    refine ⟨367307018040242643967147751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244871345360161762644765167 367307018040242643967147751)
    ·
      refine ⟨550960527060363965950721627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367307018040242643967147751 550960527060363965950721627)
      ·
        refine ⟨826440790590545948926082441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550960527060363965950721627 826440790590545948926082441)
        ·
          refine ⟨619830592942909461694561831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826440790590545948926082441 619830592942909461694561831)
          ·
            refine ⟨929745889414364192541842747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619830592942909461694561831 929745889414364192541842747)
            ·
              refine ⟨1394618834121546288812764121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 929745889414364192541842747 1394618834121546288812764121)
              ·
                refine ⟨1045964125591159716609573091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394618834121546288812764121 1045964125591159716609573091)
                ·
                  refine ⟨1568946188386739574914359637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045964125591159716609573091 1568946188386739574914359637)
                  ·
                    refine ⟨4596522036289276098381913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1568946188386739574914359637 4596522036289276098381913)
                    ·
                      refine ⟨3447391527216957073786435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4596522036289276098381913 3447391527216957073786435)
                      ·
                        rfl

theorem cell23_6713771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 10, 2].length) (baseStart_6713771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713771 prefixEnd_6713771 := by exact prefixLift 6713771
  have htrace : WordTrace (prefixWord ++ tailWord_6713771) baseStart_6713771 baseEnd_6713771 := by
    simpa [prefixWord, tailWord_6713771, baseEnd_6713771] using wordTrace_append hprefix tailTrace_6713771
  have hstable : (prefixWord ++ tailWord_6713771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713771).length < 2 ^ (prefixWord ++ tailWord_6713771).sum := by decide
  have hdescent : baseEnd_6713771 < baseStart_6713771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713841 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 1, 7]
def baseStart_6713841 : Nat := 118140960795 + 6713841 * 2 ^ 59
def prefixEnd_6713841 : Nat := 4983230072969 + 3 ^ 40 * 6713841 * 2
def baseEnd_6713841 : Nat := 1149142490287590599970371

theorem tailTrace_6713841 : CollatzResearch.WordTrace tailWord_6713841 prefixEnd_6713841 1149142490287590599970371 := by
  unfold tailWord_6713841
  simp only [CollatzResearch.WordTrace]
  refine ⟨244873898469908164599813377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163249265646605443066542251 244873898469908164599813377)
  ·
    refine ⟨183655423852431123449860033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244873898469908164599813377 183655423852431123449860033)
    ·
      refine ⟨137741567889323342587395025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183655423852431123449860033 137741567889323342587395025)
      ·
        refine ⟨103306175916992506940546269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137741567889323342587395025 103306175916992506940546269)
        ·
          refine ⟨38739815968872190102704851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103306175916992506940546269 38739815968872190102704851)
          ·
            refine ⟨58109723953308285154057277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38739815968872190102704851 58109723953308285154057277)
            ·
              refine ⟨21791146482490606932771479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58109723953308285154057277 21791146482490606932771479)
              ·
                refine ⟨32686719723735910399157219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21791146482490606932771479 32686719723735910399157219)
                ·
                  refine ⟨49030079585603865598735829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32686719723735910399157219 49030079585603865598735829)
                  ·
                    refine ⟨1149142490287590599970371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49030079585603865598735829 1149142490287590599970371)
                    ·
                      rfl

theorem cell23_6713841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_6713841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713841 prefixEnd_6713841 := by exact prefixLift 6713841
  have htrace : WordTrace (prefixWord ++ tailWord_6713841) baseStart_6713841 baseEnd_6713841 := by
    simpa [prefixWord, tailWord_6713841, baseEnd_6713841] using wordTrace_append hprefix tailTrace_6713841
  have hstable : (prefixWord ++ tailWord_6713841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713841).length < 2 ^ (prefixWord ++ tailWord_6713841).sum := by decide
  have hdescent : baseEnd_6713841 < baseStart_6713841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713862 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_6713862 : Nat := 118140960795 + 6713862 * 2 ^ 59
def prefixEnd_6713862 : Nat := 4983230072969 + 3 ^ 40 * 6713862 * 2
def baseEnd_6713862 : Nat := 383048694884057357527613

theorem tailTrace_6713862 : CollatzResearch.WordTrace tailWord_6713862 prefixEnd_6713862 383048694884057357527613 := by
  unfold tailWord_6713862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7652333262588502662072745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163249776268554723457551893 7652333262588502662072745)
  ·
    refine ⟨5739249946941376996554559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7652333262588502662072745 5739249946941376996554559)
    ·
      refine ⟨8608874920412065494831839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5739249946941376996554559 8608874920412065494831839)
      ·
        refine ⟨12913312380618098242247759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8608874920412065494831839 12913312380618098242247759)
        ·
          refine ⟨19369968570927147363371639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12913312380618098242247759 19369968570927147363371639)
          ·
            refine ⟨29054952856390721045057459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19369968570927147363371639 29054952856390721045057459)
            ·
              refine ⟨43582429284586081567586189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29054952856390721045057459 43582429284586081567586189)
              ·
                refine ⟨16343410981719780587844821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43582429284586081567586189 16343410981719780587844821)
                ·
                  refine ⟨383048694884057357527613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16343410981719780587844821 383048694884057357527613)
                  ·
                    rfl

theorem cell23_6713862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_6713862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713862 prefixEnd_6713862 := by exact prefixLift 6713862
  have htrace : WordTrace (prefixWord ++ tailWord_6713862) baseStart_6713862 baseEnd_6713862 := by
    simpa [prefixWord, tailWord_6713862, baseEnd_6713862] using wordTrace_append hprefix tailTrace_6713862
  have hstable : (prefixWord ++ tailWord_6713862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713862).length < 2 ^ (prefixWord ++ tailWord_6713862).sum := by decide
  have hdescent : baseEnd_6713862 < baseStart_6713862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713973 : List Nat := [1, 3, 4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_6713973 : Nat := 118140960795 + 6713973 * 2 ^ 59
def prefixEnd_6713973 : Nat := 4983230072969 + 3 ^ 40 * 6713973 * 2
def baseEnd_6713973 : Nat := 1149165083436388427820169

theorem tailTrace_6713973 : CollatzResearch.WordTrace tailWord_6713973 prefixEnd_6713973 1149165083436388427820169 := by
  unfold tailWord_6713973
  simp only [CollatzResearch.WordTrace]
  refine ⟨244878712905429951143618573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163252475270286634095745715 244878712905429951143618573)
  ·
    refine ⟨91829517339536231678856965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244878712905429951143618573 91829517339536231678856965)
    ·
      refine ⟨17218034501163043439785681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91829517339536231678856965 17218034501163043439785681)
      ·
        refine ⟨12913525875872282579839261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17218034501163043439785681 12913525875872282579839261)
        ·
          refine ⟨4842572203452105967439723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12913525875872282579839261 4842572203452105967439723)
          ·
            refine ⟨7263858305178158951159585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842572203452105967439723 7263858305178158951159585)
            ·
              refine ⟨5447893728883619213369689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7263858305178158951159585 5447893728883619213369689)
              ·
                refine ⟨4085920296662714410027267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447893728883619213369689 4085920296662714410027267)
                ·
                  refine ⟨6128880444994071615040901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085920296662714410027267 6128880444994071615040901)
                  ·
                    refine ⟨1149165083436388427820169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6128880444994071615040901 1149165083436388427820169)
                    ·
                      rfl

theorem cell23_6713973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_6713973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713973 prefixEnd_6713973 := by exact prefixLift 6713973
  have htrace : WordTrace (prefixWord ++ tailWord_6713973) baseStart_6713973 baseEnd_6713973 := by
    simpa [prefixWord, tailWord_6713973, baseEnd_6713973] using wordTrace_append hprefix tailTrace_6713973
  have hstable : (prefixWord ++ tailWord_6713973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713973).length < 2 ^ (prefixWord ++ tailWord_6713973).sum := by decide
  have hdescent : baseEnd_6713973 < baseStart_6713973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6713978 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_6713978 : Nat := 118140960795 + 6713978 * 2 ^ 59
def prefixEnd_6713978 : Nat := 4983230072969 + 3 ^ 40 * 6713978 * 2
def baseEnd_6713978 : Nat := 1149165939237479254632661

theorem tailTrace_6713978 : CollatzResearch.WordTrace tailWord_6713978 prefixEnd_6713978 1149165939237479254632661 := by
  unfold tailWord_6713978
  simp only [CollatzResearch.WordTrace]
  refine ⟨61219723817602959249387647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163252596846941224665033725 61219723817602959249387647)
  ·
    refine ⟨91829585726404438874081471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61219723817602959249387647 91829585726404438874081471)
    ·
      refine ⟨137744378589606658311122207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91829585726404438874081471 137744378589606658311122207)
      ·
        refine ⟨206616567884409987466683311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137744378589606658311122207 206616567884409987466683311)
        ·
          refine ⟨309924851826614981200024967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206616567884409987466683311 309924851826614981200024967)
          ·
            refine ⟨464887277739922471800037451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309924851826614981200024967 464887277739922471800037451)
            ·
              refine ⟨697330916609883707700056177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464887277739922471800037451 697330916609883707700056177)
              ·
                refine ⟨522998187457412780775042133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697330916609883707700056177 522998187457412780775042133)
                ·
                  refine ⟨6128885009266556024707525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 522998187457412780775042133 6128885009266556024707525)
                  ·
                    refine ⟨1149165939237479254632661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6128885009266556024707525 1149165939237479254632661)
                    ·
                      rfl

theorem cell23_6713978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_6713978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6713978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6713978 prefixEnd_6713978 := by exact prefixLift 6713978
  have htrace : WordTrace (prefixWord ++ tailWord_6713978) baseStart_6713978 baseEnd_6713978 := by
    simpa [prefixWord, tailWord_6713978, baseEnd_6713978] using wordTrace_append hprefix tailTrace_6713978
  have hstable : (prefixWord ++ tailWord_6713978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6713978).length < 2 ^ (prefixWord ++ tailWord_6713978).sum := by decide
  have hdescent : baseEnd_6713978 < baseStart_6713978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6713978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714029 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_6714029 : Nat := 118140960795 + 6714029 * 2 ^ 59
def prefixEnd_6714029 : Nat := 4983230072969 + 3 ^ 40 * 6714029 * 2
def baseEnd_6714029 : Nat := 1149174668408605688120083

theorem tailTrace_6714029 : CollatzResearch.WordTrace tailWord_6714029 prefixEnd_6714029 1149174668408605688120083 := by
  unfold tailWord_6714029
  simp only [CollatzResearch.WordTrace]
  refine ⟨244880755393227072707657141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163253836928818048471771427 244880755393227072707657141)
  ·
    refine ⟨22957570818115038066342857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244880755393227072707657141 22957570818115038066342857)
    ·
      refine ⟨17218178113586278549757143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22957570818115038066342857 17218178113586278549757143)
      ·
        refine ⟨25827267170379417824635715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17218178113586278549757143 25827267170379417824635715)
        ·
          refine ⟨38740900755569126736953573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25827267170379417824635715 38740900755569126736953573)
          ·
            refine ⟨7263918891669211263178795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38740900755569126736953573 7263918891669211263178795)
            ·
              refine ⟨10895878337503816894768193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7263918891669211263178795 10895878337503816894768193)
              ·
                refine ⟨8171908753127862671076145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10895878337503816894768193 8171908753127862671076145)
                ·
                  refine ⟨6128931564845897003307109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8171908753127862671076145 6128931564845897003307109)
                  ·
                    refine ⟨1149174668408605688120083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6128931564845897003307109 1149174668408605688120083)
                    ·
                      rfl

theorem cell23_6714029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_6714029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714029 prefixEnd_6714029 := by exact prefixLift 6714029
  have htrace : WordTrace (prefixWord ++ tailWord_6714029) baseStart_6714029 baseEnd_6714029 := by
    simpa [prefixWord, tailWord_6714029, baseEnd_6714029] using wordTrace_append hprefix tailTrace_6714029
  have hstable : (prefixWord ++ tailWord_6714029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714029).length < 2 ^ (prefixWord ++ tailWord_6714029).sum := by decide
  have hdescent : baseEnd_6714029 < baseStart_6714029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714052 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_6714052 : Nat := 118140960795 + 6714052 * 2 ^ 59
def prefixEnd_6714052 : Nat := 4983230072969 + 3 ^ 40 * 6714052 * 2
def baseEnd_6714052 : Nat := 3447535815280870474372643

theorem tailTrace_6714052 : CollatzResearch.WordTrace tailWord_6714052 prefixEnd_6714052 3447535815280870474372643 := by
  unfold tailWord_6714052
  simp only [CollatzResearch.WordTrace]
  refine ⟨122440797136071873817872205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163254396181429165090496273 122440797136071873817872205)
  ·
    refine ⟨45915298926026952681702077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122440797136071873817872205 45915298926026952681702077)
    ·
      refine ⟨17218237097260107255638279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45915298926026952681702077 17218237097260107255638279)
      ·
        refine ⟨25827355645890160883457419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17218237097260107255638279 25827355645890160883457419)
        ·
          refine ⟨38741033468835241325186129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25827355645890160883457419 38741033468835241325186129)
          ·
            refine ⟨29055775101626430993889597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38741033468835241325186129 29055775101626430993889597)
            ·
              refine ⟨10895915663109911622708599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29055775101626430993889597 10895915663109911622708599)
              ·
                refine ⟨16343873494664867434062899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10895915663109911622708599 16343873494664867434062899)
                ·
                  refine ⟨24515810241997301151094349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16343873494664867434062899 24515810241997301151094349)
                  ·
                    refine ⟨9193428840748987931660381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24515810241997301151094349 9193428840748987931660381)
                    ·
                      refine ⟨3447535815280870474372643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9193428840748987931660381 3447535815280870474372643)
                      ·
                        rfl

theorem cell23_6714052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_6714052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714052 prefixEnd_6714052 := by exact prefixLift 6714052
  have htrace : WordTrace (prefixWord ++ tailWord_6714052) baseStart_6714052 baseEnd_6714052 := by
    simpa [prefixWord, tailWord_6714052, baseEnd_6714052] using wordTrace_append hprefix tailTrace_6714052
  have hstable : (prefixWord ++ tailWord_6714052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714052).length < 2 ^ (prefixWord ++ tailWord_6714052).sum := by decide
  have hdescent : baseEnd_6714052 < baseStart_6714052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714109 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_6714109 : Nat := 118140960795 + 6714109 * 2 ^ 59
def prefixEnd_6714109 : Nat := 4983230072969 + 3 ^ 40 * 6714109 * 2
def baseEnd_6714109 : Nat := 3447565083678176751359881

theorem tailTrace_6714109 : CollatzResearch.WordTrace tailWord_6714109 prefixEnd_6714109 3447565083678176751359881 := by
  unfold tailWord_6714109
  simp only [CollatzResearch.WordTrace]
  refine ⟨244883673232937246370569381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163255782155291497580379587 244883673232937246370569381)
  ·
    refine ⟨45915688731175733694481759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244883673232937246370569381 45915688731175733694481759)
    ·
      refine ⟨68873533096763600541722639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45915688731175733694481759 68873533096763600541722639)
      ·
        refine ⟨103310299645145400812583959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68873533096763600541722639 103310299645145400812583959)
        ·
          refine ⟨154965449467718101218875939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103310299645145400812583959 154965449467718101218875939)
          ·
            refine ⟨232448174201577151828313909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154965449467718101218875939 232448174201577151828313909)
            ·
              refine ⟨21792016331397857983904429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232448174201577151828313909 21792016331397857983904429)
              ·
                refine ⟨8172006124274196743964161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21792016331397857983904429 8172006124274196743964161)
                ·
                  refine ⟨6129004593205647557973121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8172006124274196743964161 6129004593205647557973121)
                  ·
                    refine ⟨4596753444904235668479841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6129004593205647557973121 4596753444904235668479841)
                    ·
                      refine ⟨3447565083678176751359881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4596753444904235668479841 3447565083678176751359881)
                      ·
                        rfl

theorem cell23_6714109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_6714109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714109 prefixEnd_6714109 := by exact prefixLift 6714109
  have htrace : WordTrace (prefixWord ++ tailWord_6714109) baseStart_6714109 baseEnd_6714109 := by
    simpa [prefixWord, tailWord_6714109, baseEnd_6714109] using wordTrace_append hprefix tailTrace_6714109
  have hstable : (prefixWord ++ tailWord_6714109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714109).length < 2 ^ (prefixWord ++ tailWord_6714109).sum := by decide
  have hdescent : baseEnd_6714109 < baseStart_6714109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714145 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 2, 5]
def baseStart_6714145 : Nat := 118140960795 + 6714145 * 2 ^ 59
def prefixEnd_6714145 : Nat := 4983230072969 + 3 ^ 40 * 6714145 * 2
def baseEnd_6714145 : Nat := 1149194522993912870169905

theorem tailTrace_6714145 : CollatzResearch.WordTrace tailWord_6714145 prefixEnd_6714145 1149194522993912870169905 := by
  unfold tailWord_6714145
  simp only [CollatzResearch.WordTrace]
  refine ⟨244884986260806824518879889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163256657507204549679253259 244884986260806824518879889)
  ·
    refine ⟨183663739695605118389159917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244884986260806824518879889 183663739695605118389159917)
    ·
      refine ⟨68873902385851919395934969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183663739695605118389159917 68873902385851919395934969)
      ·
        refine ⟨51655426789388939546951227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68873902385851919395934969 51655426789388939546951227)
        ·
          refine ⟨77483140184083409320426841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51655426789388939546951227 77483140184083409320426841)
          ·
            refine ⟨58112355138062556990320131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77483140184083409320426841 58112355138062556990320131)
            ·
              refine ⟨87168532707093835485480197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58112355138062556990320131 87168532707093835485480197)
              ·
                refine ⟨16344099882580094153527537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87168532707093835485480197 16344099882580094153527537)
                ·
                  refine ⟨12258074911935070615145653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16344099882580094153527537 12258074911935070615145653)
                  ·
                    refine ⟨1149194522993912870169905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12258074911935070615145653 1149194522993912870169905)
                    ·
                      rfl

theorem cell23_6714145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_6714145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714145 prefixEnd_6714145 := by exact prefixLift 6714145
  have htrace : WordTrace (prefixWord ++ tailWord_6714145) baseStart_6714145 baseEnd_6714145 := by
    simpa [prefixWord, tailWord_6714145, baseEnd_6714145] using wordTrace_append hprefix tailTrace_6714145
  have hstable : (prefixWord ++ tailWord_6714145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714145).length < 2 ^ (prefixWord ++ tailWord_6714145).sum := by decide
  have hdescent : baseEnd_6714145 < baseStart_6714145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714152 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_6714152 : Nat := 118140960795 + 6714152 * 2 ^ 59
def prefixEnd_6714152 : Nat := 4983230072969 + 3 ^ 40 * 6714152 * 2
def baseEnd_6714152 : Nat := 3447587163346320083122183

theorem tailTrace_6714152 : CollatzResearch.WordTrace tailWord_6714152 prefixEnd_6714152 3447587163346320083122183 := by
  unfold tailWord_6714152
  simp only [CollatzResearch.WordTrace]
  refine ⟨122442620785890732357192355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163256827714520976476256473 122442620785890732357192355)
  ·
    refine ⟨183663931178836098535788533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122442620785890732357192355 183663931178836098535788533)
    ·
      refine ⟨17218493548015884237730175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183663931178836098535788533 17218493548015884237730175)
      ·
        refine ⟨25827740322023826356595263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17218493548015884237730175 25827740322023826356595263)
        ·
          refine ⟨38741610483035739534892895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25827740322023826356595263 38741610483035739534892895)
          ·
            refine ⟨58112415724553609302339343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38741610483035739534892895 58112415724553609302339343)
            ·
              refine ⟨87168623586830413953509015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58112415724553609302339343 87168623586830413953509015)
              ·
                refine ⟨130752935380245620930263523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87168623586830413953509015 130752935380245620930263523)
                ·
                  refine ⟨196129403070368431395395285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130752935380245620930263523 196129403070368431395395285)
                  ·
                    refine ⟨4596782884461760110829577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 196129403070368431395395285 4596782884461760110829577)
                    ·
                      refine ⟨3447587163346320083122183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4596782884461760110829577 3447587163346320083122183)
                      ·
                        rfl

theorem cell23_6714152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_6714152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714152 prefixEnd_6714152 := by exact prefixLift 6714152
  have htrace : WordTrace (prefixWord ++ tailWord_6714152) baseStart_6714152 baseEnd_6714152 := by
    simpa [prefixWord, tailWord_6714152, baseEnd_6714152] using wordTrace_append hprefix tailTrace_6714152
  have hstable : (prefixWord ++ tailWord_6714152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714152).length < 2 ^ (prefixWord ++ tailWord_6714152).sum := by decide
  have hdescent : baseEnd_6714152 < baseStart_6714152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714232 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 5, 1, 3]
def baseStart_6714232 : Nat := 118140960795 + 6714232 * 2 ^ 59
def prefixEnd_6714232 : Nat := 4983230072969 + 3 ^ 40 * 6714232 * 2
def baseEnd_6714232 : Nat := 3447628241798679770121815

theorem tailTrace_6714232 : CollatzResearch.WordTrace tailWord_6714232 prefixEnd_6714232 3447628241798679770121815 := by
  unfold tailWord_6714232
  simp only [CollatzResearch.WordTrace]
  refine ⟨122444079705745819188648475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163258772940994425584864633 122444079705745819188648475)
  ·
    refine ⟨183666119558618728782972713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122444079705745819188648475 183666119558618728782972713)
    ·
      refine ⟨137749589668964046587229535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183666119558618728782972713 137749589668964046587229535)
      ·
        refine ⟨206624384503446069880844303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137749589668964046587229535 206624384503446069880844303)
        ·
          refine ⟨309936576755169104821266455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206624384503446069880844303 309936576755169104821266455)
          ·
            refine ⟨464904865132753657231899683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309936576755169104821266455 464904865132753657231899683)
            ·
              refine ⟨697357297699130485847849525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464904865132753657231899683 697357297699130485847849525)
              ·
                refine ⟨65377246659293483048235893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 697357297699130485847849525 65377246659293483048235893)
                ·
                  refine ⟨6129116874308764035772115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65377246659293483048235893 6129116874308764035772115)
                  ·
                    refine ⟨9193675311463146053658173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6129116874308764035772115 9193675311463146053658173)
                    ·
                      refine ⟨3447628241798679770121815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9193675311463146053658173 3447628241798679770121815)
                      ·
                        rfl

theorem cell23_6714232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_6714232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714232 prefixEnd_6714232 := by exact prefixLift 6714232
  have htrace : WordTrace (prefixWord ++ tailWord_6714232) baseStart_6714232 baseEnd_6714232 := by
    simpa [prefixWord, tailWord_6714232, baseEnd_6714232] using wordTrace_append hprefix tailTrace_6714232
  have hstable : (prefixWord ++ tailWord_6714232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714232).length < 2 ^ (prefixWord ++ tailWord_6714232).sum := by decide
  have hdescent : baseEnd_6714232 < baseStart_6714232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714235 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 3, 5]
def baseStart_6714235 : Nat := 118140960795 + 6714235 * 2 ^ 59
def prefixEnd_6714235 : Nat := 4983230072969 + 3 ^ 40 * 6714235 * 2
def baseEnd_6714235 : Nat := 1149209927413547752794767

theorem tailTrace_6714235 : CollatzResearch.WordTrace tailWord_6714235 prefixEnd_6714235 1149209927413547752794767 := by
  unfold tailWord_6714235
  simp only [CollatzResearch.WordTrace]
  refine ⟨244888268830480769889656159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163258845886987179926437439 244888268830480769889656159)
  ·
    refine ⟨367332403245721154834484239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244888268830480769889656159 367332403245721154834484239)
    ·
      refine ⟨550998604868581732251726359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367332403245721154834484239 550998604868581732251726359)
      ·
        refine ⟨826497907302872598377589539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550998604868581732251726359 826497907302872598377589539)
        ·
          refine ⟨1239746860954308897566384309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 826497907302872598377589539 1239746860954308897566384309)
          ·
            refine ⟨116226268214466459146848529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1239746860954308897566384309 116226268214466459146848529)
            ·
              refine ⟨87169701160849844360136397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116226268214466459146848529 87169701160849844360136397)
              ·
                refine ⟨32688637935318691635051149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87169701160849844360136397 32688637935318691635051149)
                ·
                  refine ⟨12258239225744509363144181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32688637935318691635051149 12258239225744509363144181)
                  ·
                    refine ⟨1149209927413547752794767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12258239225744509363144181 1149209927413547752794767)
                    ·
                      rfl

theorem cell23_6714235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 5].length) (baseStart_6714235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714235 prefixEnd_6714235 := by exact prefixLift 6714235
  have htrace : WordTrace (prefixWord ++ tailWord_6714235) baseStart_6714235 baseEnd_6714235 := by
    simpa [prefixWord, tailWord_6714235, baseEnd_6714235] using wordTrace_append hprefix tailTrace_6714235
  have hstable : (prefixWord ++ tailWord_6714235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714235).length < 2 ^ (prefixWord ++ tailWord_6714235).sum := by decide
  have hdescent : baseEnd_6714235 < baseStart_6714235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714252 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_6714252 : Nat := 118140960795 + 6714252 * 2 ^ 59
def prefixEnd_6714252 : Nat := 4983230072969 + 3 ^ 40 * 6714252 * 2
def baseEnd_6714252 : Nat := 1149212837137256563957241

theorem tailTrace_6714252 : CollatzResearch.WordTrace tailWord_6714252 prefixEnd_6714252 1149212837137256563957241 := by
  unfold tailWord_6714252
  simp only [CollatzResearch.WordTrace]
  refine ⟨122444444435709590896512505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163259259247612787862016673 122444444435709590896512505)
  ·
    refine ⟨91833333326782193172384379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122444444435709590896512505 91833333326782193172384379)
    ·
      refine ⟨137749999990173289758576569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91833333326782193172384379 137749999990173289758576569)
      ·
        refine ⟨103312499992629967318932427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137749999990173289758576569 103312499992629967318932427)
        ·
          refine ⟨154968749988944950978398641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103312499992629967318932427 154968749988944950978398641)
          ·
            refine ⟨116226562491708713233798981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154968749988944950978398641 116226562491708713233798981)
            ·
              refine ⟨21792480467195383731337309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116226562491708713233798981 21792480467195383731337309)
              ·
                refine ⟨8172180175198268899251491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21792480467195383731337309 8172180175198268899251491)
                ·
                  refine ⟨12258270262797403348877237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8172180175198268899251491 12258270262797403348877237)
                  ·
                    refine ⟨1149212837137256563957241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12258270262797403348877237 1149212837137256563957241)
                    ·
                      rfl

theorem cell23_6714252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_6714252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714252 prefixEnd_6714252 := by exact prefixLift 6714252
  have htrace : WordTrace (prefixWord ++ tailWord_6714252) baseStart_6714252 baseEnd_6714252 := by
    simpa [prefixWord, tailWord_6714252, baseEnd_6714252] using wordTrace_append hprefix tailTrace_6714252
  have hstable : (prefixWord ++ tailWord_6714252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714252).length < 2 ^ (prefixWord ++ tailWord_6714252).sum := by decide
  have hdescent : baseEnd_6714252 < baseStart_6714252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714289 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_6714289 : Nat := 118140960795 + 6714289 * 2 ^ 59
def prefixEnd_6714289 : Nat := 4983230072969 + 3 ^ 40 * 6714289 * 2
def baseEnd_6714289 : Nat := 3447657510195986047109053

theorem tailTrace_6714289 : CollatzResearch.WordTrace tailWord_6714289 prefixEnd_6714289 3447657510195986047109053 := by
  unfold tailWord_6714289
  simp only [CollatzResearch.WordTrace]
  refine ⟨244890238372285137112121921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163260158914856758074747947 244890238372285137112121921)
  ·
    refine ⟨183667678779213852834091441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244890238372285137112121921 183667678779213852834091441)
    ·
      refine ⟨137750759084410389625568581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183667678779213852834091441 137750759084410389625568581)
      ·
        refine ⟨25828267328326948054794109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137750759084410389625568581 25828267328326948054794109)
        ·
          refine ⟨9685600248122605520547791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25828267328326948054794109 9685600248122605520547791)
          ·
            refine ⟨14528400372183908280821687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9685600248122605520547791 14528400372183908280821687)
            ·
              refine ⟨21792600558275862421232531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14528400372183908280821687 21792600558275862421232531)
              ·
                refine ⟨32688900837413793631848797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21792600558275862421232531 32688900837413793631848797)
                ·
                  refine ⟨12258337814030172611943299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32688900837413793631848797 12258337814030172611943299)
                  ·
                    refine ⟨18387506721045258917914949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12258337814030172611943299 18387506721045258917914949)
                    ·
                      refine ⟨3447657510195986047109053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18387506721045258917914949 3447657510195986047109053)
                      ·
                        rfl

theorem cell23_6714289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_6714289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714289 prefixEnd_6714289 := by exact prefixLift 6714289
  have htrace : WordTrace (prefixWord ++ tailWord_6714289) baseStart_6714289 baseEnd_6714289 := by
    simpa [prefixWord, tailWord_6714289, baseEnd_6714289] using wordTrace_append hprefix tailTrace_6714289
  have hstable : (prefixWord ++ tailWord_6714289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714289).length < 2 ^ (prefixWord ++ tailWord_6714289).sum := by decide
  have hdescent : baseEnd_6714289 < baseStart_6714289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714295 : List Nat := [1, 1, 3, 1, 3, 1, 4, 9]
def baseStart_6714295 : Nat := 118140960795 + 6714295 * 2 ^ 59
def prefixEnd_6714295 : Nat := 4983230072969 + 3 ^ 40 * 6714295 * 2
def baseEnd_6714295 : Nat := 127691133002959741616075

theorem tailTrace_6714295 : CollatzResearch.WordTrace tailWord_6714295 prefixEnd_6714295 127691133002959741616075 := by
  unfold tailWord_6714295
  simp only [CollatzResearch.WordTrace]
  refine ⟨244890457210263400136840339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163260304806842266757893559 244890457210263400136840339)
  ·
    refine ⟨367335685815395100205260509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244890457210263400136840339 367335685815395100205260509)
    ·
      refine ⟨137750882180773162576972691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367335685815395100205260509 137750882180773162576972691)
      ·
        refine ⟨206626323271159743865459037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137750882180773162576972691 206626323271159743865459037)
        ·
          refine ⟨77484871226684903949547139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206626323271159743865459037 77484871226684903949547139)
          ·
            refine ⟨116227306840027355924320709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77484871226684903949547139 116227306840027355924320709)
            ·
              refine ⟨21792620032505129235810133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116227306840027355924320709 21792620032505129235810133)
              ·
                refine ⟨127691133002959741616075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21792620032505129235810133 127691133002959741616075)
                ·
                  rfl

theorem cell23_6714295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 9].length) (baseStart_6714295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714295 prefixEnd_6714295 := by exact prefixLift 6714295
  have htrace : WordTrace (prefixWord ++ tailWord_6714295) baseStart_6714295 baseEnd_6714295 := by
    simpa [prefixWord, tailWord_6714295, baseEnd_6714295] using wordTrace_append hprefix tailTrace_6714295
  have hstable : (prefixWord ++ tailWord_6714295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714295).length < 2 ^ (prefixWord ++ tailWord_6714295).sum := by decide
  have hdescent : baseEnd_6714295 < baseStart_6714295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714312 : List Nat := [2, 1, 3, 1, 6, 10]
def baseStart_6714312 : Nat := 118140960795 + 6714312 * 2 ^ 59
def prefixEnd_6714312 : Nat := 4983230072969 + 3 ^ 40 * 6714312 * 2
def baseEnd_6714312 : Nat := 14187939589510450440829

theorem tailTrace_6714312 : CollatzResearch.WordTrace tailWord_6714312 prefixEnd_6714312 14187939589510450440829 := by
  unfold tailWord_6714312
  simp only [CollatzResearch.WordTrace]
  refine ⟨122445538625600906020104595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163260718167467874693472793 122445538625600906020104595)
  ·
    refine ⟨183668307938401359030156893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122445538625600906020104595 183668307938401359030156893)
    ·
      refine ⟨68875615476900509636308835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183668307938401359030156893 68875615476900509636308835)
      ·
        refine ⟨103313423215350764454463253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68875615476900509636308835 103313423215350764454463253)
        ·
          refine ⟨4842816713219567083802965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103313423215350764454463253 4842816713219567083802965)
          ·
            refine ⟨14187939589510450440829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4842816713219567083802965 14187939589510450440829)
            ·
              rfl

theorem cell23_6714312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 10].length) (baseStart_6714312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714312 prefixEnd_6714312 := by exact prefixLift 6714312
  have htrace : WordTrace (prefixWord ++ tailWord_6714312) baseStart_6714312 baseEnd_6714312 := by
    simpa [prefixWord, tailWord_6714312, baseEnd_6714312] using wordTrace_append hprefix tailTrace_6714312
  have hstable : (prefixWord ++ tailWord_6714312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714312).length < 2 ^ (prefixWord ++ tailWord_6714312).sum := by decide
  have hdescent : baseEnd_6714312 < baseStart_6714312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714326 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_6714326 : Nat := 118140960795 + 6714326 * 2 ^ 59
def prefixEnd_6714326 : Nat := 4983230072969 + 3 ^ 40 * 6714326 * 2
def baseEnd_6714326 : Nat := 3447676508980202402346383

theorem tailTrace_6714326 : CollatzResearch.WordTrace tailWord_6714326 prefixEnd_6714326 3447676508980202402346383 := by
  unfold tailWord_6714326
  simp only [CollatzResearch.WordTrace]
  refine ⟨15305724242071943276951177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163261058582100728287479221 15305724242071943276951177)
  ·
    refine ⟨11479293181553957457713383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15305724242071943276951177 11479293181553957457713383)
    ·
      refine ⟨17218939772330936186570075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11479293181553957457713383 17218939772330936186570075)
      ·
        refine ⟨25828409658496404279855113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17218939772330936186570075 25828409658496404279855113)
        ·
          refine ⟨19371307243872303209891335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25828409658496404279855113 19371307243872303209891335)
          ·
            refine ⟨29056960865808454814837003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19371307243872303209891335 29056960865808454814837003)
            ·
              refine ⟨43585441298712682222255505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29056960865808454814837003 43585441298712682222255505)
              ·
                refine ⟨32689080974034511666691629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43585441298712682222255505 32689080974034511666691629)
                ·
                  refine ⟨12258405365262941875009361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32689080974034511666691629 12258405365262941875009361)
                  ·
                    refine ⟨9193804023947206406257021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12258405365262941875009361 9193804023947206406257021)
                    ·
                      refine ⟨3447676508980202402346383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9193804023947206406257021 3447676508980202402346383)
                      ·
                        rfl

theorem cell23_6714326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_6714326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714326 prefixEnd_6714326 := by exact prefixLift 6714326
  have htrace : WordTrace (prefixWord ++ tailWord_6714326) baseStart_6714326 baseEnd_6714326 := by
    simpa [prefixWord, tailWord_6714326, baseEnd_6714326] using wordTrace_append hprefix tailTrace_6714326
  have hstable : (prefixWord ++ tailWord_6714326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714326).length < 2 ^ (prefixWord ++ tailWord_6714326).sum := by decide
  have hdescent : baseEnd_6714326 < baseStart_6714326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714339 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 3]
def baseStart_6714339 : Nat := 118140960795 + 6714339 * 2 ^ 59
def prefixEnd_6714339 : Nat := 4983230072969 + 3 ^ 40 * 6714339 * 2
def baseEnd_6714339 : Nat := 3447683184228710851483823

theorem tailTrace_6714339 : CollatzResearch.WordTrace tailWord_6714339 prefixEnd_6714339 3447683184228710851483823 := by
  unfold tailWord_6714339
  simp only [CollatzResearch.WordTrace]
  refine ⟨244892062022103995651442071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163261374681402663767628047 244892062022103995651442071)
  ·
    refine ⟨367338093033155993477163107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244892062022103995651442071 367338093033155993477163107)
    ·
      refine ⟨551007139549733990215744661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367338093033155993477163107 551007139549733990215744661)
      ·
        refine ⟨25828459666393780791363031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 551007139549733990215744661 25828459666393780791363031)
        ·
          refine ⟨38742689499590671187044547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25828459666393780791363031 38742689499590671187044547)
          ·
            refine ⟨58114034249386006780566821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38742689499590671187044547 58114034249386006780566821)
            ·
              refine ⟨10896381421759876271356279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58114034249386006780566821 10896381421759876271356279)
              ·
                refine ⟨16344572132639814407034419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10896381421759876271356279 16344572132639814407034419)
                ·
                  refine ⟨24516858198959721610551629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16344572132639814407034419 24516858198959721610551629)
                  ·
                    refine ⟨9193821824609895603956861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24516858198959721610551629 9193821824609895603956861)
                    ·
                      refine ⟨3447683184228710851483823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9193821824609895603956861 3447683184228710851483823)
                      ·
                        rfl

theorem cell23_6714339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_6714339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714339 prefixEnd_6714339 := by exact prefixLift 6714339
  have htrace : WordTrace (prefixWord ++ tailWord_6714339) baseStart_6714339 baseEnd_6714339 := by
    simpa [prefixWord, tailWord_6714339, baseEnd_6714339] using wordTrace_append hprefix tailTrace_6714339
  have hstable : (prefixWord ++ tailWord_6714339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714339).length < 2 ^ (prefixWord ++ tailWord_6714339).sum := by decide
  have hdescent : baseEnd_6714339 < baseStart_6714339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714357 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6714357 : Nat := 118140960795 + 6714357 * 2 ^ 59
def prefixEnd_6714357 : Nat := 4983230072969 + 3 ^ 40 * 6714357 * 2
def baseEnd_6714357 : Nat := 3447692426880491781058741

theorem tailTrace_6714357 : CollatzResearch.WordTrace tailWord_6714357 prefixEnd_6714357 3447692426880491781058741 := by
  unfold tailWord_6714357
  simp only [CollatzResearch.WordTrace]
  refine ⟨244892718536038784725597325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163261812357359189817064883 244892718536038784725597325)
  ·
    refine ⟨91834769451014544272098997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244892718536038784725597325 91834769451014544272098997)
    ·
      refine ⟨8609509636032613525509281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91834769451014544272098997 8609509636032613525509281)
      ·
        refine ⟨6457132227024460144131961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8609509636032613525509281 6457132227024460144131961)
        ·
          refine ⟨4842849170268345108098971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6457132227024460144131961 4842849170268345108098971)
          ·
            refine ⟨7264273755402517662148457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842849170268345108098971 7264273755402517662148457)
            ·
              refine ⟨5448205316551888246611343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7264273755402517662148457 5448205316551888246611343)
              ·
                refine ⟨8172307974827832369917015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448205316551888246611343 8172307974827832369917015)
                ·
                  refine ⟨12258461962241748554875523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8172307974827832369917015 12258461962241748554875523)
                  ·
                    refine ⟨18387692943362622832313285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12258461962241748554875523 18387692943362622832313285)
                    ·
                      refine ⟨3447692426880491781058741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18387692943362622832313285 3447692426880491781058741)
                      ·
                        rfl

theorem cell23_6714357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6714357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714357 prefixEnd_6714357 := by exact prefixLift 6714357
  have htrace : WordTrace (prefixWord ++ tailWord_6714357) baseStart_6714357 baseEnd_6714357 := by
    simpa [prefixWord, tailWord_6714357, baseEnd_6714357] using wordTrace_append hprefix tailTrace_6714357
  have hstable : (prefixWord ++ tailWord_6714357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714357).length < 2 ^ (prefixWord ++ tailWord_6714357).sum := by decide
  have hdescent : baseEnd_6714357 < baseStart_6714357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714400 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6714400 : Nat := 118140960795 + 6714400 * 2 ^ 59
def prefixEnd_6714400 : Nat := 4983230072969 + 3 ^ 40 * 6714400 * 2
def baseEnd_6714400 : Nat := 3447714506548635112821043

theorem tailTrace_6714400 : CollatzResearch.WordTrace tailWord_6714400 prefixEnd_6714400 3447714506548635112821043 := by
  unfold tailWord_6714400
  simp only [CollatzResearch.WordTrace]
  refine ⟨122447143437441501534706327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163262857916588668712941769 122447143437441501534706327)
  ·
    refine ⟨183670715156162252302059491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122447143437441501534706327 183670715156162252302059491)
    ·
      refine ⟨275506072734243378453089237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183670715156162252302059491 275506072734243378453089237)
      ·
        refine ⟨6457173579708829182494279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 275506072734243378453089237 6457173579708829182494279)
        ·
          refine ⟨9685760369563243773741419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6457173579708829182494279 9685760369563243773741419)
          ·
            refine ⟨14528640554344865660612129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9685760369563243773741419 14528640554344865660612129)
            ·
              refine ⟨10896480415758649245459097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14528640554344865660612129 10896480415758649245459097)
              ·
                refine ⟨8172360311818986934094323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10896480415758649245459097 8172360311818986934094323)
                ·
                  refine ⟨12258540467728480401141485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8172360311818986934094323 12258540467728480401141485)
                  ·
                    refine ⟨4596952675398180150428057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12258540467728480401141485 4596952675398180150428057)
                    ·
                      refine ⟨3447714506548635112821043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4596952675398180150428057 3447714506548635112821043)
                      ·
                        rfl

theorem cell23_6714400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6714400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714400 prefixEnd_6714400 := by exact prefixLift 6714400
  have htrace : WordTrace (prefixWord ++ tailWord_6714400) baseStart_6714400 baseEnd_6714400 := by
    simpa [prefixWord, tailWord_6714400, baseEnd_6714400] using wordTrace_append hprefix tailTrace_6714400
  have hstable : (prefixWord ++ tailWord_6714400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714400).length < 2 ^ (prefixWord ++ tailWord_6714400).sum := by decide
  have hdescent : baseEnd_6714400 < baseStart_6714400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714442 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_6714442 : Nat := 118140960795 + 6714442 * 2 ^ 59
def prefixEnd_6714442 : Nat := 4983230072969 + 3 ^ 40 * 6714442 * 2
def baseEnd_6714442 : Nat := 3447736072736123948495849

theorem tailTrace_6714442 : CollatzResearch.WordTrace tailWord_6714442 prefixEnd_6714442 3447736072736123948495849 := by
  unfold tailWord_6714442
  simp only [CollatzResearch.WordTrace]
  refine ⟨61223954685182711060610395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163263879160487229494961053 61223954685182711060610395)
  ·
    refine ⟨91835932027774066590915593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61223954685182711060610395 91835932027774066590915593)
    ·
      refine ⟨68876949020830549943186695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91835932027774066590915593 68876949020830549943186695)
      ·
        refine ⟨103315423531245824914780043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68876949020830549943186695 103315423531245824914780043)
        ·
          refine ⟨154973135296868737372170065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103315423531245824914780043 154973135296868737372170065)
          ·
            refine ⟨116229851472651553029127549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154973135296868737372170065 116229851472651553029127549)
            ·
              refine ⟨43586194302244332385922831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116229851472651553029127549 43586194302244332385922831)
              ·
                refine ⟨65379291453366498578884247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43586194302244332385922831 65379291453366498578884247)
                ·
                  refine ⟨98068937180049747868326371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65379291453366498578884247 98068937180049747868326371)
                  ·
                    refine ⟨147103405770074621802489557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98068937180049747868326371 147103405770074621802489557)
                    ·
                      refine ⟨3447736072736123948495849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147103405770074621802489557 3447736072736123948495849)
                      ·
                        rfl

theorem cell23_6714442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_6714442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714442 prefixEnd_6714442 := by exact prefixLift 6714442
  have htrace : WordTrace (prefixWord ++ tailWord_6714442) baseStart_6714442 baseEnd_6714442 := by
    simpa [prefixWord, tailWord_6714442, baseEnd_6714442] using wordTrace_append hprefix tailTrace_6714442
  have hstable : (prefixWord ++ tailWord_6714442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714442).length < 2 ^ (prefixWord ++ tailWord_6714442).sum := by decide
  have hdescent : baseEnd_6714442 < baseStart_6714442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714466 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_6714466 : Nat := 118140960795 + 6714466 * 2 ^ 59
def prefixEnd_6714466 : Nat := 4983230072969 + 3 ^ 40 * 6714466 * 2
def baseEnd_6714466 : Nat := 1149249465423943951531913

theorem tailTrace_6714466 : CollatzResearch.WordTrace tailWord_6714466 prefixEnd_6714466 1149249465423943951531913 := by
  unfold tailWord_6714466
  simp only [CollatzResearch.WordTrace]
  refine ⟨61224173523160974085328813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163264462728429264227543501 61224173523160974085328813)
  ·
    refine ⟨22959065071185365281998305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61224173523160974085328813 22959065071185365281998305)
    ·
      refine ⟨17219298803389023961498729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22959065071185365281998305 17219298803389023961498729)
      ·
        refine ⟨12914474102541767971124047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17219298803389023961498729 12914474102541767971124047)
        ·
          refine ⟨19371711153812651956686071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12914474102541767971124047 19371711153812651956686071)
          ·
            refine ⟨29057566730718977935029107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19371711153812651956686071 29057566730718977935029107)
            ·
              refine ⟨43586350096078466902543661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29057566730718977935029107 43586350096078466902543661)
              ·
                refine ⟨16344881286029425088453873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43586350096078466902543661 16344881286029425088453873)
                ·
                  refine ⟨12258660964522068816340405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16344881286029425088453873 12258660964522068816340405)
                  ·
                    refine ⟨1149249465423943951531913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12258660964522068816340405 1149249465423943951531913)
                    ·
                      rfl

theorem cell23_6714466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_6714466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714466 prefixEnd_6714466 := by exact prefixLift 6714466
  have htrace : WordTrace (prefixWord ++ tailWord_6714466) baseStart_6714466 baseEnd_6714466 := by
    simpa [prefixWord, tailWord_6714466, baseEnd_6714466] using wordTrace_append hprefix tailTrace_6714466
  have hstable : (prefixWord ++ tailWord_6714466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714466).length < 2 ^ (prefixWord ++ tailWord_6714466).sum := by decide
  have hdescent : baseEnd_6714466 < baseStart_6714466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714486 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6714486 : Nat := 118140960795 + 6714486 * 2 ^ 59
def prefixEnd_6714486 : Nat := 4983230072969 + 3 ^ 40 * 6714486 * 2
def baseEnd_6714486 : Nat := 3447758665884921776345647

theorem tailTrace_6714486 : CollatzResearch.WordTrace tailWord_6714486 prefixEnd_6714486 3447758665884921776345647 := by
  unfold tailWord_6714486
  simp only [CollatzResearch.WordTrace]
  refine ⟨15306088972035714984815207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163264949035047626504695541 15306088972035714984815207)
  ·
    refine ⟨22959133458053572477222811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15306088972035714984815207 22959133458053572477222811)
    ·
      refine ⟨34438700187080358715834217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22959133458053572477222811 34438700187080358715834217)
      ·
        refine ⟨25829025140310269036875663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34438700187080358715834217 25829025140310269036875663)
        ·
          refine ⟨38743537710465403555313495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25829025140310269036875663 38743537710465403555313495)
          ·
            refine ⟨58115306565698105332970243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38743537710465403555313495 58115306565698105332970243)
            ·
              refine ⟨87172959848547157999455365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58115306565698105332970243 87172959848547157999455365)
              ·
                refine ⟨16344929971602592124897881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87172959848547157999455365 16344929971602592124897881)
                ·
                  refine ⟨12258697478701944093673411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16344929971602592124897881 12258697478701944093673411)
                  ·
                    refine ⟨18388046218052916140510117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12258697478701944093673411 18388046218052916140510117)
                    ·
                      refine ⟨3447758665884921776345647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18388046218052916140510117 3447758665884921776345647)
                      ·
                        rfl

theorem cell23_6714486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6714486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714486 prefixEnd_6714486 := by exact prefixLift 6714486
  have htrace : WordTrace (prefixWord ++ tailWord_6714486) baseStart_6714486 baseEnd_6714486 := by
    simpa [prefixWord, tailWord_6714486, baseEnd_6714486] using wordTrace_append hprefix tailTrace_6714486
  have hstable : (prefixWord ++ tailWord_6714486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714486).length < 2 ^ (prefixWord ++ tailWord_6714486).sum := by decide
  have hdescent : baseEnd_6714486 < baseStart_6714486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714512 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_6714512 : Nat := 118140960795 + 6714512 * 2 ^ 59
def prefixEnd_6714512 : Nat := 4983230072969 + 3 ^ 40 * 6714512 * 2
def baseEnd_6714512 : Nat := 3447772016381938674620527

theorem tailTrace_6714512 : CollatzResearch.WordTrace tailWord_6714512 prefixEnd_6714512 3447772016381938674620527 := by
  unfold tailWord_6714512
  simp only [CollatzResearch.WordTrace]
  refine ⟨122449185925238623098744895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163265581233651497464993193 122449185925238623098744895)
  ·
    refine ⟨183673778887857934648117343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122449185925238623098744895 183673778887857934648117343)
    ·
      refine ⟨275510668331786901972176015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183673778887857934648117343 275510668331786901972176015)
      ·
        refine ⟨413266002497680352958264023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275510668331786901972176015 413266002497680352958264023)
        ·
          refine ⟨619899003746520529437396035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413266002497680352958264023 619899003746520529437396035)
          ·
            refine ⟨929848505619780794156094053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619899003746520529437396035 929848505619780794156094053)
            ·
              refine ⟨174346594803708898904267635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 929848505619780794156094053 174346594803708898904267635)
              ·
                refine ⟨261519892205563348356401453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174346594803708898904267635 261519892205563348356401453)
                ·
                  refine ⟨98069959577086255633650545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 261519892205563348356401453 98069959577086255633650545)
                  ·
                    refine ⟨73552469682814691725237909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98069959577086255633650545 73552469682814691725237909)
                    ·
                      refine ⟨3447772016381938674620527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73552469682814691725237909 3447772016381938674620527)
                      ·
                        rfl

theorem cell23_6714512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_6714512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714512 prefixEnd_6714512 := by exact prefixLift 6714512
  have htrace : WordTrace (prefixWord ++ tailWord_6714512) baseStart_6714512 baseEnd_6714512 := by
    simpa [prefixWord, tailWord_6714512, baseEnd_6714512] using wordTrace_append hprefix tailTrace_6714512
  have hstable : (prefixWord ++ tailWord_6714512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714512).length < 2 ^ (prefixWord ++ tailWord_6714512).sum := by decide
  have hdescent : baseEnd_6714512 < baseStart_6714512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714553 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 3]
def baseStart_6714553 : Nat := 118140960795 + 6714553 * 2 ^ 59
def prefixEnd_6714553 : Nat := 4983230072969 + 3 ^ 40 * 6714553 * 2
def baseEnd_6714553 : Nat := 3447793069088773014207839

theorem tailTrace_6714553 : CollatzResearch.WordTrace tailWord_6714553 prefixEnd_6714553 3447793069088773014207839 := by
  unfold tailWord_6714553
  simp only [CollatzResearch.WordTrace]
  refine ⟨244899867243328710199732313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163266578162219140133154875 244899867243328710199732313)
  ·
    refine ⟨183674900432496532649799235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244899867243328710199732313 183674900432496532649799235)
    ·
      refine ⟨275512350648744798974698853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183674900432496532649799235 275512350648744798974698853)
      ·
        refine ⟨51658565746639649807756035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275512350648744798974698853 51658565746639649807756035)
        ·
          refine ⟨77487848619959474711634053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51658565746639649807756035 77487848619959474711634053)
          ·
            refine ⟨14528971616242401508431385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77487848619959474711634053 14528971616242401508431385)
            ·
              refine ⟨10896728712181801131323539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14528971616242401508431385 10896728712181801131323539)
              ·
                refine ⟨16345093068272701696985309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10896728712181801131323539 16345093068272701696985309)
                ·
                  refine ⟨6129409900602263136369491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16345093068272701696985309 6129409900602263136369491)
                  ·
                    refine ⟨9194114850903394704554237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6129409900602263136369491 9194114850903394704554237)
                    ·
                      refine ⟨3447793069088773014207839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9194114850903394704554237 3447793069088773014207839)
                      ·
                        rfl

theorem cell23_6714553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_6714553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714553 prefixEnd_6714553 := by exact prefixLift 6714553
  have htrace : WordTrace (prefixWord ++ tailWord_6714553) baseStart_6714553 baseEnd_6714553 := by
    simpa [prefixWord, tailWord_6714553, baseEnd_6714553] using wordTrace_append hprefix tailTrace_6714553
  have hstable : (prefixWord ++ tailWord_6714553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714553).length < 2 ^ (prefixWord ++ tailWord_6714553).sum := by decide
  have hdescent : baseEnd_6714553 < baseStart_6714553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714559 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_6714559 : Nat := 118140960795 + 6714559 * 2 ^ 59
def prefixEnd_6714559 : Nat := 4983230072969 + 3 ^ 40 * 6714559 * 2
def baseEnd_6714559 : Nat := 3447796149972699990732811

theorem tailTrace_6714559 : CollatzResearch.WordTrace tailWord_6714559 prefixEnd_6714559 3447796149972699990732811 := by
  unfold tailWord_6714559
  simp only [CollatzResearch.WordTrace]
  refine ⟨244900086081306973224450731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163266724054204648816300487 244900086081306973224450731)
  ·
    refine ⟨367350129121960459836676097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244900086081306973224450731 367350129121960459836676097)
    ·
      refine ⟨275512596841470344877507073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367350129121960459836676097 275512596841470344877507073)
      ·
        refine ⟨206634447631102758658130305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275512596841470344877507073 206634447631102758658130305)
        ·
          refine ⟨154975835723327068993597729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206634447631102758658130305 154975835723327068993597729)
          ·
            refine ⟨116231876792495301745198297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154975835723327068993597729 116231876792495301745198297)
            ·
              refine ⟨87173907594371476308898723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116231876792495301745198297 87173907594371476308898723)
              ·
                refine ⟨130760861391557214463348085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87173907594371476308898723 130760861391557214463348085)
                ·
                  refine ⟨12258830755458488855938883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130760861391557214463348085 12258830755458488855938883)
                  ·
                    refine ⟨18388246133187733283908325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12258830755458488855938883 18388246133187733283908325)
                    ·
                      refine ⟨3447796149972699990732811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18388246133187733283908325 3447796149972699990732811)
                      ·
                        rfl

theorem cell23_6714559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_6714559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714559 prefixEnd_6714559 := by exact prefixLift 6714559
  have htrace : WordTrace (prefixWord ++ tailWord_6714559) baseStart_6714559 baseEnd_6714559 := by
    simpa [prefixWord, tailWord_6714559, baseEnd_6714559] using wordTrace_append hprefix tailTrace_6714559
  have hstable : (prefixWord ++ tailWord_6714559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714559).length < 2 ^ (prefixWord ++ tailWord_6714559).sum := by decide
  have hdescent : baseEnd_6714559 < baseStart_6714559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714649 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_6714649 : Nat := 118140960795 + 6714649 * 2 ^ 59
def prefixEnd_6714649 : Nat := 4983230072969 + 3 ^ 40 * 6714649 * 2
def baseEnd_6714649 : Nat := 3447842363231604638607397

theorem tailTrace_6714649 : CollatzResearch.WordTrace tailWord_6714649 prefixEnd_6714649 3447842363231604638607397 := by
  unfold tailWord_6714649
  simp only [CollatzResearch.WordTrace]
  refine ⟨244903368650980918595227001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163268912433987279063484667 244903368650980918595227001)
  ·
    refine ⟨183677526488235688946420251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244903368650980918595227001 183677526488235688946420251)
    ·
      refine ⟨275516289732353533419630377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183677526488235688946420251 275516289732353533419630377)
      ·
        refine ⟨206637217299265150064722783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275516289732353533419630377 206637217299265150064722783)
        ·
          refine ⟨309955825948897725097084175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206637217299265150064722783 309955825948897725097084175)
          ·
            refine ⟨464933738923346587645626263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309955825948897725097084175 464933738923346587645626263)
            ·
              refine ⟨697400608385019881468439395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464933738923346587645626263 697400608385019881468439395)
              ·
                refine ⟨1046100912577529822202659093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697400608385019881468439395 1046100912577529822202659093)
                ·
                  refine ⟨49035980277071710415749645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1046100912577529822202659093 49035980277071710415749645)
                  ·
                    refine ⟨18388492603901891405906117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49035980277071710415749645 18388492603901891405906117)
                    ·
                      refine ⟨3447842363231604638607397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18388492603901891405906117 3447842363231604638607397)
                      ·
                        rfl

theorem cell23_6714649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_6714649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714649 prefixEnd_6714649 := by exact prefixLift 6714649
  have htrace : WordTrace (prefixWord ++ tailWord_6714649) baseStart_6714649 baseEnd_6714649 := by
    simpa [prefixWord, tailWord_6714649, baseEnd_6714649] using wordTrace_append hprefix tailTrace_6714649
  have hstable : (prefixWord ++ tailWord_6714649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714649).length < 2 ^ (prefixWord ++ tailWord_6714649).sum := by decide
  have hdescent : baseEnd_6714649 < baseStart_6714649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714660 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_6714660 : Nat := 118140960795 + 6714660 * 2 ^ 59
def prefixEnd_6714660 : Nat := 4983230072969 + 3 ^ 40 * 6714660 * 2
def baseEnd_6714660 : Nat := 3447848011518804095569847

theorem tailTrace_6714660 : CollatzResearch.WordTrace tailWord_6714660 prefixEnd_6714660 3447848011518804095569847 := by
  unfold tailWord_6714660
  simp only [CollatzResearch.WordTrace]
  refine ⟨122451884926970533736938717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163269179902627378315918289 122451884926970533736938717)
  ·
    refine ⟨45919456847613950151352019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122451884926970533736938717 45919456847613950151352019)
    ·
      refine ⟨68879185271420925227028029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45919456847613950151352019 68879185271420925227028029)
      ·
        refine ⟨25829694476782846960135511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68879185271420925227028029 25829694476782846960135511)
        ·
          refine ⟨38744541715174270440203267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25829694476782846960135511 38744541715174270440203267)
          ·
            refine ⟨58116812572761405660304901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38744541715174270440203267 58116812572761405660304901)
            ·
              refine ⟨10896902357392763561307169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58116812572761405660304901 10896902357392763561307169)
              ·
                refine ⟨8172676768044572670980377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10896902357392763561307169 8172676768044572670980377)
                ·
                  refine ⟨6129507576033429503235283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8172676768044572670980377 6129507576033429503235283)
                  ·
                    refine ⟨9194261364050144254852925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6129507576033429503235283 9194261364050144254852925)
                    ·
                      refine ⟨3447848011518804095569847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9194261364050144254852925 3447848011518804095569847)
                      ·
                        rfl

theorem cell23_6714660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_6714660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714660 prefixEnd_6714660 := by exact prefixLift 6714660
  have htrace : WordTrace (prefixWord ++ tailWord_6714660) baseStart_6714660 baseEnd_6714660 := by
    simpa [prefixWord, tailWord_6714660, baseEnd_6714660] using wordTrace_append hprefix tailTrace_6714660
  have hstable : (prefixWord ++ tailWord_6714660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714660).length < 2 ^ (prefixWord ++ tailWord_6714660).sum := by decide
  have hdescent : baseEnd_6714660 < baseStart_6714660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714723 : List Nat := [1, 1, 1, 5, 2, 2, 2, 4, 5]
def baseStart_6714723 : Nat := 118140960795 + 6714723 * 2 ^ 59
def prefixEnd_6714723 : Nat := 4983230072969 + 3 ^ 40 * 6714723 * 2
def baseEnd_6714723 : Nat := 383097817866670816564673

theorem tailTrace_6714723 : CollatzResearch.WordTrace tailWord_6714723 prefixEnd_6714723 383097817866670816564673 := by
  unfold tailWord_6714723
  simp only [CollatzResearch.WordTrace]
  refine ⟨244906067652712829233420823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163270711768475219488947215 244906067652712829233420823)
  ·
    refine ⟨367359101479069243850131235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244906067652712829233420823 367359101479069243850131235)
    ·
      refine ⟨551038652218603865775196853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367359101479069243850131235 551038652218603865775196853)
      ·
        refine ⟨51659873645494112416424705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 551038652218603865775196853 51659873645494112416424705)
        ·
          refine ⟨38744905234120584312318529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51659873645494112416424705 38744905234120584312318529)
          ·
            refine ⟨29058678925590438234238897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38744905234120584312318529 29058678925590438234238897)
            ·
              refine ⟨21794009194192828675679173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29058678925590438234238897 21794009194192828675679173)
              ·
                refine ⟨4086376723911155376689845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21794009194192828675679173 4086376723911155376689845)
                ·
                  refine ⟨383097817866670816564673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4086376723911155376689845 383097817866670816564673)
                  ·
                    rfl

theorem cell23_6714723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 5].length) (baseStart_6714723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714723 prefixEnd_6714723 := by exact prefixLift 6714723
  have htrace : WordTrace (prefixWord ++ tailWord_6714723) baseStart_6714723 baseEnd_6714723 := by
    simpa [prefixWord, tailWord_6714723, baseEnd_6714723] using wordTrace_append hprefix tailTrace_6714723
  have hstable : (prefixWord ++ tailWord_6714723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714723).length < 2 ^ (prefixWord ++ tailWord_6714723).sum := by decide
  have hdescent : baseEnd_6714723 < baseStart_6714723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714733 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_6714733 : Nat := 118140960795 + 6714733 * 2 ^ 59
def prefixEnd_6714733 : Nat := 4983230072969 + 3 ^ 40 * 6714733 * 2
def baseEnd_6714733 : Nat := 3447885495606582309957011

theorem tailTrace_6714733 : CollatzResearch.WordTrace tailWord_6714733 prefixEnd_6714733 3447885495606582309957011 := by
  unfold tailWord_6714733
  simp only [CollatzResearch.WordTrace]
  refine ⟨244906432382676600941284853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163270954921784400627523235 244906432382676600941284853)
  ·
    refine ⟨22959978035875931338245455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244906432382676600941284853 22959978035875931338245455)
    ·
      refine ⟨34439967053813897007368183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22959978035875931338245455 34439967053813897007368183)
      ·
        refine ⟨51659950580720845511052275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34439967053813897007368183 51659950580720845511052275)
        ·
          refine ⟨77489925871081268266578413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51659950580720845511052275 77489925871081268266578413)
          ·
            refine ⟨29058722201655475599966905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77489925871081268266578413 29058722201655475599966905)
            ·
              refine ⟨21794041651241606699975179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29058722201655475599966905 21794041651241606699975179)
              ·
                refine ⟨32691062476862410049962769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21794041651241606699975179 32691062476862410049962769)
                ·
                  refine ⟨24518296857646807537472077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32691062476862410049962769 24518296857646807537472077)
                  ·
                    refine ⟨9194361321617552826552029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24518296857646807537472077 9194361321617552826552029)
                    ·
                      refine ⟨3447885495606582309957011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9194361321617552826552029 3447885495606582309957011)
                      ·
                        rfl

theorem cell23_6714733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_6714733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714733 prefixEnd_6714733 := by exact prefixLift 6714733
  have htrace : WordTrace (prefixWord ++ tailWord_6714733) baseStart_6714733 baseEnd_6714733 := by
    simpa [prefixWord, tailWord_6714733, baseEnd_6714733] using wordTrace_append hprefix tailTrace_6714733
  have hstable : (prefixWord ++ tailWord_6714733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714733).length < 2 ^ (prefixWord ++ tailWord_6714733).sum := by decide
  have hdescent : baseEnd_6714733 < baseStart_6714733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714734 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6714734 : Nat := 118140960795 + 6714734 * 2 ^ 59
def prefixEnd_6714734 : Nat := 4983230072969 + 3 ^ 40 * 6714734 * 2
def baseEnd_6714734 : Nat := 3447886009087236806044507

theorem tailTrace_6714734 : CollatzResearch.WordTrace tailWord_6714734 prefixEnd_6714734 3447886009087236806044507 := by
  unfold tailWord_6714734
  simp only [CollatzResearch.WordTrace]
  refine ⟨30613308606959122264008907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163270979237115318741380837 30613308606959122264008907)
  ·
    refine ⟨45919962910438683396013361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30613308606959122264008907 45919962910438683396013361)
    ·
      refine ⟨34439972182829012547010021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45919962910438683396013361 34439972182829012547010021)
      ·
        refine ⟨6457494784280439852564379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34439972182829012547010021 6457494784280439852564379)
        ·
          refine ⟨9686242176420659778846569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6457494784280439852564379 9686242176420659778846569)
          ·
            refine ⟨7264681632315494834134927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9686242176420659778846569 7264681632315494834134927)
            ·
              refine ⟨10897022448473242251202391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7264681632315494834134927 10897022448473242251202391)
              ·
                refine ⟨16345533672709863376803587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10897022448473242251202391 16345533672709863376803587)
                ·
                  refine ⟨24518300509064795065205381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16345533672709863376803587 24518300509064795065205381)
                  ·
                    refine ⟨4597181345449649074726009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24518300509064795065205381 4597181345449649074726009)
                    ·
                      refine ⟨3447886009087236806044507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597181345449649074726009 3447886009087236806044507)
                      ·
                        rfl

theorem cell23_6714734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6714734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714734 prefixEnd_6714734 := by exact prefixLift 6714734
  have htrace : WordTrace (prefixWord ++ tailWord_6714734) baseStart_6714734 baseEnd_6714734 := by
    simpa [prefixWord, tailWord_6714734, baseEnd_6714734] using wordTrace_append hprefix tailTrace_6714734
  have hstable : (prefixWord ++ tailWord_6714734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714734).length < 2 ^ (prefixWord ++ tailWord_6714734).sum := by decide
  have hdescent : baseEnd_6714734 < baseStart_6714734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714773 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_6714773 : Nat := 118140960795 + 6714773 * 2 ^ 59
def prefixEnd_6714773 : Nat := 4983230072969 + 3 ^ 40 * 6714773 * 2
def baseEnd_6714773 : Nat := 3447906034832762153456827

theorem tailTrace_6714773 : CollatzResearch.WordTrace tailWord_6714773 prefixEnd_6714773 3447906034832762153456827 := by
  unfold tailWord_6714773
  simp only [CollatzResearch.WordTrace]
  refine ⟨244907891302531687772740973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163271927535021125181827315 244907891302531687772740973)
  ·
    refine ⟨91840459238449382914777865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244907891302531687772740973 91840459238449382914777865)
    ·
      refine ⟨68880344428837037186083399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91840459238449382914777865 68880344428837037186083399)
      ·
        refine ⟨103320516643255555779125099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68880344428837037186083399 103320516643255555779125099)
        ·
          refine ⟨154980774964883333668687649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103320516643255555779125099 154980774964883333668687649)
          ·
            refine ⟨116235581223662500251515737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154980774964883333668687649 116235581223662500251515737)
            ·
              refine ⟨87176685917746875188636803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116235581223662500251515737 87176685917746875188636803)
              ·
                refine ⟨130765028876620312782955205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87176685917746875188636803 130765028876620312782955205)
                ·
                  refine ⟨24518442914366308646804101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130765028876620312782955205 24518442914366308646804101)
                  ·
                    refine ⟨4597208046443682871275769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24518442914366308646804101 4597208046443682871275769)
                    ·
                      refine ⟨3447906034832762153456827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597208046443682871275769 3447906034832762153456827)
                      ·
                        rfl

theorem cell23_6714773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_6714773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714773 prefixEnd_6714773 := by exact prefixLift 6714773
  have htrace : WordTrace (prefixWord ++ tailWord_6714773) baseStart_6714773 baseEnd_6714773 := by
    simpa [prefixWord, tailWord_6714773, baseEnd_6714773] using wordTrace_append hprefix tailTrace_6714773
  have hstable : (prefixWord ++ tailWord_6714773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714773).length < 2 ^ (prefixWord ++ tailWord_6714773).sum := by decide
  have hdescent : baseEnd_6714773 < baseStart_6714773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714780 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6714780 : Nat := 118140960795 + 6714780 * 2 ^ 59
def prefixEnd_6714780 : Nat := 4983230072969 + 3 ^ 40 * 6714780 * 2
def baseEnd_6714780 : Nat := 3447909629197343626069295

theorem tailTrace_6714780 : CollatzResearch.WordTrace tailWord_6714780 prefixEnd_6714780 3447909629197343626069295 := by
  unfold tailWord_6714780
  simp only [CollatzResearch.WordTrace]
  refine ⟨122454073306753163984122897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163272097742337551978830529 122454073306753163984122897)
  ·
    refine ⟨91840554980064872988092173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122454073306753163984122897 91840554980064872988092173)
    ·
      refine ⟨34440208117524327370534565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91840554980064872988092173 34440208117524327370534565)
      ·
        refine ⟨6457539022035811381975231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34440208117524327370534565 6457539022035811381975231)
        ·
          refine ⟨9686308533053717072962847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6457539022035811381975231 9686308533053717072962847)
          ·
            refine ⟨14529462799580575609444271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9686308533053717072962847 14529462799580575609444271)
            ·
              refine ⟨21794194199370863414166407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14529462799580575609444271 21794194199370863414166407)
              ·
                refine ⟨32691291299056295121249611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21794194199370863414166407 32691291299056295121249611)
                ·
                  refine ⟨49036936948584442681874417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32691291299056295121249611 49036936948584442681874417)
                  ·
                    refine ⟨36777702711438332011405813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49036936948584442681874417 36777702711438332011405813)
                    ·
                      refine ⟨3447909629197343626069295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36777702711438332011405813 3447909629197343626069295)
                      ·
                        rfl

theorem cell23_6714780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6714780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714780 prefixEnd_6714780 := by exact prefixLift 6714780
  have htrace : WordTrace (prefixWord ++ tailWord_6714780) baseStart_6714780 baseEnd_6714780 := by
    simpa [prefixWord, tailWord_6714780, baseEnd_6714780] using wordTrace_append hprefix tailTrace_6714780
  have hstable : (prefixWord ++ tailWord_6714780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714780).length < 2 ^ (prefixWord ++ tailWord_6714780).sum := by decide
  have hdescent : baseEnd_6714780 < baseStart_6714780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714833 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 5, 5, 2]
def baseStart_6714833 : Nat := 118140960795 + 6714833 * 2 ^ 59
def prefixEnd_6714833 : Nat := 4983230072969 + 3 ^ 40 * 6714833 * 2
def baseEnd_6714833 : Nat := 3447936843672031918706551

theorem tailTrace_6714833 : CollatzResearch.WordTrace tailWord_6714833 prefixEnd_6714833 3447936843672031918706551 := by
  unfold tailWord_6714833
  simp only [CollatzResearch.WordTrace]
  refine ⟨244910079682314318019925153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163273386454876212013283435 244910079682314318019925153)
  ·
    refine ⟨183682559761735738514943865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244910079682314318019925153 183682559761735738514943865)
    ·
      refine ⟨137761919821301803886207899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183682559761735738514943865 137761919821301803886207899)
      ·
        refine ⟨206642879731952705829311849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137761919821301803886207899 206642879731952705829311849)
        ·
          refine ⟨154982159798964529371983887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206642879731952705829311849 154982159798964529371983887)
          ·
            refine ⟨232473239698446794057975831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154982159798964529371983887 232473239698446794057975831)
            ·
              refine ⟨348709859547670191086963747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232473239698446794057975831 348709859547670191086963747)
              ·
                refine ⟨523064789321505286630445621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348709859547670191086963747 523064789321505286630445621)
                ·
                  refine ⟨49037323998891120621604277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 523064789321505286630445621 49037323998891120621604277)
                  ·
                    refine ⟨4597249124896042558275401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49037323998891120621604277 4597249124896042558275401)
                    ·
                      refine ⟨3447936843672031918706551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597249124896042558275401 3447936843672031918706551)
                      ·
                        rfl

theorem cell23_6714833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_6714833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714833 prefixEnd_6714833 := by exact prefixLift 6714833
  have htrace : WordTrace (prefixWord ++ tailWord_6714833) baseStart_6714833 baseEnd_6714833 := by
    simpa [prefixWord, tailWord_6714833, baseEnd_6714833] using wordTrace_append hprefix tailTrace_6714833
  have hstable : (prefixWord ++ tailWord_6714833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714833).length < 2 ^ (prefixWord ++ tailWord_6714833).sum := by decide
  have hdescent : baseEnd_6714833 < baseStart_6714833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714863 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_6714863 : Nat := 118140960795 + 6714863 * 2 ^ 59
def prefixEnd_6714863 : Nat := 4983230072969 + 3 ^ 40 * 6714863 * 2
def baseEnd_6714863 : Nat := 3447952248091666801331413

theorem tailTrace_6714863 : CollatzResearch.WordTrace tailWord_6714863 prefixEnd_6714863 3447952248091666801331413 := by
  unfold tailWord_6714863
  simp only [CollatzResearch.WordTrace]
  refine ⟨244911173872205633143517243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163274115914803755429011495 244911173872205633143517243)
  ·
    refine ⟨367366760808308449715275865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244911173872205633143517243 367366760808308449715275865)
    ·
      refine ⟨275525070606231337286456899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367366760808308449715275865 275525070606231337286456899)
      ·
        refine ⟨413287605909347005929685349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275525070606231337286456899 413287605909347005929685349)
        ·
          refine ⟨77491426108002563611816003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 413287605909347005929685349 77491426108002563611816003)
          ·
            refine ⟨116237139162003845417724005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77491426108002563611816003 116237139162003845417724005)
            ·
              refine ⟨21794463592875721015823251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116237139162003845417724005 21794463592875721015823251)
              ·
                refine ⟨32691695389313581523734877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21794463592875721015823251 32691695389313581523734877)
                ·
                  refine ⟨12259385770992593071400579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32691695389313581523734877 12259385770992593071400579)
                  ·
                    refine ⟨18389078656488889607100869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12259385770992593071400579 18389078656488889607100869)
                    ·
                      refine ⟨3447952248091666801331413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18389078656488889607100869 3447952248091666801331413)
                      ·
                        rfl

theorem cell23_6714863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_6714863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714863 prefixEnd_6714863 := by exact prefixLift 6714863
  have htrace : WordTrace (prefixWord ++ tailWord_6714863) baseStart_6714863 baseEnd_6714863 := by
    simpa [prefixWord, tailWord_6714863, baseEnd_6714863] using wordTrace_append hprefix tailTrace_6714863
  have hstable : (prefixWord ++ tailWord_6714863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714863).length < 2 ^ (prefixWord ++ tailWord_6714863).sum := by decide
  have hdescent : baseEnd_6714863 < baseStart_6714863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714873 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 4, 4]
def baseStart_6714873 : Nat := 118140960795 + 6714873 * 2 ^ 59
def prefixEnd_6714873 : Nat := 4983230072969 + 3 ^ 40 * 6714873 * 2
def baseEnd_6714873 : Nat := 1149319127632737254068789

theorem tailTrace_6714873 : CollatzResearch.WordTrace tailWord_6714873 prefixEnd_6714873 1149319127632737254068789 := by
  unfold tailWord_6714873
  simp only [CollatzResearch.WordTrace]
  refine ⟨244911538602169404851381273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163274359068112936567587515 244911538602169404851381273)
  ·
    refine ⟨183683653951627053638535955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244911538602169404851381273 183683653951627053638535955)
    ·
      refine ⟨275525480927440580457803933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183683653951627053638535955 275525480927440580457803933)
      ·
        refine ⟨103322055347790217671676475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275525480927440580457803933 103322055347790217671676475)
        ·
          refine ⟨154983083021685326507514713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103322055347790217671676475 154983083021685326507514713)
          ·
            refine ⟨116237312266263994880636035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154983083021685326507514713 116237312266263994880636035)
            ·
              refine ⟨174355968399395992320954053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116237312266263994880636035 174355968399395992320954053)
              ·
                refine ⟨32691744074886748560178885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174355968399395992320954053 32691744074886748560178885)
                ·
                  refine ⟨6129702014041265355033541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32691744074886748560178885 6129702014041265355033541)
                  ·
                    refine ⟨1149319127632737254068789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6129702014041265355033541 1149319127632737254068789)
                    ·
                      rfl

theorem cell23_6714873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 4].length) (baseStart_6714873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714873 prefixEnd_6714873 := by exact prefixLift 6714873
  have htrace : WordTrace (prefixWord ++ tailWord_6714873) baseStart_6714873 baseEnd_6714873 := by
    simpa [prefixWord, tailWord_6714873, baseEnd_6714873] using wordTrace_append hprefix tailTrace_6714873
  have hstable : (prefixWord ++ tailWord_6714873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714873).length < 2 ^ (prefixWord ++ tailWord_6714873).sum := by decide
  have hdescent : baseEnd_6714873 < baseStart_6714873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714877 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_6714877 : Nat := 118140960795 + 6714877 * 2 ^ 59
def prefixEnd_6714877 : Nat := 4983230072969 + 3 ^ 40 * 6714877 * 2
def baseEnd_6714877 : Nat := 1149319812273609915518783

theorem tailTrace_6714877 : CollatzResearch.WordTrace tailWord_6714877 prefixEnd_6714877 1149319812273609915518783 := by
  unfold tailWord_6714877
  simp only [CollatzResearch.WordTrace]
  refine ⟨244911684494154913534526885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163274456329436609023017923 244911684494154913534526885)
  ·
    refine ⟨45920940842654046287723791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244911684494154913534526885 45920940842654046287723791)
    ·
      refine ⟨68881411263981069431585687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45920940842654046287723791 68881411263981069431585687)
      ·
        refine ⟨103322116895971604147378531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68881411263981069431585687 103322116895971604147378531)
        ·
          refine ⟨154983175343957406221067797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103322116895971604147378531 154983175343957406221067797)
          ·
            refine ⟨7264836344248003416612553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154983175343957406221067797 7264836344248003416612553)
            ·
              refine ⟨5448627258186002562459415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7264836344248003416612553 5448627258186002562459415)
              ·
                refine ⟨8172940887279003843689123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448627258186002562459415 8172940887279003843689123)
                ·
                  refine ⟨12259411330918505765533685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8172940887279003843689123 12259411330918505765533685)
                  ·
                    refine ⟨1149319812273609915518783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12259411330918505765533685 1149319812273609915518783)
                    ·
                      rfl

theorem cell23_6714877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_6714877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714877 prefixEnd_6714877 := by exact prefixLift 6714877
  have htrace : WordTrace (prefixWord ++ tailWord_6714877) baseStart_6714877 baseEnd_6714877 := by
    simpa [prefixWord, tailWord_6714877, baseEnd_6714877] using wordTrace_append hprefix tailTrace_6714877
  have hstable : (prefixWord ++ tailWord_6714877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714877).length < 2 ^ (prefixWord ++ tailWord_6714877).sum := by decide
  have hdescent : baseEnd_6714877 < baseStart_6714877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714883 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 3]
def baseStart_6714883 : Nat := 118140960795 + 6714883 * 2 ^ 59
def prefixEnd_6714883 : Nat := 4983230072969 + 3 ^ 40 * 6714883 * 2
def baseEnd_6714883 : Nat := 3447962517704756723081321

theorem tailTrace_6714883 : CollatzResearch.WordTrace tailWord_6714883 prefixEnd_6714883 3447962517704756723081321 := by
  unfold tailWord_6714883
  simp only [CollatzResearch.WordTrace]
  refine ⟨244911903332133176559245303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163274602221422117706163535 244911903332133176559245303)
  ·
    refine ⟨367367854998199764838867955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244911903332133176559245303 367367854998199764838867955)
    ·
      refine ⟨551051782497299647258301933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367367854998199764838867955 551051782497299647258301933)
      ·
        refine ⟨206644418436487367721863225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 551051782497299647258301933 206644418436487367721863225)
        ·
          refine ⟨154983313827365525791397419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206644418436487367721863225 154983313827365525791397419)
          ·
            refine ⟨232474970741048288687096129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154983313827365525791397419 232474970741048288687096129)
            ·
              refine ⟨174356228055786216515322097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232474970741048288687096129 174356228055786216515322097)
              ·
                refine ⟨130767171041839662386491573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174356228055786216515322097 130767171041839662386491573)
                ·
                  refine ⟨12259422285172468348733585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130767171041839662386491573 12259422285172468348733585)
                  ·
                    refine ⟨9194566713879351261550189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12259422285172468348733585 9194566713879351261550189)
                    ·
                      refine ⟨3447962517704756723081321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9194566713879351261550189 3447962517704756723081321)
                      ·
                        rfl

theorem cell23_6714883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_6714883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714883 prefixEnd_6714883 := by exact prefixLift 6714883
  have htrace : WordTrace (prefixWord ++ tailWord_6714883) baseStart_6714883 baseEnd_6714883 := by
    simpa [prefixWord, tailWord_6714883, baseEnd_6714883] using wordTrace_append hprefix tailTrace_6714883
  have hstable : (prefixWord ++ tailWord_6714883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714883).length < 2 ^ (prefixWord ++ tailWord_6714883).sum := by decide
  have hdescent : baseEnd_6714883 < baseStart_6714883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714890 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_6714890 : Nat := 118140960795 + 6714890 * 2 ^ 59
def prefixEnd_6714890 : Nat := 4983230072969 + 3 ^ 40 * 6714890 * 2
def baseEnd_6714890 : Nat := 1149322037356446065231263

theorem tailTrace_6714890 : CollatzResearch.WordTrace tailWord_6714890 prefixEnd_6714890 1149322037356446065231263 := by
  unfold tailWord_6714890
  simp only [CollatzResearch.WordTrace]
  refine ⟨61228039660776954188687531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163274772428738544503166749 61228039660776954188687531)
  ·
    refine ⟨91842059491165431283031297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61228039660776954188687531 91842059491165431283031297)
    ·
      refine ⟨68881544618374073462273473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91842059491165431283031297 68881544618374073462273473)
      ·
        refine ⟨51661158463780555096705105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68881544618374073462273473 51661158463780555096705105)
        ·
          refine ⟨38745868847835416322528829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51661158463780555096705105 38745868847835416322528829)
          ·
            refine ⟨14529700817938281120948311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38745868847835416322528829 14529700817938281120948311)
            ·
              refine ⟨21794551226907421681422467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14529700817938281120948311 21794551226907421681422467)
              ·
                refine ⟨32691826840361132522133701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21794551226907421681422467 32691826840361132522133701)
                ·
                  refine ⟨6129717532567712347900069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32691826840361132522133701 6129717532567712347900069)
                  ·
                    refine ⟨1149322037356446065231263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6129717532567712347900069 1149322037356446065231263)
                    ·
                      rfl

theorem cell23_6714890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_6714890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714890 prefixEnd_6714890 := by exact prefixLift 6714890
  have htrace : WordTrace (prefixWord ++ tailWord_6714890) baseStart_6714890 baseEnd_6714890 := by
    simpa [prefixWord, tailWord_6714890, baseEnd_6714890] using wordTrace_append hprefix tailTrace_6714890
  have hstable : (prefixWord ++ tailWord_6714890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714890).length < 2 ^ (prefixWord ++ tailWord_6714890).sum := by decide
  have hdescent : baseEnd_6714890 < baseStart_6714890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714897 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 3, 2, 2]
def baseStart_6714897 : Nat := 118140960795 + 6714897 * 2 ^ 59
def prefixEnd_6714897 : Nat := 4983230072969 + 3 ^ 40 * 6714897 * 2
def baseEnd_6714897 : Nat := 3447969706433919668306257

theorem tailTrace_6714897 : CollatzResearch.WordTrace tailWord_6714897 prefixEnd_6714897 3447969706433919668306257 := by
  unfold tailWord_6714897
  simp only [CollatzResearch.WordTrace]
  refine ⟨244912413954082456950254945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163274942636054971300169963 244912413954082456950254945)
  ·
    refine ⟨183684310465561842712691209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244912413954082456950254945 183684310465561842712691209)
    ·
      refine ⟨137763232849171382034518407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183684310465561842712691209 137763232849171382034518407)
      ·
        refine ⟨206644849273757073051777611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137763232849171382034518407 206644849273757073051777611)
        ·
          refine ⟨309967273910635609577666417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206644849273757073051777611 309967273910635609577666417)
          ·
            refine ⟨232475455432976707183249813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309967273910635609577666417 232475455432976707183249813)
            ·
              refine ⟨10897286973420783149214835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232475455432976707183249813 10897286973420783149214835)
              ·
                refine ⟨16345930460131174723822253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10897286973420783149214835 16345930460131174723822253)
                ·
                  refine ⟨6129723922549190521433345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16345930460131174723822253 6129723922549190521433345)
                  ·
                    refine ⟨4597292941911892891075009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6129723922549190521433345 4597292941911892891075009)
                    ·
                      refine ⟨3447969706433919668306257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597292941911892891075009 3447969706433919668306257)
                      ·
                        rfl

theorem cell23_6714897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_6714897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714897 prefixEnd_6714897 := by exact prefixLift 6714897
  have htrace : WordTrace (prefixWord ++ tailWord_6714897) baseStart_6714897 baseEnd_6714897 := by
    simpa [prefixWord, tailWord_6714897, baseEnd_6714897] using wordTrace_append hprefix tailTrace_6714897
  have hstable : (prefixWord ++ tailWord_6714897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714897).length < 2 ^ (prefixWord ++ tailWord_6714897).sum := by decide
  have hdescent : baseEnd_6714897 < baseStart_6714897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714920 : List Nat := [2, 1, 5, 2, 2, 1, 1, 9]
def baseStart_6714920 : Nat := 118140960795 + 6714920 * 2 ^ 59
def prefixEnd_6714920 : Nat := 4983230072969 + 3 ^ 40 * 6714920 * 2
def baseEnd_6714920 : Nat := 127703019129221225122913

theorem tailTrace_6714920 : CollatzResearch.WordTrace tailWord_6714920 prefixEnd_6714920 127703019129221225122913 := by
  unfold tailWord_6714920
  simp only [CollatzResearch.WordTrace]
  refine ⟨122456626416499565939171107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163275501888666087918894809 122456626416499565939171107)
  ·
    refine ⟨183684939624749348908756661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122456626416499565939171107 183684939624749348908756661)
    ·
      refine ⟨17220463089820251460195937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183684939624749348908756661 17220463089820251460195937)
      ·
        refine ⟨12915347317365188595146953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17220463089820251460195937 12915347317365188595146953)
        ·
          refine ⟨9686510488023891446360215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12915347317365188595146953 9686510488023891446360215)
          ·
            refine ⟨14529765732035837169540323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9686510488023891446360215 14529765732035837169540323)
            ·
              refine ⟨21794648598053755754310485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14529765732035837169540323 21794648598053755754310485)
              ·
                refine ⟨127703019129221225122913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21794648598053755754310485 127703019129221225122913)
                ·
                  rfl

theorem cell23_6714920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 9].length) (baseStart_6714920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714920 prefixEnd_6714920 := by exact prefixLift 6714920
  have htrace : WordTrace (prefixWord ++ tailWord_6714920) baseStart_6714920 baseEnd_6714920 := by
    simpa [prefixWord, tailWord_6714920, baseEnd_6714920] using wordTrace_append hprefix tailTrace_6714920
  have hstable : (prefixWord ++ tailWord_6714920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714920).length < 2 ^ (prefixWord ++ tailWord_6714920).sum := by decide
  have hdescent : baseEnd_6714920 < baseStart_6714920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714931 : List Nat := [1, 1, 1, 2, 4, 5, 1, 3, 1, 2, 2]
def baseStart_6714931 : Nat := 118140960795 + 6714931 * 2 ^ 59
def prefixEnd_6714931 : Nat := 4983230072969 + 3 ^ 40 * 6714931 * 2
def baseEnd_6714931 : Nat := 3447987164776172535281101

theorem tailTrace_6714931 : CollatzResearch.WordTrace tailWord_6714931 prefixEnd_6714931 3447987164776172535281101 := by
  unfold tailWord_6714931
  simp only [CollatzResearch.WordTrace]
  refine ⟨244913654035959280756992647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163275769357306187171328431 244913654035959280756992647)
  ·
    refine ⟨367370481053938921135488971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244913654035959280756992647 367370481053938921135488971)
    ·
      refine ⟨551055721580908381703233457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367370481053938921135488971 551055721580908381703233457)
      ·
        refine ⟨413291791185681286277425093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551055721580908381703233457 413291791185681286277425093)
        ·
          refine ⟨77492210847315241177017205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 413291791185681286277425093 77492210847315241177017205)
          ·
            refine ⟨7264894766935803860345363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77492210847315241177017205 7264894766935803860345363)
            ·
              refine ⟨10897342150403705790518045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7264894766935803860345363 10897342150403705790518045)
              ·
                refine ⟨4086503306401389671444267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10897342150403705790518045 4086503306401389671444267)
                ·
                  refine ⟨6129754959602084507166401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086503306401389671444267 6129754959602084507166401)
                  ·
                    refine ⟨4597316219701563380374801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6129754959602084507166401 4597316219701563380374801)
                    ·
                      refine ⟨3447987164776172535281101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597316219701563380374801 3447987164776172535281101)
                      ·
                        rfl

theorem cell23_6714931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 2, 2].length) (baseStart_6714931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714931 prefixEnd_6714931 := by exact prefixLift 6714931
  have htrace : WordTrace (prefixWord ++ tailWord_6714931) baseStart_6714931 baseEnd_6714931 := by
    simpa [prefixWord, tailWord_6714931, baseEnd_6714931] using wordTrace_append hprefix tailTrace_6714931
  have hstable : (prefixWord ++ tailWord_6714931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714931).length < 2 ^ (prefixWord ++ tailWord_6714931).sum := by decide
  have hdescent : baseEnd_6714931 < baseStart_6714931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6714970 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2]
def baseStart_6714970 : Nat := 118140960795 + 6714970 * 2 ^ 59
def prefixEnd_6714970 : Nat := 4983230072969 + 3 ^ 40 * 6714970 * 2
def baseEnd_6714970 : Nat := 3448007190521697882693421

theorem tailTrace_6714970 : CollatzResearch.WordTrace tailWord_6714970 prefixEnd_6714970 3448007190521697882693421 := by
  unfold tailWord_6714970
  simp only [CollatzResearch.WordTrace]
  refine ⟨61228769120704497604415591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163276717655211993611774909 61228769120704497604415591)
  ·
    refine ⟨91843153681056746406623387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61228769120704497604415591 91843153681056746406623387)
    ·
      refine ⟨137764730521585119609935081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91843153681056746406623387 137764730521585119609935081)
      ·
        refine ⟨103323547891188839707451311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137764730521585119609935081 103323547891188839707451311)
        ·
          refine ⟨154985321836783259561176967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103323547891188839707451311 154985321836783259561176967)
          ·
            refine ⟨232477982755174889341765451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154985321836783259561176967 232477982755174889341765451)
            ·
              refine ⟨348716974132762334012648177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232477982755174889341765451 348716974132762334012648177)
              ·
                refine ⟨261537730599571750509486133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348716974132762334012648177 261537730599571750509486133)
                ·
                  refine ⟨24519162243709851610264325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 261537730599571750509486133 24519162243709851610264325)
                  ·
                    refine ⟨4597342920695597176924561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24519162243709851610264325 4597342920695597176924561)
                    ·
                      refine ⟨3448007190521697882693421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597342920695597176924561 3448007190521697882693421)
                      ·
                        rfl

theorem cell23_6714970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_6714970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6714970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6714970 prefixEnd_6714970 := by exact prefixLift 6714970
  have htrace : WordTrace (prefixWord ++ tailWord_6714970) baseStart_6714970 baseEnd_6714970 := by
    simpa [prefixWord, tailWord_6714970, baseEnd_6714970] using wordTrace_append hprefix tailTrace_6714970
  have hstable : (prefixWord ++ tailWord_6714970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6714970).length < 2 ^ (prefixWord ++ tailWord_6714970).sum := by decide
  have hdescent : baseEnd_6714970 < baseStart_6714970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6714970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715020 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_6715020 : Nat := 118140960795 + 6715020 * 2 ^ 59
def prefixEnd_6715020 : Nat := 4983230072969 + 3 ^ 40 * 6715020 * 2
def baseEnd_6715020 : Nat := 3448032864554422687068191

theorem tailTrace_6715020 : CollatzResearch.WordTrace tailWord_6715020 prefixEnd_6715020 3448032864554422687068191 := by
  unfold tailWord_6715020
  simp only [CollatzResearch.WordTrace]
  refine ⟨122458450066318424478491257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163277933421757899304655009 122458450066318424478491257)
  ·
    refine ⟨91843837549738818358868443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122458450066318424478491257 91843837549738818358868443)
    ·
      refine ⟨137765756324608227538302665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91843837549738818358868443 137765756324608227538302665)
      ·
        refine ⟨103324317243456170653726999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137765756324608227538302665 103324317243456170653726999)
        ·
          refine ⟨154986475865184255980590499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103324317243456170653726999 154986475865184255980590499)
          ·
            refine ⟨232479713797776383970885749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154986475865184255980590499 232479713797776383970885749)
            ·
              refine ⟨21794973168541535997270539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232479713797776383970885749 21794973168541535997270539)
              ·
                refine ⟨32692459752812303995905809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21794973168541535997270539 32692459752812303995905809)
                ·
                  refine ⟨24519344814609227996929357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32692459752812303995905809 24519344814609227996929357)
                  ·
                    refine ⟨9194754305478460498848509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24519344814609227996929357 9194754305478460498848509)
                    ·
                      refine ⟨3448032864554422687068191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9194754305478460498848509 3448032864554422687068191)
                      ·
                        rfl

theorem cell23_6715020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_6715020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715020 prefixEnd_6715020 := by exact prefixLift 6715020
  have htrace : WordTrace (prefixWord ++ tailWord_6715020) baseStart_6715020 baseEnd_6715020 := by
    simpa [prefixWord, tailWord_6715020, baseEnd_6715020] using wordTrace_append hprefix tailTrace_6715020
  have hstable : (prefixWord ++ tailWord_6715020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715020).length < 2 ^ (prefixWord ++ tailWord_6715020).sum := by decide
  have hdescent : baseEnd_6715020 < baseStart_6715020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715033 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_6715033 : Nat := 118140960795 + 6715033 * 2 ^ 59
def prefixEnd_6715033 : Nat := 4983230072969 + 3 ^ 40 * 6715033 * 2
def baseEnd_6715033 : Nat := 3448039539802931136205631

theorem tailTrace_6715033 : CollatzResearch.WordTrace tailWord_6715033 prefixEnd_6715033 3448039539802931136205631 := by
  unfold tailWord_6715033
  simp only [CollatzResearch.WordTrace]
  refine ⟨244917374281589752177205753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163278249521059834784803835 244917374281589752177205753)
  ·
    refine ⟨183688030711192314132904315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244917374281589752177205753 183688030711192314132904315)
    ·
      refine ⟨275532046066788471199356473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183688030711192314132904315 275532046066788471199356473)
      ·
        refine ⟨206649034550091353399517355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275532046066788471199356473 206649034550091353399517355)
        ·
          refine ⟨309973551825137030099276033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206649034550091353399517355 309973551825137030099276033)
          ·
            refine ⟨232480163868852772574457025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309973551825137030099276033 232480163868852772574457025)
            ·
              refine ⟨174360122901639579430842769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232480163868852772574457025 174360122901639579430842769)
              ·
                refine ⟨130770092176229684573132077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174360122901639579430842769 130770092176229684573132077)
                ·
                  refine ⟨49038784566086131714924529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130770092176229684573132077 49038784566086131714924529)
                  ·
                    refine ⟨36779088424564598786193397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49038784566086131714924529 36779088424564598786193397)
                    ·
                      refine ⟨3448039539802931136205631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36779088424564598786193397 3448039539802931136205631)
                      ·
                        rfl

theorem cell23_6715033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_6715033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715033 prefixEnd_6715033 := by exact prefixLift 6715033
  have htrace : WordTrace (prefixWord ++ tailWord_6715033) baseStart_6715033 baseEnd_6715033 := by
    simpa [prefixWord, tailWord_6715033, baseEnd_6715033] using wordTrace_append hprefix tailTrace_6715033
  have hstable : (prefixWord ++ tailWord_6715033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715033).length < 2 ^ (prefixWord ++ tailWord_6715033).sum := by decide
  have hdescent : baseEnd_6715033 < baseStart_6715033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715040 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 1, 7]
def baseStart_6715040 : Nat := 118140960795 + 6715040 * 2 ^ 59
def prefixEnd_6715040 : Nat := 4983230072969 + 3 ^ 40 * 6715040 * 2
def baseEnd_6715040 : Nat := 1149347711389170869606033

theorem tailTrace_6715040 : CollatzResearch.WordTrace tailWord_6715040 prefixEnd_6715040 1149347711389170869606033 := by
  unfold tailWord_6715040
  simp only [CollatzResearch.WordTrace]
  refine ⟨122458814796282196186355287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163278419728376261581807049 122458814796282196186355287)
  ·
    refine ⟨183688222194423294279532931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122458814796282196186355287 183688222194423294279532931)
    ·
      refine ⟨275532333291634941419299397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183688222194423294279532931 275532333291634941419299397)
      ·
        refine ⟨51662312492181551516118637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275532333291634941419299397 51662312492181551516118637)
        ·
          refine ⟨19373367184568081818544489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51662312492181551516118637 19373367184568081818544489)
          ·
            refine ⟨14530025388426061363908367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19373367184568081818544489 14530025388426061363908367)
            ·
              refine ⟨21795038082639092045862551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14530025388426061363908367 21795038082639092045862551)
              ·
                refine ⟨32692557123958638068793827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21795038082639092045862551 32692557123958638068793827)
                ·
                  refine ⟨49038835685937957103190741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32692557123958638068793827 49038835685937957103190741)
                  ·
                    refine ⟨1149347711389170869606033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49038835685937957103190741 1149347711389170869606033)
                    ·
                      rfl

theorem cell23_6715040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_6715040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715040 prefixEnd_6715040 := by exact prefixLift 6715040
  have htrace : WordTrace (prefixWord ++ tailWord_6715040) baseStart_6715040 baseEnd_6715040 := by
    simpa [prefixWord, tailWord_6715040, baseEnd_6715040] using wordTrace_append hprefix tailTrace_6715040
  have hstable : (prefixWord ++ tailWord_6715040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715040).length < 2 ^ (prefixWord ++ tailWord_6715040).sum := by decide
  have hdescent : baseEnd_6715040 < baseStart_6715040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715080 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_6715080 : Nat := 118140960795 + 6715080 * 2 ^ 59
def prefixEnd_6715080 : Nat := 4983230072969 + 3 ^ 40 * 6715080 * 2
def baseEnd_6715080 : Nat := 3448063673393692452317915

theorem tailTrace_6715080 : CollatzResearch.WordTrace tailWord_6715080 prefixEnd_6715080 3448063673393692452317915 := by
  unfold tailWord_6715080
  simp only [CollatzResearch.WordTrace]
  refine ⟨122459544256209739602083347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163279392341612986136111129 122459544256209739602083347)
  ·
    refine ⟨183689316384314609403125021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122459544256209739602083347 183689316384314609403125021)
    ·
      refine ⟨68883493644117978526171883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183689316384314609403125021 68883493644117978526171883)
      ·
        refine ⟨103325240466176967789257825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68883493644117978526171883 103325240466176967789257825)
        ·
          refine ⟨77493930349632725841943369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103325240466176967789257825 77493930349632725841943369)
          ·
            refine ⟨58120447762224544381457527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77493930349632725841943369 58120447762224544381457527)
            ·
              refine ⟨87180671643336816572186291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58120447762224544381457527 87180671643336816572186291)
              ·
                refine ⟨130771007465005224858279437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87180671643336816572186291 130771007465005224858279437)
                ·
                  refine ⟨49039127799376959321854789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130771007465005224858279437 49039127799376959321854789)
                  ·
                    refine ⟨9194836462383179872847773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49039127799376959321854789 9194836462383179872847773)
                    ·
                      refine ⟨3448063673393692452317915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9194836462383179872847773 3448063673393692452317915)
                      ·
                        rfl

theorem cell23_6715080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_6715080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715080 prefixEnd_6715080 := by exact prefixLift 6715080
  have htrace : WordTrace (prefixWord ++ tailWord_6715080) baseStart_6715080 baseEnd_6715080 := by
    simpa [prefixWord, tailWord_6715080, baseEnd_6715080] using wordTrace_append hprefix tailTrace_6715080
  have hstable : (prefixWord ++ tailWord_6715080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715080).length < 2 ^ (prefixWord ++ tailWord_6715080).sum := by decide
  have hdescent : baseEnd_6715080 < baseStart_6715080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715104 : List Nat := [2, 1, 1, 3, 1, 2, 5, 3, 1, 4]
def baseStart_6715104 : Nat := 118140960795 + 6715104 * 2 ^ 59
def prefixEnd_6715104 : Nat := 4983230072969 + 3 ^ 40 * 6715104 * 2
def baseEnd_6715104 : Nat := 1149358665643133452805935

theorem tailTrace_6715104 : CollatzResearch.WordTrace tailWord_6715104 prefixEnd_6715104 1149358665643133452805935 := by
  unfold tailWord_6715104
  simp only [CollatzResearch.WordTrace]
  refine ⟨122459981932166265651520183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163279975909555020868693577 122459981932166265651520183)
  ·
    refine ⟨183689972898249398477280275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122459981932166265651520183 183689972898249398477280275)
    ·
      refine ⟨275534959347374097715920413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183689972898249398477280275 275534959347374097715920413)
      ·
        refine ⟨103325609755265286643470155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275534959347374097715920413 103325609755265286643470155)
        ·
          refine ⟨154988414632897929965205233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103325609755265286643470155 154988414632897929965205233)
          ·
            refine ⟨116241310974673447473903925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154988414632897929965205233 116241310974673447473903925)
            ·
              refine ⟨10897622903875635700678493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116241310974673447473903925 10897622903875635700678493)
              ·
                refine ⟨4086608588953363387754435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10897622903875635700678493 4086608588953363387754435)
                ·
                  refine ⟨6129912883430045081631653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086608588953363387754435 6129912883430045081631653)
                  ·
                    refine ⟨1149358665643133452805935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6129912883430045081631653 1149358665643133452805935)
                    ·
                      rfl

theorem cell23_6715104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 4].length) (baseStart_6715104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715104 prefixEnd_6715104 := by exact prefixLift 6715104
  have htrace : WordTrace (prefixWord ++ tailWord_6715104) baseStart_6715104 baseEnd_6715104 := by
    simpa [prefixWord, tailWord_6715104, baseEnd_6715104] using wordTrace_append hprefix tailTrace_6715104
  have hstable : (prefixWord ++ tailWord_6715104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715104).length < 2 ^ (prefixWord ++ tailWord_6715104).sum := by decide
  have hdescent : baseEnd_6715104 < baseStart_6715104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715121 : List Nat := [1, 2, 2, 2, 2, 4, 3, 2, 1, 4]
def baseStart_6715121 : Nat := 118140960795 + 6715121 * 2 ^ 59
def prefixEnd_6715121 : Nat := 4983230072969 + 3 ^ 40 * 6715121 * 2
def baseEnd_6715121 : Nat := 1149361575366842263968409

theorem tailTrace_6715121 : CollatzResearch.WordTrace tailWord_6715121 prefixEnd_6715121 1149361575366842263968409 := by
  unfold tailWord_6715121
  simp only [CollatzResearch.WordTrace]
  refine ⟨244920583905270943206409217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163280389270180628804272811 244920583905270943206409217)
  ·
    refine ⟨183690437928953207404806913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244920583905270943206409217 183690437928953207404806913)
    ·
      refine ⟨137767828446714905553605185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183690437928953207404806913 137767828446714905553605185)
      ·
        refine ⟨103325871335036179165203889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137767828446714905553605185 103325871335036179165203889)
        ·
          refine ⟨77494403501277134373902917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103325871335036179165203889 77494403501277134373902917)
          ·
            refine ⟨14530200656489462695106797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77494403501277134373902917 14530200656489462695106797)
            ·
              refine ⟨5448825246183548510665049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14530200656489462695106797 5448825246183548510665049)
              ·
                refine ⟨4086618934637661382998787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5448825246183548510665049 4086618934637661382998787)
                ·
                  refine ⟨6129928401956492074498181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086618934637661382998787 6129928401956492074498181)
                  ·
                    refine ⟨1149361575366842263968409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6129928401956492074498181 1149361575366842263968409)
                    ·
                      rfl

theorem cell23_6715121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_6715121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715121 prefixEnd_6715121 := by exact prefixLift 6715121
  have htrace : WordTrace (prefixWord ++ tailWord_6715121) baseStart_6715121 baseEnd_6715121 := by
    simpa [prefixWord, tailWord_6715121, baseEnd_6715121] using wordTrace_append hprefix tailTrace_6715121
  have hstable : (prefixWord ++ tailWord_6715121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715121).length < 2 ^ (prefixWord ++ tailWord_6715121).sum := by decide
  have hdescent : baseEnd_6715121 < baseStart_6715121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715130 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_6715130 : Nat := 118140960795 + 6715130 * 2 ^ 59
def prefixEnd_6715130 : Nat := 4983230072969 + 3 ^ 40 * 6715130 * 2
def baseEnd_6715130 : Nat := 1149363115808805752230895

theorem tailTrace_6715130 : CollatzResearch.WordTrace tailWord_6715130 prefixEnd_6715130 1149363115808805752230895 := by
  unfold tailWord_6715130
  simp only [CollatzResearch.WordTrace]
  refine ⟨61230228040559584435871711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163280608108158891828991229 61230228040559584435871711)
  ·
    refine ⟨91845342060839376653807567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61230228040559584435871711 91845342060839376653807567)
    ·
      refine ⟨137768013091259064980711351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91845342060839376653807567 137768013091259064980711351)
      ·
        refine ⟨206652019636888597471067027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137768013091259064980711351 206652019636888597471067027)
        ·
          refine ⟨309978029455332896206600541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206652019636888597471067027 309978029455332896206600541)
          ·
            refine ⟨116241761045749836077475203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309978029455332896206600541 116241761045749836077475203)
            ·
              refine ⟨174362641568624754116212805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116241761045749836077475203 174362641568624754116212805)
              ·
                refine ⟨32692995294117141396789901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174362641568624754116212805 32692995294117141396789901)
                ·
                  refine ⟨12259873235293928023796213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32692995294117141396789901 12259873235293928023796213)
                  ·
                    refine ⟨1149363115808805752230895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12259873235293928023796213 1149363115808805752230895)
                    ·
                      rfl

theorem cell23_6715130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_6715130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715130 prefixEnd_6715130 := by exact prefixLift 6715130
  have htrace : WordTrace (prefixWord ++ tailWord_6715130) baseStart_6715130 baseEnd_6715130 := by
    simpa [prefixWord, tailWord_6715130, baseEnd_6715130] using wordTrace_append hprefix tailTrace_6715130
  have hstable : (prefixWord ++ tailWord_6715130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715130).length < 2 ^ (prefixWord ++ tailWord_6715130).sum := by decide
  have hdescent : baseEnd_6715130 < baseStart_6715130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715134 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_6715134 : Nat := 118140960795 + 6715134 * 2 ^ 59
def prefixEnd_6715134 : Nat := 4983230072969 + 3 ^ 40 * 6715134 * 2
def baseEnd_6715134 : Nat := 383121266816559471226963

theorem tailTrace_6715134 : CollatzResearch.WordTrace tailWord_6715134 prefixEnd_6715134 383121266816559471226963 := by
  unfold tailWord_6715134
  simp only [CollatzResearch.WordTrace]
  refine ⟨30615132256777980803329057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163280705369482564284421637 30615132256777980803329057)
  ·
    refine ⟨22961349192583485602496793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30615132256777980803329057 22961349192583485602496793)
    ·
      refine ⟨17221011894437614201872595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22961349192583485602496793 17221011894437614201872595)
      ·
        refine ⟨25831517841656421302808893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17221011894437614201872595 25831517841656421302808893)
        ·
          refine ⟨9686819190621157988553335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25831517841656421302808893 9686819190621157988553335)
          ·
            refine ⟨14530228785931736982830003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9686819190621157988553335 14530228785931736982830003)
            ·
              refine ⟨21795343178897605474245005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14530228785931736982830003 21795343178897605474245005)
              ·
                refine ⟨8173253692086602052841877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21795343178897605474245005 8173253692086602052841877)
                ·
                  refine ⟨383121266816559471226963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8173253692086602052841877 383121266816559471226963)
                  ·
                    rfl

theorem cell23_6715134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_6715134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715134 prefixEnd_6715134 := by exact prefixLift 6715134
  have htrace : WordTrace (prefixWord ++ tailWord_6715134) baseStart_6715134 baseEnd_6715134 := by
    simpa [prefixWord, tailWord_6715134, baseEnd_6715134] using wordTrace_append hprefix tailTrace_6715134
  have hstable : (prefixWord ++ tailWord_6715134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715134).length < 2 ^ (prefixWord ++ tailWord_6715134).sum := by decide
  have hdescent : baseEnd_6715134 < baseStart_6715134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715137 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_6715137 : Nat := 118140960795 + 6715137 * 2 ^ 59
def prefixEnd_6715137 : Nat := 4983230072969 + 3 ^ 40 * 6715137 * 2
def baseEnd_6715137 : Nat := 3448092941790998729305153

theorem tailTrace_6715137 : CollatzResearch.WordTrace tailWord_6715137 prefixEnd_6715137 3448092941790998729305153 := by
  unfold tailWord_6715137
  simp only [CollatzResearch.WordTrace]
  refine ⟨244921167473212977938991665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163280778315475318625994443 244921167473212977938991665)
  ·
    refine ⟨183690875604909733454243749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244921167473212977938991665 183690875604909733454243749)
    ·
      refine ⟨34442039175920575022670703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183690875604909733454243749 34442039175920575022670703)
      ·
        refine ⟨51663058763880862534006055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34442039175920575022670703 51663058763880862534006055)
        ·
          refine ⟨77494588145821293801009083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51663058763880862534006055 77494588145821293801009083)
          ·
            refine ⟨116241882218731940701513625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77494588145821293801009083 116241882218731940701513625)
            ·
              refine ⟨87181411664048955526135219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116241882218731940701513625 87181411664048955526135219)
              ·
                refine ⟨130772117496073433289202829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87181411664048955526135219 130772117496073433289202829)
                ·
                  refine ⟨49039544061027537483451061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130772117496073433289202829 49039544061027537483451061)
                  ·
                    refine ⟨4597457255721331639073537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49039544061027537483451061 4597457255721331639073537)
                    ·
                      refine ⟨3448092941790998729305153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597457255721331639073537 3448092941790998729305153)
                      ·
                        rfl

theorem cell23_6715137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_6715137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715137 prefixEnd_6715137 := by exact prefixLift 6715137
  have htrace : WordTrace (prefixWord ++ tailWord_6715137) baseStart_6715137 baseEnd_6715137 := by
    simpa [prefixWord, tailWord_6715137, baseEnd_6715137] using wordTrace_append hprefix tailTrace_6715137
  have hstable : (prefixWord ++ tailWord_6715137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715137).length < 2 ^ (prefixWord ++ tailWord_6715137).sum := by decide
  have hdescent : baseEnd_6715137 < baseStart_6715137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715147 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 1, 5]
def baseStart_6715147 : Nat := 118140960795 + 6715147 * 2 ^ 59
def prefixEnd_6715147 : Nat := 4983230072969 + 3 ^ 40 * 6715147 * 2
def baseEnd_6715147 : Nat := 1149366025532514563393369

theorem tailTrace_6715147 : CollatzResearch.WordTrace tailWord_6715147 prefixEnd_6715147 1149366025532514563393369 := by
  unfold tailWord_6715147
  simp only [CollatzResearch.WordTrace]
  refine ⟨244921532203176749646855695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163281021468784499764570463 244921532203176749646855695)
  ·
    refine ⟨367382298304765124470283543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244921532203176749646855695 367382298304765124470283543)
    ·
      refine ⟨551073447457147686705425315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367382298304765124470283543 551073447457147686705425315)
      ·
        refine ⟨826610171185721530058137973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551073447457147686705425315 826610171185721530058137973)
        ·
          refine ⟨77494703548661393442950435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 826610171185721530058137973 77494703548661393442950435)
          ·
            refine ⟨116242055322992090164425653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77494703548661393442950435 116242055322992090164425653)
            ·
              refine ⟨10897692686530508452914905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116242055322992090164425653 10897692686530508452914905)
              ·
                refine ⟨8173269514897881339686179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10897692686530508452914905 8173269514897881339686179)
                ·
                  refine ⟨12259904272346822009529269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173269514897881339686179 12259904272346822009529269)
                  ·
                    refine ⟨1149366025532514563393369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12259904272346822009529269 1149366025532514563393369)
                    ·
                      rfl

theorem cell23_6715147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 5].length) (baseStart_6715147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715147 prefixEnd_6715147 := by exact prefixLift 6715147
  have htrace : WordTrace (prefixWord ++ tailWord_6715147) baseStart_6715147 baseEnd_6715147 := by
    simpa [prefixWord, tailWord_6715147, baseEnd_6715147] using wordTrace_append hprefix tailTrace_6715147
  have hstable : (prefixWord ++ tailWord_6715147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715147).length < 2 ^ (prefixWord ++ tailWord_6715147).sum := by decide
  have hdescent : baseEnd_6715147 < baseStart_6715147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715160 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 3, 6]
def baseStart_6715160 : Nat := 118140960795 + 6715160 * 2 ^ 59
def prefixEnd_6715160 : Nat := 4983230072969 + 3 ^ 40 * 6715160 * 2
def baseEnd_6715160 : Nat := 1149368250615350713105849

theorem tailTrace_6715160 : CollatzResearch.WordTrace tailWord_6715160 prefixEnd_6715160 1149368250615350713105849 := by
  unfold tailWord_6715160
  simp only [CollatzResearch.WordTrace]
  refine ⟨122461003176064826433539467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163281337568086435244719289 122461003176064826433539467)
  ·
    refine ⟨183691504764097239650309201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122461003176064826433539467 183691504764097239650309201)
    ·
      refine ⟨137768628573072929737731901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183691504764097239650309201 137768628573072929737731901)
      ·
        refine ⟨51663235714902348651649463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137768628573072929737731901 51663235714902348651649463)
        ·
          refine ⟨77494853572353522977474195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51663235714902348651649463 77494853572353522977474195)
          ·
            refine ⟨116242280358530284466211293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77494853572353522977474195 116242280358530284466211293)
            ·
              refine ⟨43590855134448856674829235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116242280358530284466211293 43590855134448856674829235)
              ·
                refine ⟨65386282701673285012243853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43590855134448856674829235 65386282701673285012243853)
                ·
                  refine ⟨24519856013127481879591445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65386282701673285012243853 24519856013127481879591445)
                  ·
                    refine ⟨1149368250615350713105849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24519856013127481879591445 1149368250615350713105849)
                    ·
                      rfl

theorem cell23_6715160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_6715160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715160 prefixEnd_6715160 := by exact prefixLift 6715160
  have htrace : WordTrace (prefixWord ++ tailWord_6715160) baseStart_6715160 baseEnd_6715160 := by
    simpa [prefixWord, tailWord_6715160, baseEnd_6715160] using wordTrace_append hprefix tailTrace_6715160
  have hstable : (prefixWord ++ tailWord_6715160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715160).length < 2 ^ (prefixWord ++ tailWord_6715160).sum := by decide
  have hdescent : baseEnd_6715160 < baseStart_6715160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715164 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_6715164 : Nat := 118140960795 + 6715164 * 2 ^ 59
def prefixEnd_6715164 : Nat := 4983230072969 + 3 ^ 40 * 6715164 * 2
def baseEnd_6715164 : Nat := 1149368935256223374555843

theorem tailTrace_6715164 : CollatzResearch.WordTrace tailWord_6715164 prefixEnd_6715164 1149368935256223374555843 := by
  unfold tailWord_6715164
  simp only [CollatzResearch.WordTrace]
  refine ⟨122461076122057580775112273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163281434829410107700149697 122461076122057580775112273)
  ·
    refine ⟨91845807091543185581334205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122461076122057580775112273 91845807091543185581334205)
    ·
      refine ⟨34442177659328694593000327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91845807091543185581334205 34442177659328694593000327)
      ·
        refine ⟨51663266488993041889500491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34442177659328694593000327 51663266488993041889500491)
        ·
          refine ⟨77494899733489562834250737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51663266488993041889500491 77494899733489562834250737)
          ·
            refine ⟨58121174800117172125688053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77494899733489562834250737 58121174800117172125688053)
            ·
              refine ⟨5448860137510984886783255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58121174800117172125688053 5448860137510984886783255)
              ·
                refine ⟨8173290206266477330174883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448860137510984886783255 8173290206266477330174883)
                ·
                  refine ⟨12259935309399715995262325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173290206266477330174883 12259935309399715995262325)
                  ·
                    refine ⟨1149368935256223374555843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12259935309399715995262325 1149368935256223374555843)
                    ·
                      rfl

theorem cell23_6715164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_6715164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715164 prefixEnd_6715164 := by exact prefixLift 6715164
  have htrace : WordTrace (prefixWord ++ tailWord_6715164) baseStart_6715164 baseEnd_6715164 := by
    simpa [prefixWord, tailWord_6715164, baseEnd_6715164] using wordTrace_append hprefix tailTrace_6715164
  have hstable : (prefixWord ++ tailWord_6715164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715164).length < 2 ^ (prefixWord ++ tailWord_6715164).sum := by decide
  have hdescent : baseEnd_6715164 < baseStart_6715164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715194 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_6715194 : Nat := 118140960795 + 6715194 * 2 ^ 59
def prefixEnd_6715194 : Nat := 4983230072969 + 3 ^ 40 * 6715194 * 2
def baseEnd_6715194 : Nat := 1149374070062768335430797

theorem tailTrace_6715194 : CollatzResearch.WordTrace tailWord_6715194 prefixEnd_6715194 1149374070062768335430797 := by
  unfold tailWord_6715194
  simp only [CollatzResearch.WordTrace]
  refine ⟨61230811608501619168454159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163282164289337651115877757 61230811608501619168454159)
  ·
    refine ⟨91846217412752428752681239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61230811608501619168454159 91846217412752428752681239)
    ·
      refine ⟨137769326119128643129021859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91846217412752428752681239 137769326119128643129021859)
      ·
        refine ⟨206653989178692964693532789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137769326119128643129021859 206653989178692964693532789)
        ·
          refine ⟨19373811485502465440018699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206653989178692964693532789 19373811485502465440018699)
          ·
            refine ⟨29060717228253698160028049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19373811485502465440018699 29060717228253698160028049)
            ·
              refine ⟨21795537921190273620021037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29060717228253698160028049 21795537921190273620021037)
              ·
                refine ⟨8173326720446352607507889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21795537921190273620021037 8173326720446352607507889)
                ·
                  refine ⟨6129995040334764455630917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8173326720446352607507889 6129995040334764455630917)
                  ·
                    refine ⟨1149374070062768335430797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6129995040334764455630917 1149374070062768335430797)
                    ·
                      rfl

theorem cell23_6715194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_6715194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715194 prefixEnd_6715194 := by exact prefixLift 6715194
  have htrace : WordTrace (prefixWord ++ tailWord_6715194) baseStart_6715194 baseEnd_6715194 := by
    simpa [prefixWord, tailWord_6715194, baseEnd_6715194] using wordTrace_append hprefix tailTrace_6715194
  have hstable : (prefixWord ++ tailWord_6715194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715194).length < 2 ^ (prefixWord ++ tailWord_6715194).sum := by decide
  have hdescent : baseEnd_6715194 < baseStart_6715194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715218 : List Nat := [3, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_6715218 : Nat := 118140960795 + 6715218 * 2 ^ 59
def prefixEnd_6715218 : Nat := 4983230072969 + 3 ^ 40 * 6715218 * 2
def baseEnd_6715218 : Nat := 3448134533724012912392281

theorem tailTrace_6715218 : CollatzResearch.WordTrace tailWord_6715218 prefixEnd_6715218 3448134533724012912392281 := by
  unfold tailWord_6715218
  simp only [CollatzResearch.WordTrace]
  refine ⟨61231030446479882193172577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163282747857279685848460205 61231030446479882193172577)
  ·
    refine ⟨45923272834859911644879433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61231030446479882193172577 45923272834859911644879433)
    ·
      refine ⟨34442454626144933733659575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45923272834859911644879433 34442454626144933733659575)
      ·
        refine ⟨51663681939217400600489363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34442454626144933733659575 51663681939217400600489363)
        ·
          refine ⟨77495522908826100900734045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51663681939217400600489363 77495522908826100900734045)
          ·
            refine ⟨29060821090809787837775267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77495522908826100900734045 29060821090809787837775267)
            ·
              refine ⟨43591231636214681756662901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29060821090809787837775267 43591231636214681756662901)
              ·
                refine ⟨4086677965895126414687147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43591231636214681756662901 4086677965895126414687147)
                ·
                  refine ⟨6130016948842689622030721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086677965895126414687147 6130016948842689622030721)
                  ·
                    refine ⟨4597512711632017216523041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6130016948842689622030721 4597512711632017216523041)
                    ·
                      refine ⟨3448134533724012912392281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597512711632017216523041 3448134533724012912392281)
                      ·
                        rfl

theorem cell23_6715218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_6715218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715218 prefixEnd_6715218 := by exact prefixLift 6715218
  have htrace : WordTrace (prefixWord ++ tailWord_6715218) baseStart_6715218 baseEnd_6715218 := by
    simpa [prefixWord, tailWord_6715218, baseEnd_6715218] using wordTrace_append hprefix tailTrace_6715218
  have hstable : (prefixWord ++ tailWord_6715218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715218).length < 2 ^ (prefixWord ++ tailWord_6715218).sum := by decide
  have hdescent : baseEnd_6715218 < baseStart_6715218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715221 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_6715221 : Nat := 118140960795 + 6715221 * 2 ^ 59
def prefixEnd_6715221 : Nat := 4983230072969 + 3 ^ 40 * 6715221 * 2
def baseEnd_6715221 : Nat := 3448136074165976400654767

theorem tailTrace_6715221 : CollatzResearch.WordTrace tailWord_6715221 prefixEnd_6715221 3448136074165976400654767 := by
  unfold tailWord_6715221
  simp only [CollatzResearch.WordTrace]
  refine ⟨244924231204908660285049517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163282820803272440190033011 244924231204908660285049517)
  ·
    refine ⟨91846586701840747606893569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244924231204908660285049517 91846586701840747606893569)
    ·
      refine ⟨68884940026380560705170177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91846586701840747606893569 68884940026380560705170177)
      ·
        refine ⟨51663705019785420528877633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68884940026380560705170177 51663705019785420528877633)
        ·
          refine ⟨38747778764839065396658225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51663705019785420528877633 38747778764839065396658225)
          ·
            refine ⟨29060834073629299047493669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38747778764839065396658225 29060834073629299047493669)
            ·
              refine ⟨5448906388805493571405063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29060834073629299047493669 5448906388805493571405063)
              ·
                refine ⟨8173359583208240357107595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448906388805493571405063 8173359583208240357107595)
                ·
                  refine ⟨12260039374812360535661393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173359583208240357107595 12260039374812360535661393)
                  ·
                    refine ⟨9195029531109270401746045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12260039374812360535661393 9195029531109270401746045)
                    ·
                      refine ⟨3448136074165976400654767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9195029531109270401746045 3448136074165976400654767)
                      ·
                        rfl

theorem cell23_6715221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_6715221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715221 prefixEnd_6715221 := by exact prefixLift 6715221
  have htrace : WordTrace (prefixWord ++ tailWord_6715221) baseStart_6715221 baseEnd_6715221 := by
    simpa [prefixWord, tailWord_6715221, baseEnd_6715221] using wordTrace_append hprefix tailTrace_6715221
  have hstable : (prefixWord ++ tailWord_6715221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715221).length < 2 ^ (prefixWord ++ tailWord_6715221).sum := by decide
  have hdescent : baseEnd_6715221 < baseStart_6715221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715228 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_6715228 : Nat := 118140960795 + 6715228 * 2 ^ 59
def prefixEnd_6715228 : Nat := 4983230072969 + 3 ^ 40 * 6715228 * 2
def baseEnd_6715228 : Nat := 1149379889510185957755745

theorem tailTrace_6715228 : CollatzResearch.WordTrace tailWord_6715228 prefixEnd_6715228 1149379889510185957755745 := by
  unfold tailWord_6715228
  simp only [CollatzResearch.WordTrace]
  refine ⟨122462243257941650240277169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163282991010588866987036225 122462243257941650240277169)
  ·
    refine ⟨91846682443456237680207877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122462243257941650240277169 91846682443456237680207877)
    ·
      refine ⟨17221252958148044565038977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91846682443456237680207877 17221252958148044565038977)
      ·
        refine ⟨12915939718611033423779233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17221252958148044565038977 12915939718611033423779233)
        ·
          refine ⟨9686954788958275067834425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12915939718611033423779233 9686954788958275067834425)
          ·
            refine ⟨7265216091718706300875819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9686954788958275067834425 7265216091718706300875819)
            ·
              refine ⟨10897824137578059451313729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265216091718706300875819 10897824137578059451313729)
              ·
                refine ⟨8173368103183544588485297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10897824137578059451313729 8173368103183544588485297)
                ·
                  refine ⟨6130026077387658441363973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8173368103183544588485297 6130026077387658441363973)
                  ·
                    refine ⟨1149379889510185957755745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6130026077387658441363973 1149379889510185957755745)
                    ·
                      rfl

theorem cell23_6715228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_6715228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715228 prefixEnd_6715228 := by exact prefixLift 6715228
  have htrace : WordTrace (prefixWord ++ tailWord_6715228) baseStart_6715228 baseEnd_6715228 := by
    simpa [prefixWord, tailWord_6715228, baseEnd_6715228] using wordTrace_append hprefix tailTrace_6715228
  have hstable : (prefixWord ++ tailWord_6715228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715228).length < 2 ^ (prefixWord ++ tailWord_6715228).sum := by decide
  have hdescent : baseEnd_6715228 < baseStart_6715228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715280 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 11]
def baseStart_6715280 : Nat := 118140960795 + 6715280 * 2 ^ 59
def prefixEnd_6715280 : Nat := 4983230072969 + 3 ^ 40 * 6715280 * 2
def baseEnd_6715280 : Nat := 383129596613843518868555

theorem tailTrace_6715280 : CollatzResearch.WordTrace tailWord_6715280 prefixEnd_6715280 383129596613843518868555 := by
  unfold tailWord_6715280
  simp only [CollatzResearch.WordTrace]
  refine ⟨122463191555847456680723647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163284255407796608907631529 122463191555847456680723647)
  ·
    refine ⟨183694787333771185021085471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122463191555847456680723647 183694787333771185021085471)
    ·
      refine ⟨275542181000656777531628207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183694787333771185021085471 275542181000656777531628207)
      ·
        refine ⟨413313271500985166297442311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275542181000656777531628207 413313271500985166297442311)
        ·
          refine ⟨619969907251477749446163467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413313271500985166297442311 619969907251477749446163467)
          ·
            refine ⟨929954860877216624169245201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 619969907251477749446163467 929954860877216624169245201)
            ·
              refine ⟨697466145657912468126933901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929954860877216624169245201 697466145657912468126933901)
              ·
                refine ⟨261549804621717175547600213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697466145657912468126933901 261549804621717175547600213)
                ·
                  refine ⟨383129596613843518868555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 261549804621717175547600213 383129596613843518868555)
                  ·
                    rfl

theorem cell23_6715280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 11].length) (baseStart_6715280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715280 prefixEnd_6715280 := by exact prefixLift 6715280
  have htrace : WordTrace (prefixWord ++ tailWord_6715280) baseStart_6715280 baseEnd_6715280 := by
    simpa [prefixWord, tailWord_6715280, baseEnd_6715280] using wordTrace_append hprefix tailTrace_6715280
  have hstable : (prefixWord ++ tailWord_6715280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715280).length < 2 ^ (prefixWord ++ tailWord_6715280).sum := by decide
  have hdescent : baseEnd_6715280 < baseStart_6715280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715286 : List Nat := [5, 3, 1, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6715286 : Nat := 118140960795 + 6715286 * 2 ^ 59
def prefixEnd_6715286 : Nat := 4983230072969 + 3 ^ 40 * 6715286 * 2
def baseEnd_6715286 : Nat := 3448169450408518646341969

theorem tailTrace_6715286 : CollatzResearch.WordTrace tailWord_6715286 prefixEnd_6715286 3448169450408518646341969 := by
  unfold tailWord_6715286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15307912621854573524135357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163284401299782117590777141 15307912621854573524135357)
  ·
    refine ⟨5740467233195465071550759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15307912621854573524135357 5740467233195465071550759)
    ·
      refine ⟨8610700849793197607326139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5740467233195465071550759 8610700849793197607326139)
      ·
        refine ⟨12916051274689796410989209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8610700849793197607326139 12916051274689796410989209)
        ·
          refine ⟨9687038456017347308241907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12916051274689796410989209 9687038456017347308241907)
          ·
            refine ⟨14530557684026020962362861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9687038456017347308241907 14530557684026020962362861)
            ·
              refine ⟨5448959131509757860886073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14530557684026020962362861 5448959131509757860886073)
              ·
                refine ⟨4086719348632318395664555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5448959131509757860886073 4086719348632318395664555)
                ·
                  refine ⟨6130079022948477593496833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086719348632318395664555 6130079022948477593496833)
                  ·
                    refine ⟨4597559267211358195122625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6130079022948477593496833 4597559267211358195122625)
                    ·
                      refine ⟨3448169450408518646341969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597559267211358195122625 3448169450408518646341969)
                      ·
                        rfl

theorem cell23_6715286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6715286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715286 prefixEnd_6715286 := by exact prefixLift 6715286
  have htrace : WordTrace (prefixWord ++ tailWord_6715286) baseStart_6715286 baseEnd_6715286 := by
    simpa [prefixWord, tailWord_6715286, baseEnd_6715286] using wordTrace_append hprefix tailTrace_6715286
  have hstable : (prefixWord ++ tailWord_6715286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715286).length < 2 ^ (prefixWord ++ tailWord_6715286).sum := by decide
  have hdescent : baseEnd_6715286 < baseStart_6715286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715441 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 1, 5, 2]
def baseStart_6715441 : Nat := 118140960795 + 6715441 * 2 ^ 59
def prefixEnd_6715441 : Nat := 4983230072969 + 3 ^ 40 * 6715441 * 2
def baseEnd_6715441 : Nat := 3448249039909965539903755

theorem tailTrace_6715441 : CollatzResearch.WordTrace tailWord_6715441 prefixEnd_6715441 3448249039909965539903755 := by
  unfold tailWord_6715441
  simp only [CollatzResearch.WordTrace]
  refine ⟨244932255264111637858058177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163288170176074425238705451 244932255264111637858058177)
  ·
    refine ⟨183699191448083728393543633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244932255264111637858058177 183699191448083728393543633)
    ·
      refine ⟨137774393586062796295157725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183699191448083728393543633 137774393586062796295157725)
      ·
        refine ⟨51665397594773548610684147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137774393586062796295157725 51665397594773548610684147)
        ·
          refine ⟨77498096392160322916026221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51665397594773548610684147 77498096392160322916026221)
          ·
            refine ⟨29061786147060121093509833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77498096392160322916026221 29061786147060121093509833)
            ·
              refine ⟨21796339610295090820132375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29061786147060121093509833 21796339610295090820132375)
              ·
                refine ⟨32694509415442636230198563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21796339610295090820132375 32694509415442636230198563)
                ·
                  refine ⟨49041764123163954345297845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32694509415442636230198563 49041764123163954345297845)
                  ·
                    refine ⟨4597665386546620719871673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49041764123163954345297845 4597665386546620719871673)
                    ·
                      refine ⟨3448249039909965539903755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597665386546620719871673 3448249039909965539903755)
                      ·
                        rfl

theorem cell23_6715441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_6715441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715441 prefixEnd_6715441 := by exact prefixLift 6715441
  have htrace : WordTrace (prefixWord ++ tailWord_6715441) baseStart_6715441 baseEnd_6715441 := by
    simpa [prefixWord, tailWord_6715441, baseEnd_6715441] using wordTrace_append hprefix tailTrace_6715441
  have hstable : (prefixWord ++ tailWord_6715441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715441).length < 2 ^ (prefixWord ++ tailWord_6715441).sum := by decide
  have hdescent : baseEnd_6715441 < baseStart_6715441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715465 : List Nat := [1, 2, 1, 1, 2, 2, 7, 2, 1, 1, 3]
def baseStart_6715465 : Nat := 118140960795 + 6715465 * 2 ^ 59
def prefixEnd_6715465 : Nat := 4983230072969 + 3 ^ 40 * 6715465 * 2
def baseEnd_6715465 : Nat := 3448261363445673446003645

theorem tailTrace_6715465 : CollatzResearch.WordTrace tailWord_6715465 prefixEnd_6715465 3448261363445673446003645 := by
  unfold tailWord_6715465
  simp only [CollatzResearch.WordTrace]
  refine ⟨244933130616024689956931849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163288753744016459971287899 244933130616024689956931849)
  ·
    refine ⟨183699847962018517467698887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244933130616024689956931849 183699847962018517467698887)
    ·
      refine ⟨275549771943027776201548331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183699847962018517467698887 275549771943027776201548331)
      ·
        refine ⟨413324657914541664302322497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275549771943027776201548331 413324657914541664302322497)
        ·
          refine ⟨309993493435906248226741873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413324657914541664302322497 309993493435906248226741873)
          ·
            refine ⟨232495120076929686170056405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309993493435906248226741873 232495120076929686170056405)
            ·
              refine ⟨5449104376803039519610697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 232495120076929686170056405 5449104376803039519610697)
              ·
                refine ⟨4086828282602279639708023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5449104376803039519610697 4086828282602279639708023)
                ·
                  refine ⟨6130242423903419459562035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086828282602279639708023 6130242423903419459562035)
                  ·
                    refine ⟨9195363635855129189343053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6130242423903419459562035 9195363635855129189343053)
                    ·
                      refine ⟨3448261363445673446003645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9195363635855129189343053 3448261363445673446003645)
                      ·
                        rfl

theorem cell23_6715465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 1, 3].length) (baseStart_6715465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715465 prefixEnd_6715465 := by exact prefixLift 6715465
  have htrace : WordTrace (prefixWord ++ tailWord_6715465) baseStart_6715465 baseEnd_6715465 := by
    simpa [prefixWord, tailWord_6715465, baseEnd_6715465] using wordTrace_append hprefix tailTrace_6715465
  have hstable : (prefixWord ++ tailWord_6715465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715465).length < 2 ^ (prefixWord ++ tailWord_6715465).sum := by decide
  have hdescent : baseEnd_6715465 < baseStart_6715465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715481 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 2, 4]
def baseStart_6715481 : Nat := 118140960795 + 6715481 * 2 ^ 59
def prefixEnd_6715481 : Nat := 4983230072969 + 3 ^ 40 * 6715481 * 2
def baseEnd_6715481 : Nat := 1149423193045381794467857

theorem tailTrace_6715481 : CollatzResearch.WordTrace tailWord_6715481 prefixEnd_6715481 1149423193045381794467857 := by
  unfold tailWord_6715481
  simp only [CollatzResearch.WordTrace]
  refine ⟨244933714183966724689514297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163289142789311149793009531 244933714183966724689514297)
  ·
    refine ⟨183700285637975043517135723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244933714183966724689514297 183700285637975043517135723)
    ·
      refine ⟨275550428456962565275703585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183700285637975043517135723 275550428456962565275703585)
      ·
        refine ⟨206662821342721923956777689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275550428456962565275703585 206662821342721923956777689)
        ·
          refine ⟨154997116007041442967583267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206662821342721923956777689 154997116007041442967583267)
          ·
            refine ⟨232495674010562164451374901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154997116007041442967583267 232495674010562164451374901)
            ·
              refine ⟨21796469438490202917316397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232495674010562164451374901 21796469438490202917316397)
              ·
                refine ⟨8173676039433826093993649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21796469438490202917316397 8173676039433826093993649)
                ·
                  refine ⟨6130257029575369570495237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8173676039433826093993649 6130257029575369570495237)
                  ·
                    refine ⟨1149423193045381794467857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6130257029575369570495237 1149423193045381794467857)
                    ·
                      rfl

theorem cell23_6715481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 4].length) (baseStart_6715481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715481 prefixEnd_6715481 := by exact prefixLift 6715481
  have htrace : WordTrace (prefixWord ++ tailWord_6715481) baseStart_6715481 baseEnd_6715481 := by
    simpa [prefixWord, tailWord_6715481, baseEnd_6715481] using wordTrace_append hprefix tailTrace_6715481
  have hstable : (prefixWord ++ tailWord_6715481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715481).length < 2 ^ (prefixWord ++ tailWord_6715481).sum := by decide
  have hdescent : baseEnd_6715481 < baseStart_6715481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715485 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6715485 : Nat := 118140960795 + 6715485 * 2 ^ 59
def prefixEnd_6715485 : Nat := 4983230072969 + 3 ^ 40 * 6715485 * 2
def baseEnd_6715485 : Nat := 1149423877686254455917851

theorem tailTrace_6715485 : CollatzResearch.WordTrace tailWord_6715485 prefixEnd_6715485 1149423877686254455917851 := by
  unfold tailWord_6715485
  simp only [CollatzResearch.WordTrace]
  refine ⟨244933860075952233372659909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163289240050634822248439939 244933860075952233372659909)
  ·
    refine ⟨45925098764241043757373733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244933860075952233372659909 45925098764241043757373733)
    ·
      refine ⟨8610956018295195704507575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45925098764241043757373733 8610956018295195704507575)
      ·
        refine ⟨12916434027442793556761363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8610956018295195704507575 12916434027442793556761363)
        ·
          refine ⟨19374651041164190335142045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12916434027442793556761363 19374651041164190335142045)
          ·
            refine ⟨7265494140436571375678267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19374651041164190335142045 7265494140436571375678267)
            ·
              refine ⟨10898241210654857063517401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265494140436571375678267 10898241210654857063517401)
              ·
                refine ⟨8173680907991142797638051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10898241210654857063517401 8173680907991142797638051)
                ·
                  refine ⟨12260521361986714196457077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173680907991142797638051 12260521361986714196457077)
                  ·
                    refine ⟨1149423877686254455917851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12260521361986714196457077 1149423877686254455917851)
                    ·
                      rfl

theorem cell23_6715485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6715485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715485 prefixEnd_6715485 := by exact prefixLift 6715485
  have htrace : WordTrace (prefixWord ++ tailWord_6715485) baseStart_6715485 baseEnd_6715485 := by
    simpa [prefixWord, tailWord_6715485, baseEnd_6715485] using wordTrace_append hprefix tailTrace_6715485
  have hstable : (prefixWord ++ tailWord_6715485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715485).length < 2 ^ (prefixWord ++ tailWord_6715485).sum := by decide
  have hdescent : baseEnd_6715485 < baseStart_6715485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715488 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 4]
def baseStart_6715488 : Nat := 118140960795 + 6715488 * 2 ^ 59
def prefixEnd_6715488 : Nat := 4983230072969 + 3 ^ 40 * 6715488 * 2
def baseEnd_6715488 : Nat := 3448273173500726856016039

theorem tailTrace_6715488 : CollatzResearch.WordTrace tailWord_6715488 prefixEnd_6715488 3448273173500726856016039 := by
  unfold tailWord_6715488
  simp only [CollatzResearch.WordTrace]
  refine ⟨122466984747470682442509559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163289312996627576590012745 122466984747470682442509559)
  ·
    refine ⟨183700477121206023663764339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122466984747470682442509559 183700477121206023663764339)
    ·
      refine ⟨275550715681809035495646509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183700477121206023663764339 275550715681809035495646509)
      ·
        refine ⟨103331518380678388310867441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275550715681809035495646509 103331518380678388310867441)
        ·
          refine ⟨77498638785508791233150581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103331518380678388310867441 77498638785508791233150581)
          ·
            refine ⟨7265497386141449178107867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77498638785508791233150581 7265497386141449178107867)
            ·
              refine ⟨10898246079212173767161801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265497386141449178107867 10898246079212173767161801)
              ·
                refine ⟨8173684559409130325371351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10898246079212173767161801 8173684559409130325371351)
                ·
                  refine ⟨12260526839113695488057027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173684559409130325371351 12260526839113695488057027)
                  ·
                    refine ⟨18390790258670543232085541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12260526839113695488057027 18390790258670543232085541)
                    ·
                      refine ⟨3448273173500726856016039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18390790258670543232085541 3448273173500726856016039)
                      ·
                        rfl

theorem cell23_6715488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_6715488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715488 prefixEnd_6715488 := by exact prefixLift 6715488
  have htrace : WordTrace (prefixWord ++ tailWord_6715488) baseStart_6715488 baseEnd_6715488 := by
    simpa [prefixWord, tailWord_6715488, baseEnd_6715488] using wordTrace_append hprefix tailTrace_6715488
  have hstable : (prefixWord ++ tailWord_6715488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715488).length < 2 ^ (prefixWord ++ tailWord_6715488).sum := by decide
  have hdescent : baseEnd_6715488 < baseStart_6715488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715501 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6715501 : Nat := 118140960795 + 6715501 * 2 ^ 59
def prefixEnd_6715501 : Nat := 4983230072969 + 3 ^ 40 * 6715501 * 2
def baseEnd_6715501 : Nat := 3448279848749235305153479

theorem tailTrace_6715501 : CollatzResearch.WordTrace tailWord_6715501 prefixEnd_6715501 3448279848749235305153479 := by
  unfold tailWord_6715501
  simp only [CollatzResearch.WordTrace]
  refine ⟨244934443643894268105242357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163289629095929512070161571 244934443643894268105242357)
  ·
    refine ⟨22962604091615087634866471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244934443643894268105242357 22962604091615087634866471)
    ·
      refine ⟨34443906137422631452299707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22962604091615087634866471 34443906137422631452299707)
      ·
        refine ⟨51665859206133947178449561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34443906137422631452299707 51665859206133947178449561)
        ·
          refine ⟨38749394404600460383837171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51665859206133947178449561 38749394404600460383837171)
          ·
            refine ⟨58124091606900690575755757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38749394404600460383837171 58124091606900690575755757)
            ·
              refine ⟨21796534352587758965908409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58124091606900690575755757 21796534352587758965908409)
              ·
                refine ⟨16347400764440819224431307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21796534352587758965908409 16347400764440819224431307)
                ·
                  refine ⟨24521101146661228836646961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16347400764440819224431307 24521101146661228836646961)
                  ·
                    refine ⟨18390825859995921627485221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24521101146661228836646961 18390825859995921627485221)
                    ·
                      refine ⟨3448279848749235305153479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18390825859995921627485221 3448279848749235305153479)
                      ·
                        rfl

theorem cell23_6715501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6715501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715501 prefixEnd_6715501 := by exact prefixLift 6715501
  have htrace : WordTrace (prefixWord ++ tailWord_6715501) baseStart_6715501 baseEnd_6715501 := by
    simpa [prefixWord, tailWord_6715501, baseEnd_6715501] using wordTrace_append hprefix tailTrace_6715501
  have hstable : (prefixWord ++ tailWord_6715501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715501).length < 2 ^ (prefixWord ++ tailWord_6715501).sum := by decide
  have hdescent : baseEnd_6715501 < baseStart_6715501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715505 : List Nat := [1, 2, 2, 2, 1, 1, 4, 5, 1, 2, 2]
def baseStart_6715505 : Nat := 118140960795 + 6715505 * 2 ^ 59
def prefixEnd_6715505 : Nat := 4983230072969 + 3 ^ 40 * 6715505 * 2
def baseEnd_6715505 : Nat := 3448281902671853289503461

theorem tailTrace_6715505 : CollatzResearch.WordTrace tailWord_6715505 prefixEnd_6715505 3448281902671853289503461 := by
  unfold tailWord_6715505
  simp only [CollatzResearch.WordTrace]
  refine ⟨244934589535879776788387969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163289726357253184525591979 244934589535879776788387969)
  ·
    refine ⟨183700942151909832591290977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244934589535879776788387969 183700942151909832591290977)
    ·
      refine ⟨137775706613932374443468233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183700942151909832591290977 137775706613932374443468233)
      ·
        refine ⟨103331779960449280832601175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137775706613932374443468233 103331779960449280832601175)
        ·
          refine ⟨154997669940673921248901763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103331779960449280832601175 154997669940673921248901763)
          ·
            refine ⟨232496504911010881873352645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154997669940673921248901763 232496504911010881873352645)
            ·
              refine ⟨43593094670814540351253621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232496504911010881873352645 43593094670814540351253621)
              ·
                refine ⟨4086852625388863157930027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43593094670814540351253621 4086852625388863157930027)
                ·
                  refine ⟨6130278938083294736895041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086852625388863157930027 6130278938083294736895041)
                  ·
                    refine ⟨4597709203562471052671281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6130278938083294736895041 4597709203562471052671281)
                    ·
                      refine ⟨3448281902671853289503461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597709203562471052671281 3448281902671853289503461)
                      ·
                        rfl

theorem cell23_6715505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_6715505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715505 prefixEnd_6715505 := by exact prefixLift 6715505
  have htrace : WordTrace (prefixWord ++ tailWord_6715505) baseStart_6715505 baseEnd_6715505 := by
    simpa [prefixWord, tailWord_6715505, baseEnd_6715505] using wordTrace_append hprefix tailTrace_6715505
  have hstable : (prefixWord ++ tailWord_6715505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715505).length < 2 ^ (prefixWord ++ tailWord_6715505).sum := by decide
  have hdescent : baseEnd_6715505 < baseStart_6715505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715524 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_6715524 : Nat := 118140960795 + 6715524 * 2 ^ 59
def prefixEnd_6715524 : Nat := 4983230072969 + 3 ^ 40 * 6715524 * 2
def baseEnd_6715524 : Nat := 1149430552934762905055291

theorem tailTrace_6715524 : CollatzResearch.WordTrace tailWord_6715524 prefixEnd_6715524 1149430552934762905055291 := by
  unfold tailWord_6715524
  simp only [CollatzResearch.WordTrace]
  refine ⟨122467641261405471516664813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163290188348540628688886417 122467641261405471516664813)
  ·
    refine ⟨45925365473027051818749305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122467641261405471516664813 45925365473027051818749305)
    ·
      refine ⟨34444024104770288864061979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45925365473027051818749305 34444024104770288864061979)
      ·
        refine ⟨51666036157155433296092969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34444024104770288864061979 51666036157155433296092969)
        ·
          refine ⟨38749527117866574972069727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51666036157155433296092969 38749527117866574972069727)
          ·
            refine ⟨58124290676799862458104591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38749527117866574972069727 58124290676799862458104591)
            ·
              refine ⟨87186436015199793687156887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58124290676799862458104591 87186436015199793687156887)
              ·
                refine ⟨130779654022799690530735331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87186436015199793687156887 130779654022799690530735331)
                ·
                  refine ⟨196169481034199535796102997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130779654022799690530735331 196169481034199535796102997)
                  ·
                    refine ⟨1149430552934762905055291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 196169481034199535796102997 1149430552934762905055291)
                    ·
                      rfl

theorem cell23_6715524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_6715524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715524 prefixEnd_6715524 := by exact prefixLift 6715524
  have htrace : WordTrace (prefixWord ++ tailWord_6715524) baseStart_6715524 baseEnd_6715524 := by
    simpa [prefixWord, tailWord_6715524, baseEnd_6715524] using wordTrace_append hprefix tailTrace_6715524
  have hstable : (prefixWord ++ tailWord_6715524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715524).length < 2 ^ (prefixWord ++ tailWord_6715524).sum := by decide
  have hdescent : baseEnd_6715524 < baseStart_6715524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715538 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_6715538 : Nat := 118140960795 + 6715538 * 2 ^ 59
def prefixEnd_6715538 : Nat := 4983230072969 + 3 ^ 40 * 6715538 * 2
def baseEnd_6715538 : Nat := 3448298847533451660390809

theorem tailTrace_6715538 : CollatzResearch.WordTrace tailWord_6715538 prefixEnd_6715538 3448298847533451660390809 := by
  unfold tailWord_6715538
  simp only [CollatzResearch.WordTrace]
  refine ⟨61233948286190055856084817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163290528763173482282892845 61233948286190055856084817)
  ·
    refine ⟨45925461214642541892063613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61233948286190055856084817 45925461214642541892063613)
    ·
      refine ⟨17222047955490953209523855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45925461214642541892063613 17222047955490953209523855)
      ·
        refine ⟨25833071933236429814285783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17222047955490953209523855 25833071933236429814285783)
        ·
          refine ⟨38749607899854644721428675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25833071933236429814285783 38749607899854644721428675)
          ·
            refine ⟨58124411849781967082143013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38749607899854644721428675 58124411849781967082143013)
            ·
              refine ⟨10898327221834118827901815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58124411849781967082143013 10898327221834118827901815)
              ·
                refine ⟨16347490832751178241852723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10898327221834118827901815 16347490832751178241852723)
                ·
                  refine ⟨24521236249126767362779085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16347490832751178241852723 24521236249126767362779085)
                  ·
                    refine ⟨9195463593422537761042157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24521236249126767362779085 9195463593422537761042157)
                    ·
                      refine ⟨3448298847533451660390809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9195463593422537761042157 3448298847533451660390809)
                      ·
                        rfl

theorem cell23_6715538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_6715538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715538 prefixEnd_6715538 := by exact prefixLift 6715538
  have htrace : WordTrace (prefixWord ++ tailWord_6715538) baseStart_6715538 baseEnd_6715538 := by
    simpa [prefixWord, tailWord_6715538, baseEnd_6715538] using wordTrace_append hprefix tailTrace_6715538
  have hstable : (prefixWord ++ tailWord_6715538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715538).length < 2 ^ (prefixWord ++ tailWord_6715538).sum := by decide
  have hdescent : baseEnd_6715538 < baseStart_6715538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715548 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_6715548 : Nat := 118140960795 + 6715548 * 2 ^ 59
def prefixEnd_6715548 : Nat := 4983230072969 + 3 ^ 40 * 6715548 * 2
def baseEnd_6715548 : Nat := 3448303982339996621265763

theorem tailTrace_6715548 : CollatzResearch.WordTrace tailWord_6715548 prefixEnd_6715548 3448303982339996621265763 := by
  unfold tailWord_6715548
  simp only [CollatzResearch.WordTrace]
  refine ⟨122468078937361997566101649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163290771916482663421468865 122468078937361997566101649)
  ·
    refine ⟨91851059203021498174576237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122468078937361997566101649 91851059203021498174576237)
    ·
      refine ⟨34444147201133061815466089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91851059203021498174576237 34444147201133061815466089)
      ·
        refine ⟨25833110400849796361599567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34444147201133061815466089 25833110400849796361599567)
        ·
          refine ⟨38749665601274694542399351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25833110400849796361599567 38749665601274694542399351)
          ·
            refine ⟨58124498401912041813599027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38749665601274694542399351 58124498401912041813599027)
            ·
              refine ⟨87186747602868062720398541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58124498401912041813599027 87186747602868062720398541)
              ·
                refine ⟨32695030351075523520149453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87186747602868062720398541 32695030351075523520149453)
                ·
                  refine ⟨12260636381653321320056045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32695030351075523520149453 12260636381653321320056045)
                  ·
                    refine ⟨4597738643119995495021017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12260636381653321320056045 4597738643119995495021017)
                    ·
                      refine ⟨3448303982339996621265763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597738643119995495021017 3448303982339996621265763)
                      ·
                        rfl

theorem cell23_6715548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_6715548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715548 prefixEnd_6715548 := by exact prefixLift 6715548
  have htrace : WordTrace (prefixWord ++ tailWord_6715548) baseStart_6715548 baseEnd_6715548 := by
    simpa [prefixWord, tailWord_6715548, baseEnd_6715548] using wordTrace_append hprefix tailTrace_6715548
  have hstable : (prefixWord ++ tailWord_6715548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715548).length < 2 ^ (prefixWord ++ tailWord_6715548).sum := by decide
  have hdescent : baseEnd_6715548 < baseStart_6715548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715559 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_6715559 : Nat := 118140960795 + 6715559 * 2 ^ 59
def prefixEnd_6715559 : Nat := 4983230072969 + 3 ^ 40 * 6715559 * 2
def baseEnd_6715559 : Nat := 3448309630627196078228213

theorem tailTrace_6715559 : CollatzResearch.WordTrace tailWord_6715559 prefixEnd_6715559 3448309630627196078228213 := by
  unfold tailWord_6715559
  simp only [CollatzResearch.WordTrace]
  refine ⟨244936559077684144010853731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163291039385122762673902487 244936559077684144010853731)
  ·
    refine ⟨367404838616526216016280597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244936559077684144010853731 367404838616526216016280597)
    ·
      refine ⟨17222101810149666375763153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 367404838616526216016280597 17222101810149666375763153)
      ·
        refine ⟨12916576357612249781822365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17222101810149666375763153 12916576357612249781822365)
        ·
          refine ⟨4843716134104593668183387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12916576357612249781822365 4843716134104593668183387)
          ·
            refine ⟨7265574201156890502275081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843716134104593668183387 7265574201156890502275081)
            ·
              refine ⟨5449180650867667876706311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7265574201156890502275081 5449180650867667876706311)
              ·
                refine ⟨8173770976301501815059467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5449180650867667876706311 8173770976301501815059467)
                ·
                  refine ⟨12260656464452252722589201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173770976301501815059467 12260656464452252722589201)
                  ·
                    refine ⟨9195492348339189541941901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12260656464452252722589201 9195492348339189541941901)
                    ·
                      refine ⟨3448309630627196078228213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9195492348339189541941901 3448309630627196078228213)
                      ·
                        rfl

theorem cell23_6715559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_6715559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715559 prefixEnd_6715559 := by exact prefixLift 6715559
  have htrace : WordTrace (prefixWord ++ tailWord_6715559) baseStart_6715559 baseEnd_6715559 := by
    simpa [prefixWord, tailWord_6715559, baseEnd_6715559] using wordTrace_append hprefix tailTrace_6715559
  have hstable : (prefixWord ++ tailWord_6715559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715559).length < 2 ^ (prefixWord ++ tailWord_6715559).sum := by decide
  have hdescent : baseEnd_6715559 < baseStart_6715559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715564 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_6715564 : Nat := 118140960795 + 6715564 * 2 ^ 59
def prefixEnd_6715564 : Nat := 4983230072969 + 3 ^ 40 * 6715564 * 2
def baseEnd_6715564 : Nat := 3448312198030468558665689

theorem tailTrace_6715564 : CollatzResearch.WordTrace tailWord_6715564 prefixEnd_6715564 3448312198030468558665689 := by
  unfold tailWord_6715564
  simp only [CollatzResearch.WordTrace]
  refine ⟨122468370721333014932392873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163291160961777353243190497 122468370721333014932392873)
  ·
    refine ⟨91851278040999761199294655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122468370721333014932392873 91851278040999761199294655)
    ·
      refine ⟨137776917061499641798941983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91851278040999761199294655 137776917061499641798941983)
      ·
        refine ⟨206665375592249462698412975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137776917061499641798941983 206665375592249462698412975)
        ·
          refine ⟨309998063388374194047619463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206665375592249462698412975 309998063388374194047619463)
          ·
            refine ⟨464997095082561291071429195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309998063388374194047619463 464997095082561291071429195)
            ·
              refine ⟨697495642623841936607143793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464997095082561291071429195 697495642623841936607143793)
              ·
                refine ⟨523121731967881452455357845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 697495642623841936607143793 523121731967881452455357845)
                ·
                  refine ⟨24521331185994443083844899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 523121731967881452455357845 24521331185994443083844899)
                  ·
                    refine ⟨36781996778991664625767349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24521331185994443083844899 36781996778991664625767349)
                    ·
                      refine ⟨3448312198030468558665689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36781996778991664625767349 3448312198030468558665689)
                      ·
                        rfl

theorem cell23_6715564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_6715564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715564 prefixEnd_6715564 := by exact prefixLift 6715564
  have htrace : WordTrace (prefixWord ++ tailWord_6715564) baseStart_6715564 baseEnd_6715564 := by
    simpa [prefixWord, tailWord_6715564, baseEnd_6715564] using wordTrace_append hprefix tailTrace_6715564
  have hstable : (prefixWord ++ tailWord_6715564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715564).length < 2 ^ (prefixWord ++ tailWord_6715564).sum := by decide
  have hdescent : baseEnd_6715564 < baseStart_6715564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715631 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 4, 5]
def baseStart_6715631 : Nat := 118140960795 + 6715631 * 2 ^ 59
def prefixEnd_6715631 : Nat := 4983230072969 + 3 ^ 40 * 6715631 * 2
def baseEnd_6715631 : Nat := 1149448867078106598842627

theorem tailTrace_6715631 : CollatzResearch.WordTrace tailWord_6715631 prefixEnd_6715631 1149448867078106598842627 := by
  unfold tailWord_6715631
  simp only [CollatzResearch.WordTrace]
  refine ⟨244939185133423300307474747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163292790088948866871649831 244939185133423300307474747)
  ·
    refine ⟨367408777700134950461212121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244939185133423300307474747 367408777700134950461212121)
    ·
      refine ⟨275556583275101212845909091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367408777700134950461212121 275556583275101212845909091)
      ·
        refine ⟨413334874912651819268863637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275556583275101212845909091 413334874912651819268863637)
        ·
          refine ⟨19375072261530554028227983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 413334874912651819268863637 19375072261530554028227983)
          ·
            refine ⟨29062608392295831042341975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19375072261530554028227983 29062608392295831042341975)
            ·
              refine ⟨43593912588443746563512963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29062608392295831042341975 43593912588443746563512963)
              ·
                refine ⟨65390868882665619845269445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43593912588443746563512963 65390868882665619845269445)
                ·
                  refine ⟨12260787915499803720988021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65390868882665619845269445 12260787915499803720988021)
                  ·
                    refine ⟨1149448867078106598842627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12260787915499803720988021 1149448867078106598842627)
                    ·
                      rfl

theorem cell23_6715631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_6715631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715631 prefixEnd_6715631 := by exact prefixLift 6715631
  have htrace : WordTrace (prefixWord ++ tailWord_6715631) baseStart_6715631 baseEnd_6715631 := by
    simpa [prefixWord, tailWord_6715631, baseEnd_6715631] using wordTrace_append hprefix tailTrace_6715631
  have hstable : (prefixWord ++ tailWord_6715631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715631).length < 2 ^ (prefixWord ++ tailWord_6715631).sum := by decide
  have hdescent : baseEnd_6715631 < baseStart_6715631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715651 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 4]
def baseStart_6715651 : Nat := 118140960795 + 6715651 * 2 ^ 59
def prefixEnd_6715651 : Nat := 4983230072969 + 3 ^ 40 * 6715651 * 2
def baseEnd_6715651 : Nat := 3448356870847409718277789

theorem tailTrace_6715651 : CollatzResearch.WordTrace tailWord_6715651 prefixEnd_6715651 3448356870847409718277789 := by
  unfold tailWord_6715651
  simp only [CollatzResearch.WordTrace]
  refine ⟨244939914593350843723202807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163293276395567229148801871 244939914593350843723202807)
  ·
    refine ⟨367409871890026265584804211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244939914593350843723202807 367409871890026265584804211)
    ·
      refine ⟨551114807835039398377206317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367409871890026265584804211 551114807835039398377206317)
      ·
        refine ⟨206668052938139774391452369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 551114807835039398377206317 206668052938139774391452369)
        ·
          refine ⟨155001039703604830793589277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206668052938139774391452369 155001039703604830793589277)
          ·
            refine ⟨58125389888851811547595979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155001039703604830793589277 58125389888851811547595979)
            ·
              refine ⟨87188084833277717321393969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58125389888851811547595979 87188084833277717321393969)
              ·
                refine ⟨65391063624958287991045477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87188084833277717321393969 65391063624958287991045477)
                ·
                  refine ⟨12260824429679678998321027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65391063624958287991045477 12260824429679678998321027)
                  ·
                    refine ⟨18391236644519518497481541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12260824429679678998321027 18391236644519518497481541)
                    ·
                      refine ⟨3448356870847409718277789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18391236644519518497481541 3448356870847409718277789)
                      ·
                        rfl

theorem cell23_6715651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_6715651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715651 prefixEnd_6715651 := by exact prefixLift 6715651
  have htrace : WordTrace (prefixWord ++ tailWord_6715651) baseStart_6715651 baseEnd_6715651 := by
    simpa [prefixWord, tailWord_6715651, baseEnd_6715651] using wordTrace_append hprefix tailTrace_6715651
  have hstable : (prefixWord ++ tailWord_6715651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715651).length < 2 ^ (prefixWord ++ tailWord_6715651).sum := by decide
  have hdescent : baseEnd_6715651 < baseStart_6715651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715752 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_6715752 : Nat := 118140960795 + 6715752 * 2 ^ 59
def prefixEnd_6715752 : Nat := 4983230072969 + 3 ^ 40 * 6715752 * 2
def baseEnd_6715752 : Nat := 3448408732393513823114825

theorem tailTrace_6715752 : CollatzResearch.WordTrace tailWord_6715752 prefixEnd_6715752 3448408732393513823114825 := by
  unfold tailWord_6715752
  simp only [CollatzResearch.WordTrace]
  refine ⟨122471799182992468986314755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163295732243989958648419673 122471799182992468986314755)
  ·
    refine ⟨183707698774488703479472133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122471799182992468986314755 183707698774488703479472133)
    ·
      refine ⟨34445193520216631902401025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183707698774488703479472133 34445193520216631902401025)
      ·
        refine ⟨25833895140162473926800769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34445193520216631902401025 25833895140162473926800769)
        ·
          refine ⟨19375421355121855445100577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25833895140162473926800769 19375421355121855445100577)
          ·
            refine ⟨14531566016341391583825433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19375421355121855445100577 14531566016341391583825433)
            ·
              refine ⟨10898674512256043687869075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14531566016341391583825433 10898674512256043687869075)
              ·
                refine ⟨16348011768384065531803613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10898674512256043687869075 16348011768384065531803613)
                ·
                  refine ⟨6130504413144024574426355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16348011768384065531803613 6130504413144024574426355)
                  ·
                    refine ⟨9195756619716036861639533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6130504413144024574426355 9195756619716036861639533)
                    ·
                      refine ⟨3448408732393513823114825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9195756619716036861639533 3448408732393513823114825)
                      ·
                        rfl

theorem cell23_6715752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_6715752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715752 prefixEnd_6715752 := by exact prefixLift 6715752
  have htrace : WordTrace (prefixWord ++ tailWord_6715752) baseStart_6715752 baseEnd_6715752 := by
    simpa [prefixWord, tailWord_6715752, baseEnd_6715752] using wordTrace_append hprefix tailTrace_6715752
  have hstable : (prefixWord ++ tailWord_6715752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715752).length < 2 ^ (prefixWord ++ tailWord_6715752).sum := by decide
  have hdescent : baseEnd_6715752 < baseStart_6715752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715829 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_6715829 : Nat := 118140960795 + 6715829 * 2 ^ 59
def prefixEnd_6715829 : Nat := 4983230072969 + 3 ^ 40 * 6715829 * 2
def baseEnd_6715829 : Nat := 3448448270403910021851971

theorem tailTrace_6715829 : CollatzResearch.WordTrace tailWord_6715829 prefixEnd_6715829 3448448270403910021851971 := by
  unfold tailWord_6715829
  simp only [CollatzResearch.WordTrace]
  refine ⟨244946406786705980123182541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163297604524470653415455027 244946406786705980123182541)
  ·
    refine ⟨91854902545014742546193453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244946406786705980123182541 91854902545014742546193453)
    ·
      refine ⟨34445588454380528454822545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91854902545014742546193453 34445588454380528454822545)
      ·
        refine ⟨25834191340785396341116909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34445588454380528454822545 25834191340785396341116909)
        ·
          refine ⟨9687821752794523627918841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25834191340785396341116909 9687821752794523627918841)
          ·
            refine ⟨7265866314595892720939131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9687821752794523627918841 7265866314595892720939131)
            ·
              refine ⟨10898799471893839081408697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265866314595892720939131 10898799471893839081408697)
              ·
                refine ⟨8174099603920379311056523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10898799471893839081408697 8174099603920379311056523)
                ·
                  refine ⟨12261149405880568966584785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8174099603920379311056523 12261149405880568966584785)
                  ·
                    refine ⟨9195862054410426724938589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12261149405880568966584785 9195862054410426724938589)
                    ·
                      refine ⟨3448448270403910021851971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9195862054410426724938589 3448448270403910021851971)
                      ·
                        rfl

theorem cell23_6715829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_6715829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715829 prefixEnd_6715829 := by exact prefixLift 6715829
  have htrace : WordTrace (prefixWord ++ tailWord_6715829) baseStart_6715829 baseEnd_6715829 := by
    simpa [prefixWord, tailWord_6715829, baseEnd_6715829] using wordTrace_append hprefix tailTrace_6715829
  have hstable : (prefixWord ++ tailWord_6715829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715829).length < 2 ^ (prefixWord ++ tailWord_6715829).sum := by decide
  have hdescent : baseEnd_6715829 < baseStart_6715829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715838 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_6715838 : Nat := 118140960795 + 6715838 * 2 ^ 59
def prefixEnd_6715838 : Nat := 4983230072969 + 3 ^ 40 * 6715838 * 2
def baseEnd_6715838 : Nat := 3448452891729800486639429

theorem tailTrace_6715838 : CollatzResearch.WordTrace tailWord_6715838 prefixEnd_6715838 3448452891729800486639429 := by
  unfold tailWord_6715838
  simp only [CollatzResearch.WordTrace]
  refine ⟨30618341880459171832532521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163297823362448916440173445 30618341880459171832532521)
  ·
    refine ⟨22963756410344378874399391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30618341880459171832532521 22963756410344378874399391)
    ·
      refine ⟨34445634615516568311599087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22963756410344378874399391 34445634615516568311599087)
      ·
        refine ⟨51668451923274852467398631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34445634615516568311599087 51668451923274852467398631)
        ·
          refine ⟨77502677884912278701097947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51668451923274852467398631 77502677884912278701097947)
          ·
            refine ⟨116254016827368418051646921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77502677884912278701097947 116254016827368418051646921)
            ·
              refine ⟨87190512620526313538735191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116254016827368418051646921 87190512620526313538735191)
              ·
                refine ⟨130785768930789470308102787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87190512620526313538735191 130785768930789470308102787)
                ·
                  refine ⟨196178653396184205462154181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130785768930789470308102787 196178653396184205462154181)
                  ·
                    refine ⟨36783497511784538524153909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 196178653396184205462154181 36783497511784538524153909)
                    ·
                      refine ⟨3448452891729800486639429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36783497511784538524153909 3448452891729800486639429)
                      ·
                        rfl

theorem cell23_6715838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_6715838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715838 prefixEnd_6715838 := by exact prefixLift 6715838
  have htrace : WordTrace (prefixWord ++ tailWord_6715838) baseStart_6715838 baseEnd_6715838 := by
    simpa [prefixWord, tailWord_6715838, baseEnd_6715838] using wordTrace_append hprefix tailTrace_6715838
  have hstable : (prefixWord ++ tailWord_6715838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715838).length < 2 ^ (prefixWord ++ tailWord_6715838).sum := by decide
  have hdescent : baseEnd_6715838 < baseStart_6715838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715865 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 3, 4, 2]
def baseStart_6715865 : Nat := 118140960795 + 6715865 * 2 ^ 59
def prefixEnd_6715865 : Nat := 4983230072969 + 3 ^ 40 * 6715865 * 2
def baseEnd_6715865 : Nat := 3448466755707471881001805

theorem tailTrace_6715865 : CollatzResearch.WordTrace tailWord_6715865 prefixEnd_6715865 3448466755707471881001805 := by
  unfold tailWord_6715865
  simp only [CollatzResearch.WordTrace]
  refine ⟨244947719814575558271493049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163298479876383705514328699 244947719814575558271493049)
  ·
    refine ⟨183710789860931668703619787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244947719814575558271493049 183710789860931668703619787)
    ·
      refine ⟨275566184791397503055429681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183710789860931668703619787 275566184791397503055429681)
      ·
        refine ⟨206674638593548127291572261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275566184791397503055429681 206674638593548127291572261)
        ·
          refine ⟨38751494736290273867169799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206674638593548127291572261 38751494736290273867169799)
          ·
            refine ⟨58127242104435410800754699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38751494736290273867169799 58127242104435410800754699)
            ·
              refine ⟨87190863156653116201132049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58127242104435410800754699 87190863156653116201132049)
              ·
                refine ⟨65393147367489837150849037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87190863156653116201132049 65393147367489837150849037)
                ·
                  refine ⟨24522430262808688931568389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65393147367489837150849037 24522430262808688931568389)
                  ·
                    refine ⟨4597955674276629174669073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24522430262808688931568389 4597955674276629174669073)
                    ·
                      refine ⟨3448466755707471881001805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597955674276629174669073 3448466755707471881001805)
                      ·
                        rfl

theorem cell23_6715865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 4, 2].length) (baseStart_6715865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715865 prefixEnd_6715865 := by exact prefixLift 6715865
  have htrace : WordTrace (prefixWord ++ tailWord_6715865) baseStart_6715865 baseEnd_6715865 := by
    simpa [prefixWord, tailWord_6715865, baseEnd_6715865] using wordTrace_append hprefix tailTrace_6715865
  have hstable : (prefixWord ++ tailWord_6715865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715865).length < 2 ^ (prefixWord ++ tailWord_6715865).sum := by decide
  have hdescent : baseEnd_6715865 < baseStart_6715865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715875 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 2, 6]
def baseStart_6715875 : Nat := 118140960795 + 6715875 * 2 ^ 59
def prefixEnd_6715875 : Nat := 4983230072969 + 3 ^ 40 * 6715875 * 2
def baseEnd_6715875 : Nat := 1149490630171338947292253

theorem tailTrace_6715875 : CollatzResearch.WordTrace tailWord_6715875 prefixEnd_6715875 1149490630171338947292253 := by
  unfold tailWord_6715875
  simp only [CollatzResearch.WordTrace]
  refine ⟨244948084544539329979357079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163298723029692886652904719 244948084544539329979357079)
  ·
    refine ⟨367422126816808994969035619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244948084544539329979357079 367422126816808994969035619)
    ·
      refine ⟨551133190225213492453553429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367422126816808994969035619 551133190225213492453553429)
      ·
        refine ⟨25834368291806882458760317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 551133190225213492453553429 25834368291806882458760317)
        ·
          refine ⟨9687888109427580922035119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25834368291806882458760317 9687888109427580922035119)
          ·
            refine ⟨14531832164141371383052679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9687888109427580922035119 14531832164141371383052679)
            ·
              refine ⟨21797748246212057074579019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14531832164141371383052679 21797748246212057074579019)
              ·
                refine ⟨32696622369318085611868529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21797748246212057074579019 32696622369318085611868529)
                ·
                  refine ⟨24522466776988564208901397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32696622369318085611868529 24522466776988564208901397)
                  ·
                    refine ⟨1149490630171338947292253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24522466776988564208901397 1149490630171338947292253)
                    ·
                      rfl

theorem cell23_6715875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 6].length) (baseStart_6715875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715875 prefixEnd_6715875 := by exact prefixLift 6715875
  have htrace : WordTrace (prefixWord ++ tailWord_6715875) baseStart_6715875 baseEnd_6715875 := by
    simpa [prefixWord, tailWord_6715875, baseEnd_6715875] using wordTrace_append hprefix tailTrace_6715875
  have hstable : (prefixWord ++ tailWord_6715875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715875).length < 2 ^ (prefixWord ++ tailWord_6715875).sum := by decide
  have hdescent : baseEnd_6715875 < baseStart_6715875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715882 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_6715882 : Nat := 118140960795 + 6715882 * 2 ^ 59
def prefixEnd_6715882 : Nat := 4983230072969 + 3 ^ 40 * 6715882 * 2
def baseEnd_6715882 : Nat := 3448475484878598314489227

theorem tailTrace_6715882 : CollatzResearch.WordTrace tailWord_6715882 prefixEnd_6715882 3448475484878598314489227 := by
  unfold tailWord_6715882
  simp only [CollatzResearch.WordTrace]
  refine ⟨61237084963878492543715475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163298893237009313449907933 61237084963878492543715475)
  ·
    refine ⟨91855627445817738815573213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61237084963878492543715475 91855627445817738815573213)
    ·
      refine ⟨34445860292181652055839955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91855627445817738815573213 34445860292181652055839955)
      ·
        refine ⟨51668790438272478083759933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34445860292181652055839955 51668790438272478083759933)
        ·
          refine ⟨19375796414352179281409975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51668790438272478083759933 19375796414352179281409975)
          ·
            refine ⟨29063694621528268922114963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19375796414352179281409975 29063694621528268922114963)
            ·
              refine ⟨43595541932292403383172445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29063694621528268922114963 43595541932292403383172445)
              ·
                refine ⟨16348328224609651268689667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43595541932292403383172445 16348328224609651268689667)
                ·
                  refine ⟨24522492336914476903034501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16348328224609651268689667 24522492336914476903034501)
                  ·
                    refine ⟨4597967313171464419318969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24522492336914476903034501 4597967313171464419318969)
                    ·
                      refine ⟨3448475484878598314489227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597967313171464419318969 3448475484878598314489227)
                      ·
                        rfl

theorem cell23_6715882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_6715882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715882 prefixEnd_6715882 := by exact prefixLift 6715882
  have htrace : WordTrace (prefixWord ++ tailWord_6715882) baseStart_6715882 baseEnd_6715882 := by
    simpa [prefixWord, tailWord_6715882, baseEnd_6715882] using wordTrace_append hprefix tailTrace_6715882
  have hstable : (prefixWord ++ tailWord_6715882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715882).length < 2 ^ (prefixWord ++ tailWord_6715882).sum := by decide
  have hdescent : baseEnd_6715882 < baseStart_6715882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715888 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 7]
def baseStart_6715888 : Nat := 118140960795 + 6715888 * 2 ^ 59
def prefixEnd_6715888 : Nat := 4983230072969 + 3 ^ 40 * 6715888 * 2
def baseEnd_6715888 : Nat := 383164285084725032334911

theorem tailTrace_6715888 : CollatzResearch.WordTrace tailWord_6715888 prefixEnd_6715888 383164285084725032334911 := by
  unfold tailWord_6715888
  simp only [CollatzResearch.WordTrace]
  refine ⟨122474279346746116599790159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163299039128994822133053545 122474279346746116599790159)
  ·
    refine ⟨183711419020119174899685239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122474279346746116599790159 183711419020119174899685239)
    ·
      refine ⟨275567128530178762349527859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183711419020119174899685239 275567128530178762349527859)
      ·
        refine ⟨413350692795268143524291789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275567128530178762349527859 413350692795268143524291789)
        ·
          refine ⟨155006509798225553821609421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413350692795268143524291789 155006509798225553821609421)
          ·
            refine ⟨58127441174334582683103533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155006509798225553821609421 58127441174334582683103533)
            ·
              refine ⟨21797790440375468506163825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58127441174334582683103533 21797790440375468506163825)
              ·
                refine ⟨16348342830281601379622869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21797790440375468506163825 16348342830281601379622869)
                ·
                  refine ⟨383164285084725032334911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16348342830281601379622869 383164285084725032334911)
                  ·
                    rfl

theorem cell23_6715888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 7].length) (baseStart_6715888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715888 prefixEnd_6715888 := by exact prefixLift 6715888
  have htrace : WordTrace (prefixWord ++ tailWord_6715888) baseStart_6715888 baseEnd_6715888 := by
    simpa [prefixWord, tailWord_6715888, baseEnd_6715888] using wordTrace_append hprefix tailTrace_6715888
  have hstable : (prefixWord ++ tailWord_6715888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715888).length < 2 ^ (prefixWord ++ tailWord_6715888).sum := by decide
  have hdescent : baseEnd_6715888 < baseStart_6715888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715910 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_6715910 : Nat := 118140960795 + 6715910 * 2 ^ 59
def prefixEnd_6715910 : Nat := 4983230072969 + 3 ^ 40 * 6715910 * 2
def baseEnd_6715910 : Nat := 3448489862336924204939099

theorem tailTrace_6715910 : CollatzResearch.WordTrace tailWord_6715910 prefixEnd_6715910 3448489862336924204939099 := by
  unfold tailWord_6715910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654667534356641592402537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 163299574066275020637920789 7654667534356641592402537)
  ·
    refine ⟨5741000650767481194301903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7654667534356641592402537 5741000650767481194301903)
    ·
      refine ⟨8611500976151221791452855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5741000650767481194301903 8611500976151221791452855)
      ·
        refine ⟨12917251464226832687179283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8611500976151221791452855 12917251464226832687179283)
        ·
          refine ⟨19375877196340249030768925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12917251464226832687179283 19375877196340249030768925)
          ·
            refine ⟨7265953948627593386538347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19375877196340249030768925 7265953948627593386538347)
            ·
              refine ⟨10898930922941390079807521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265953948627593386538347 10898930922941390079807521)
              ·
                refine ⟨8174198192206042559855641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10898930922941390079807521 8174198192206042559855641)
                ·
                  refine ⟨6130648644154531919891731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8174198192206042559855641 6130648644154531919891731)
                  ·
                    refine ⟨9195972966231797879837597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6130648644154531919891731 9195972966231797879837597)
                    ·
                      refine ⟨3448489862336924204939099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9195972966231797879837597 3448489862336924204939099)
                      ·
                        rfl

theorem cell23_6715910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_6715910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715910 prefixEnd_6715910 := by exact prefixLift 6715910
  have htrace : WordTrace (prefixWord ++ tailWord_6715910) baseStart_6715910 baseEnd_6715910 := by
    simpa [prefixWord, tailWord_6715910, baseEnd_6715910] using wordTrace_append hprefix tailTrace_6715910
  have hstable : (prefixWord ++ tailWord_6715910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715910).length < 2 ^ (prefixWord ++ tailWord_6715910).sum := by decide
  have hdescent : baseEnd_6715910 < baseStart_6715910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715915 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 3]
def baseStart_6715915 : Nat := 118140960795 + 6715915 * 2 ^ 59
def prefixEnd_6715915 : Nat := 4983230072969 + 3 ^ 40 * 6715915 * 2
def baseEnd_6715915 : Nat := 3448492429740196685376575

theorem tailTrace_6715915 : CollatzResearch.WordTrace tailWord_6715915 prefixEnd_6715915 3448492429740196685376575 := by
  unfold tailWord_6715915
  simp only [CollatzResearch.WordTrace]
  refine ⟨244949543464394416810813199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163299695642929611207208799 244949543464394416810813199)
  ·
    refine ⟨367424315196591625216219799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244949543464394416810813199 367424315196591625216219799)
    ·
      refine ⟨551136472794887437824329699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367424315196591625216219799 551136472794887437824329699)
      ·
        refine ⟨826704709192331156736494549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551136472794887437824329699 826704709192331156736494549)
        ·
          refine ⟨19375891621695261486011591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 826704709192331156736494549 19375891621695261486011591)
          ·
            refine ⟨29063837432542892229017387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19375891621695261486011591 29063837432542892229017387)
            ·
              refine ⟨43595756148814338343526081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29063837432542892229017387 43595756148814338343526081)
              ·
                refine ⟨32696817111610753757644561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43595756148814338343526081 32696817111610753757644561)
                ·
                  refine ⟨24522612833708065318233421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32696817111610753757644561 24522612833708065318233421)
                  ·
                    refine ⟨9195979812640524494337533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24522612833708065318233421 9195979812640524494337533)
                    ·
                      refine ⟨3448492429740196685376575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9195979812640524494337533 3448492429740196685376575)
                      ·
                        rfl

theorem cell23_6715915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 3].length) (baseStart_6715915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715915 prefixEnd_6715915 := by exact prefixLift 6715915
  have htrace : WordTrace (prefixWord ++ tailWord_6715915) baseStart_6715915 baseEnd_6715915 := by
    simpa [prefixWord, tailWord_6715915, baseEnd_6715915] using wordTrace_append hprefix tailTrace_6715915
  have hstable : (prefixWord ++ tailWord_6715915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715915).length < 2 ^ (prefixWord ++ tailWord_6715915).sum := by decide
  have hdescent : baseEnd_6715915 < baseStart_6715915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715916 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 2, 2, 2]
def baseStart_6715916 : Nat := 118140960795 + 6715916 * 2 ^ 59
def prefixEnd_6715916 : Nat := 4983230072969 + 3 ^ 40 * 6715916 * 2
def baseEnd_6715916 : Nat := 3448492943220851181464071

theorem tailTrace_6715916 : CollatzResearch.WordTrace tailWord_6715916 prefixEnd_6715916 3448492943220851181464071 := by
  unfold tailWord_6715916
  simp only [CollatzResearch.WordTrace]
  refine ⟨122474789968695396990799801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163299719958260529321066401 122474789968695396990799801)
  ·
    refine ⟨91856092476521547743099851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122474789968695396990799801 91856092476521547743099851)
    ·
      refine ⟨137784138714782321614649777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91856092476521547743099851 137784138714782321614649777)
      ·
        refine ⟨103338104036086741210987333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137784138714782321614649777 103338104036086741210987333)
        ·
          refine ⟨19375894506766263977060125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103338104036086741210987333 19375894506766263977060125)
          ·
            refine ⟨7265960440037348991397547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19375894506766263977060125 7265960440037348991397547)
            ·
              refine ⟨10898940660056023487096321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265960440037348991397547 10898940660056023487096321)
              ·
                refine ⟨8174205495042017615322241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10898940660056023487096321 8174205495042017615322241)
                ·
                  refine ⟨6130654121281513211491681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8174205495042017615322241 6130654121281513211491681)
                  ·
                    refine ⟨4597990590961134908618761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6130654121281513211491681 4597990590961134908618761)
                    ·
                      refine ⟨3448492943220851181464071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4597990590961134908618761 3448492943220851181464071)
                      ·
                        rfl

theorem cell23_6715916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_6715916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715916 prefixEnd_6715916 := by exact prefixLift 6715916
  have htrace : WordTrace (prefixWord ++ tailWord_6715916) baseStart_6715916 baseEnd_6715916 := by
    simpa [prefixWord, tailWord_6715916, baseEnd_6715916] using wordTrace_append hprefix tailTrace_6715916
  have hstable : (prefixWord ++ tailWord_6715916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715916).length < 2 ^ (prefixWord ++ tailWord_6715916).sum := by decide
  have hdescent : baseEnd_6715916 < baseStart_6715916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715955 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 4]
def baseStart_6715955 : Nat := 118140960795 + 6715955 * 2 ^ 59
def prefixEnd_6715955 : Nat := 4983230072969 + 3 ^ 40 * 6715955 * 2
def baseEnd_6715955 : Nat := 3448512968966376528876391

theorem tailTrace_6715955 : CollatzResearch.WordTrace tailWord_6715955 prefixEnd_6715955 3448512968966376528876391 := by
  unfold tailWord_6715955
  simp only [CollatzResearch.WordTrace]
  refine ⟨244951002384249503642269319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163300668256166335761512879 244951002384249503642269319)
  ·
    refine ⟨367426503576374255463403979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244951002384249503642269319 367426503576374255463403979)
    ·
      refine ⟨551139755364561383195105969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367426503576374255463403979 551139755364561383195105969)
      ·
        refine ⟨413354816523421037396329477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 551139755364561383195105969 413354816523421037396329477)
        ·
          refine ⟨77504028098141444511811777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 413354816523421037396329477 77504028098141444511811777)
          ·
            refine ⟨58128021073606083383858833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77504028098141444511811777 58128021073606083383858833)
            ·
              refine ⟨43596015805204562537894125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58128021073606083383858833 43596015805204562537894125)
              ·
                refine ⟨16348505926951710951710297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43596015805204562537894125 16348505926951710951710297)
                ·
                  refine ⟨12261379445213783213782723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16348505926951710951710297 12261379445213783213782723)
                  ·
                    refine ⟨18392069167820674820674085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12261379445213783213782723 18392069167820674820674085)
                    ·
                      refine ⟨3448512968966376528876391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18392069167820674820674085 3448512968966376528876391)
                      ·
                        rfl

theorem cell23_6715955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 4].length) (baseStart_6715955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715955 prefixEnd_6715955 := by exact prefixLift 6715955
  have htrace : WordTrace (prefixWord ++ tailWord_6715955) baseStart_6715955 baseEnd_6715955 := by
    simpa [prefixWord, tailWord_6715955, baseEnd_6715955] using wordTrace_append hprefix tailTrace_6715955
  have hstable : (prefixWord ++ tailWord_6715955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715955).length < 2 ^ (prefixWord ++ tailWord_6715955).sum := by decide
  have hdescent : baseEnd_6715955 < baseStart_6715955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715968 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_6715968 : Nat := 118140960795 + 6715968 * 2 ^ 59
def prefixEnd_6715968 : Nat := 4983230072969 + 3 ^ 40 * 6715968 * 2
def baseEnd_6715968 : Nat := 3448519644214884978013831

theorem tailTrace_6715968 : CollatzResearch.WordTrace tailWord_6715968 prefixEnd_6715968 3448519644214884978013831 := by
  unfold tailWord_6715968
  simp only [CollatzResearch.WordTrace]
  refine ⟨122475738266601203431246279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163300984355468271241661705 122475738266601203431246279)
  ·
    refine ⟨183713607399901805146869419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122475738266601203431246279 183713607399901805146869419)
    ·
      refine ⟨275570411099852707720304129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183713607399901805146869419 275570411099852707720304129)
      ·
        refine ⟨206677808324889530790228097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275570411099852707720304129 206677808324889530790228097)
        ·
          refine ⟨155008356243667148092671073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206677808324889530790228097 155008356243667148092671073)
          ·
            refine ⟨116256267182750361069503305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155008356243667148092671073 116256267182750361069503305)
            ·
              refine ⟨87192200387062770802127479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116256267182750361069503305 87192200387062770802127479)
              ·
                refine ⟨130788300580594156203191219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87192200387062770802127479 130788300580594156203191219)
                ·
                  refine ⟨196182450870891234304786829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130788300580594156203191219 196182450870891234304786829)
                  ·
                    refine ⟨73568419076584212864295061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196182450870891234304786829 73568419076584212864295061)
                    ·
                      refine ⟨3448519644214884978013831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73568419076584212864295061 3448519644214884978013831)
                      ·
                        rfl

theorem cell23_6715968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_6715968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715968 prefixEnd_6715968 := by exact prefixLift 6715968
  have htrace : WordTrace (prefixWord ++ tailWord_6715968) baseStart_6715968 baseEnd_6715968 := by
    simpa [prefixWord, tailWord_6715968, baseEnd_6715968] using wordTrace_append hprefix tailTrace_6715968
  have hstable : (prefixWord ++ tailWord_6715968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715968).length < 2 ^ (prefixWord ++ tailWord_6715968).sum := by decide
  have hdescent : baseEnd_6715968 < baseStart_6715968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6715982 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_6715982 : Nat := 118140960795 + 6715982 * 2 ^ 59
def prefixEnd_6715982 : Nat := 4983230072969 + 3 ^ 40 * 6715982 * 2
def baseEnd_6715982 : Nat := 1149508944314682641079589

theorem tailTrace_6715982 : CollatzResearch.WordTrace tailWord_6715982 prefixEnd_6715982 1149508944314682641079589 := by
  unfold tailWord_6715982
  simp only [CollatzResearch.WordTrace]
  refine ⟨30618998394393960906687775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163301324770101124835668133 30618998394393960906687775)
  ·
    refine ⟨45928497591590941360031663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30618998394393960906687775 45928497591590941360031663)
    ·
      refine ⟨68892746387386412040047495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45928497591590941360031663 68892746387386412040047495)
      ·
        refine ⟨103339119581079618060071243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68892746387386412040047495 103339119581079618060071243)
        ·
          refine ⟨155008679371619427090106865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103339119581079618060071243 155008679371619427090106865)
          ·
            refine ⟨116256509528714570317580149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155008679371619427090106865 116256509528714570317580149)
            ·
              refine ⟨10899047768316990967273139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116256509528714570317580149 10899047768316990967273139)
              ·
                refine ⟨16348571652475486450909709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10899047768316990967273139 16348571652475486450909709)
                ·
                  refine ⟨6130714369678307419091141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16348571652475486450909709 6130714369678307419091141)
                  ·
                    refine ⟨1149508944314682641079589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6130714369678307419091141 1149508944314682641079589)
                    ·
                      rfl

theorem cell23_6715982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_6715982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6715982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6715982 prefixEnd_6715982 := by exact prefixLift 6715982
  have htrace : WordTrace (prefixWord ++ tailWord_6715982) baseStart_6715982 baseEnd_6715982 := by
    simpa [prefixWord, tailWord_6715982, baseEnd_6715982] using wordTrace_append hprefix tailTrace_6715982
  have hstable : (prefixWord ++ tailWord_6715982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6715982).length < 2 ^ (prefixWord ++ tailWord_6715982).sum := by decide
  have hdescent : baseEnd_6715982 < baseStart_6715982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6715982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716079 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 1, 1, 4]
def baseStart_6716079 : Nat := 118140960795 + 6716079 * 2 ^ 59
def prefixEnd_6716079 : Nat := 4983230072969 + 3 ^ 40 * 6716079 * 2
def baseEnd_6716079 : Nat := 3448576640567534043725821

theorem tailTrace_6716079 : CollatzResearch.WordTrace tailWord_6716079 prefixEnd_6716079 3448576640567534043725821 := by
  unfold tailWord_6716079
  simp only [CollatzResearch.WordTrace]
  refine ⟨244955525035800272819783291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163303683357200181879855527 244955525035800272819783291)
  ·
    refine ⟨367433287553700409229674937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244955525035800272819783291 367433287553700409229674937)
    ·
      refine ⟨275574965665275306922256203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367433287553700409229674937 275574965665275306922256203)
      ·
        refine ⟨413362448497912960383384305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275574965665275306922256203 413362448497912960383384305)
        ·
          refine ⟨310021836373434720287538229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413362448497912960383384305 310021836373434720287538229)
          ·
            refine ⟨29064547160009505026956709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310021836373434720287538229 29064547160009505026956709)
            ·
              refine ⟨5449602592501782192554383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29064547160009505026956709 5449602592501782192554383)
              ·
                refine ⟨8174403888752673288831575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5449602592501782192554383 8174403888752673288831575)
                ·
                  refine ⟨12261605833129009933247363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8174403888752673288831575 12261605833129009933247363)
                  ·
                    refine ⟨18392408749693514899871045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12261605833129009933247363 18392408749693514899871045)
                    ·
                      refine ⟨3448576640567534043725821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18392408749693514899871045 3448576640567534043725821)
                      ·
                        rfl

theorem cell23_6716079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 1, 1, 4].length) (baseStart_6716079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716079 prefixEnd_6716079 := by exact prefixLift 6716079
  have htrace : WordTrace (prefixWord ++ tailWord_6716079) baseStart_6716079 baseEnd_6716079 := by
    simpa [prefixWord, tailWord_6716079, baseEnd_6716079] using wordTrace_append hprefix tailTrace_6716079
  have hstable : (prefixWord ++ tailWord_6716079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716079).length < 2 ^ (prefixWord ++ tailWord_6716079).sum := by decide
  have hdescent : baseEnd_6716079 < baseStart_6716079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716096 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 3, 2, 2]
def baseStart_6716096 : Nat := 118140960795 + 6716096 * 2 ^ 59
def prefixEnd_6716096 : Nat := 4983230072969 + 3 ^ 40 * 6716096 * 2
def baseEnd_6716096 : Nat := 3448585369738660477213243

theorem tailTrace_6716096 : CollatzResearch.WordTrace tailWord_6716096 prefixEnd_6716096 3448585369738660477213243 := by
  unfold tailWord_6716096
  simp only [CollatzResearch.WordTrace]
  refine ⟨122478072538369342361576071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163304096717825789815434761 122478072538369342361576071)
  ·
    refine ⟨183717108807554013542364107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122478072538369342361576071 183717108807554013542364107)
    ·
      refine ⟨275575663211331020313546161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183717108807554013542364107 275575663211331020313546161)
      ·
        refine ⟨206681747408498265235159621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275575663211331020313546161 206681747408498265235159621)
        ·
          refine ⟨38752827639093424731592429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206681747408498265235159621 38752827639093424731592429)
          ·
            refine ⟨14532310364660034274347161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38752827639093424731592429 14532310364660034274347161)
            ·
              refine ⟨10899232773495025705760371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14532310364660034274347161 10899232773495025705760371)
              ·
                refine ⟨16348849160242538558640557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10899232773495025705760371 16348849160242538558640557)
                ·
                  refine ⟨6130818435090951959490209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16348849160242538558640557 6130818435090951959490209)
                  ·
                    refine ⟨4598113826318213969617657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6130818435090951959490209 4598113826318213969617657)
                    ·
                      refine ⟨3448585369738660477213243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598113826318213969617657 3448585369738660477213243)
                      ·
                        rfl

theorem cell23_6716096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_6716096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716096 prefixEnd_6716096 := by exact prefixLift 6716096
  have htrace : WordTrace (prefixWord ++ tailWord_6716096) baseStart_6716096 baseEnd_6716096 := by
    simpa [prefixWord, tailWord_6716096, baseEnd_6716096] using wordTrace_append hprefix tailTrace_6716096
  have hstable : (prefixWord ++ tailWord_6716096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716096).length < 2 ^ (prefixWord ++ tailWord_6716096).sum := by decide
  have hdescent : baseEnd_6716096 < baseStart_6716096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716106 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_6716106 : Nat := 118140960795 + 6716106 * 2 ^ 59
def prefixEnd_6716106 : Nat := 4983230072969 + 3 ^ 40 * 6716106 * 2
def baseEnd_6716106 : Nat := 1149530168181735146029399

theorem tailTrace_6716106 : CollatzResearch.WordTrace tailWord_6716106 prefixEnd_6716106 1149530168181735146029399 := by
  unfold tailWord_6716106
  simp only [CollatzResearch.WordTrace]
  refine ⟨61239127451675614107754043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163304339871134970954010781 61239127451675614107754043)
  ·
    refine ⟨91858691177513421161631065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61239127451675614107754043 91858691177513421161631065)
    ·
      refine ⟨68894018383135065871223299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91858691177513421161631065 68894018383135065871223299)
      ·
        refine ⟨103341027574702598806834949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68894018383135065871223299 103341027574702598806834949)
        ·
          refine ⟨19376442670256737276281553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103341027574702598806834949 19376442670256737276281553)
          ·
            refine ⟨14532332002692552957211165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19376442670256737276281553 14532332002692552957211165)
            ·
              refine ⟨5449624501009707358954187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14532332002692552957211165 5449624501009707358954187)
              ·
                refine ⟨8174436751514561038431281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5449624501009707358954187 8174436751514561038431281)
                ·
                  refine ⟨6130827563635920778823461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8174436751514561038431281 6130827563635920778823461)
                  ·
                    refine ⟨1149530168181735146029399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6130827563635920778823461 1149530168181735146029399)
                    ·
                      rfl

theorem cell23_6716106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_6716106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716106 prefixEnd_6716106 := by exact prefixLift 6716106
  have htrace : WordTrace (prefixWord ++ tailWord_6716106) baseStart_6716106 baseEnd_6716106 := by
    simpa [prefixWord, tailWord_6716106, baseEnd_6716106] using wordTrace_append hprefix tailTrace_6716106
  have hstable : (prefixWord ++ tailWord_6716106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716106).length < 2 ^ (prefixWord ++ tailWord_6716106).sum := by decide
  have hdescent : baseEnd_6716106 < baseStart_6716106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716129 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 3]
def baseStart_6716129 : Nat := 118140960795 + 6716129 * 2 ^ 59
def prefixEnd_6716129 : Nat := 4983230072969 + 3 ^ 40 * 6716129 * 2
def baseEnd_6716129 : Nat := 3448602314600258848100591

theorem tailTrace_6716129 : CollatzResearch.WordTrace tailWord_6716129 prefixEnd_6716129 3448602314600258848100591 := by
  unfold tailWord_6716129
  simp only [CollatzResearch.WordTrace]
  refine ⟨244957348685619131359103441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163304899123746087572735627 244957348685619131359103441)
  ·
    refine ⟨183718011514214348519327581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244957348685619131359103441 183718011514214348519327581)
    ·
      refine ⟨68894254317830380694747843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183718011514214348519327581 68894254317830380694747843)
      ·
        refine ⟨103341381476745571042121765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68894254317830380694747843 103341381476745571042121765)
        ·
          refine ⟨19376509026889794570397831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103341381476745571042121765 19376509026889794570397831)
          ·
            refine ⟨29064763540334691855596747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19376509026889794570397831 29064763540334691855596747)
            ·
              refine ⟨43597145310502037783395121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29064763540334691855596747 43597145310502037783395121)
              ·
                refine ⟨32697858982876528337546341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43597145310502037783395121 32697858982876528337546341)
                ·
                  refine ⟨6130848559289349063289939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32697858982876528337546341 6130848559289349063289939)
                  ·
                    refine ⟨9196272838934023594934909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6130848559289349063289939 9196272838934023594934909)
                    ·
                      refine ⟨3448602314600258848100591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9196272838934023594934909 3448602314600258848100591)
                      ·
                        rfl

theorem cell23_6716129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_6716129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716129 prefixEnd_6716129 := by exact prefixLift 6716129
  have htrace : WordTrace (prefixWord ++ tailWord_6716129) baseStart_6716129 baseEnd_6716129 := by
    simpa [prefixWord, tailWord_6716129, baseEnd_6716129] using wordTrace_append hprefix tailTrace_6716129
  have hstable : (prefixWord ++ tailWord_6716129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716129).length < 2 ^ (prefixWord ++ tailWord_6716129).sum := by decide
  have hdescent : baseEnd_6716129 < baseStart_6716129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716165 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_6716165 : Nat := 118140960795 + 6716165 * 2 ^ 59
def prefixEnd_6716165 : Nat := 4983230072969 + 3 ^ 40 * 6716165 * 2
def baseEnd_6716165 : Nat := 3448620799903820707250425

theorem tailTrace_6716165 : CollatzResearch.WordTrace tailWord_6716165 prefixEnd_6716165 3448620799903820707250425 := by
  unfold tailWord_6716165
  simp only [CollatzResearch.WordTrace]
  refine ⟨244958661713488709507413949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163305774475659139671609299 244958661713488709507413949)
  ·
    refine ⟨91859498142558266065280231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244958661713488709507413949 91859498142558266065280231)
    ·
      refine ⟨137789247213837399097920347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91859498142558266065280231 137789247213837399097920347)
      ·
        refine ⟨206683870820756098646880521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137789247213837399097920347 206683870820756098646880521)
        ·
          refine ⟨155012903115567073985160391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206683870820756098646880521 155012903115567073985160391)
          ·
            refine ⟨232519354673350610977740587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155012903115567073985160391 232519354673350610977740587)
            ·
              refine ⟨348779032010025916466610881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232519354673350610977740587 348779032010025916466610881)
              ·
                refine ⟨261584274007519437349958161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348779032010025916466610881 261584274007519437349958161)
                ·
                  refine ⟨196188205505639578012468621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261584274007519437349958161 196188205505639578012468621)
                  ·
                    refine ⟨73570577064614841754675733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196188205505639578012468621 73570577064614841754675733)
                    ·
                      refine ⟨3448620799903820707250425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73570577064614841754675733 3448620799903820707250425)
                      ·
                        rfl

theorem cell23_6716165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_6716165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716165 prefixEnd_6716165 := by exact prefixLift 6716165
  have htrace : WordTrace (prefixWord ++ tailWord_6716165) baseStart_6716165 baseEnd_6716165 := by
    simpa [prefixWord, tailWord_6716165, baseEnd_6716165] using wordTrace_append hprefix tailTrace_6716165
  have hstable : (prefixWord ++ tailWord_6716165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716165).length < 2 ^ (prefixWord ++ tailWord_6716165).sum := by decide
  have hdescent : baseEnd_6716165 < baseStart_6716165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716175 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 9]
def baseStart_6716175 : Nat := 118140960795 + 6716175 * 2 ^ 59
def prefixEnd_6716175 : Nat := 4983230072969 + 3 ^ 40 * 6716175 * 2
def baseEnd_6716175 : Nat := 383180659412262852013931

theorem tailTrace_6716175 : CollatzResearch.WordTrace tailWord_6716175 prefixEnd_6716175 383180659412262852013931 := by
  unfold tailWord_6716175
  simp only [CollatzResearch.WordTrace]
  refine ⟨244959026443452481215277979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163306017628968320810185319 244959026443452481215277979)
  ·
    refine ⟨367438539665178721822916969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244959026443452481215277979 367438539665178721822916969)
    ·
      refine ⟨275578904748884041367187727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367438539665178721822916969 275578904748884041367187727)
      ·
        refine ⟨413368357123326062050781591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275578904748884041367187727 413368357123326062050781591)
        ·
          refine ⟨620052535684989093076172387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413368357123326062050781591 620052535684989093076172387)
          ·
            refine ⟨930078803527483639614258581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620052535684989093076172387 930078803527483639614258581)
            ·
              refine ⟨43597443915350795606918371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 930078803527483639614258581 43597443915350795606918371)
              ·
                refine ⟨65396165873026193410377557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43597443915350795606918371 65396165873026193410377557)
                ·
                  refine ⟨383180659412262852013931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65396165873026193410377557 383180659412262852013931)
                  ·
                    rfl

theorem cell23_6716175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 9].length) (baseStart_6716175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716175 prefixEnd_6716175 := by exact prefixLift 6716175
  have htrace : WordTrace (prefixWord ++ tailWord_6716175) baseStart_6716175 baseEnd_6716175 := by
    simpa [prefixWord, tailWord_6716175, baseEnd_6716175] using wordTrace_append hprefix tailTrace_6716175
  have hstable : (prefixWord ++ tailWord_6716175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716175).length < 2 ^ (prefixWord ++ tailWord_6716175).sum := by decide
  have hdescent : baseEnd_6716175 < baseStart_6716175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716185 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_6716185 : Nat := 118140960795 + 6716185 * 2 ^ 59
def prefixEnd_6716185 : Nat := 4983230072969 + 3 ^ 40 * 6716185 * 2
def baseEnd_6716185 : Nat := 3448631069516910629000333

theorem tailTrace_6716185 : CollatzResearch.WordTrace tailWord_6716185 prefixEnd_6716185 3448631069516910629000333 := by
  unfold tailWord_6716185
  simp only [CollatzResearch.WordTrace]
  refine ⟨244959391173416252923142009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163306260782277501948761339 244959391173416252923142009)
  ·
    refine ⟨183719543380062189692356507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244959391173416252923142009 183719543380062189692356507)
    ·
      refine ⟨275579315070093284538534761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183719543380062189692356507 275579315070093284538534761)
      ·
        refine ⟨206684486302569963403901071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275579315070093284538534761 206684486302569963403901071)
        ·
          refine ⟨310026729453854945105851607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206684486302569963403901071 310026729453854945105851607)
          ·
            refine ⟨465040094180782417658777411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310026729453854945105851607 465040094180782417658777411)
            ·
              refine ⟨697560141271173626488166117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465040094180782417658777411 697560141271173626488166117)
              ·
                refine ⟨130792526488345054966531147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697560141271173626488166117 130792526488345054966531147)
                ·
                  refine ⟨196188789732517582449796721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130792526488345054966531147 196188789732517582449796721)
                  ·
                    refine ⟨147141592299388186837347541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196188789732517582449796721 147141592299388186837347541)
                    ·
                      refine ⟨3448631069516910629000333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 147141592299388186837347541 3448631069516910629000333)
                      ·
                        rfl

theorem cell23_6716185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_6716185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716185 prefixEnd_6716185 := by exact prefixLift 6716185
  have htrace : WordTrace (prefixWord ++ tailWord_6716185) baseStart_6716185 baseEnd_6716185 := by
    simpa [prefixWord, tailWord_6716185, baseEnd_6716185] using wordTrace_append hprefix tailTrace_6716185
  have hstable : (prefixWord ++ tailWord_6716185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716185).length < 2 ^ (prefixWord ++ tailWord_6716185).sum := by decide
  have hdescent : baseEnd_6716185 < baseStart_6716185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716209 : List Nat := [1, 2, 2, 3, 2, 1, 3, 4, 5]
def baseStart_6716209 : Nat := 118140960795 + 6716209 * 2 ^ 59
def prefixEnd_6716209 : Nat := 4983230072969 + 3 ^ 40 * 6716209 * 2
def baseEnd_6716209 : Nat := 383182599228068726122247

theorem tailTrace_6716209 : CollatzResearch.WordTrace tailWord_6716209 prefixEnd_6716209 383182599228068726122247 := by
  unfold tailWord_6716209
  simp only [CollatzResearch.WordTrace]
  refine ⟨244960266525329305022015681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163306844350219536681343787 244960266525329305022015681)
  ·
    refine ⟨183720199893996978766511761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244960266525329305022015681 183720199893996978766511761)
    ·
      refine ⟨137790149920497734074883821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183720199893996978766511761 137790149920497734074883821)
      ·
        refine ⟨51671306220186650278081433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137790149920497734074883821 51671306220186650278081433)
        ·
          refine ⟨38753479665139987708561075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51671306220186650278081433 38753479665139987708561075)
          ·
            refine ⟨58130219497709981562841613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38753479665139987708561075 58130219497709981562841613)
            ·
              refine ⟨21798832311641243086065605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58130219497709981562841613 21798832311641243086065605)
              ·
                refine ⟨4087281058432733078637301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21798832311641243086065605 4087281058432733078637301)
                ·
                  refine ⟨383182599228068726122247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4087281058432733078637301 383182599228068726122247)
                  ·
                    rfl

theorem cell23_6716209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 5].length) (baseStart_6716209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716209 prefixEnd_6716209 := by exact prefixLift 6716209
  have htrace : WordTrace (prefixWord ++ tailWord_6716209) baseStart_6716209 baseEnd_6716209 := by
    simpa [prefixWord, tailWord_6716209, baseEnd_6716209] using wordTrace_append hprefix tailTrace_6716209
  have hstable : (prefixWord ++ tailWord_6716209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716209).length < 2 ^ (prefixWord ++ tailWord_6716209).sum := by decide
  have hdescent : baseEnd_6716209 < baseStart_6716209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716310 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6716310 : Nat := 118140960795 + 6716310 * 2 ^ 59
def prefixEnd_6716310 : Nat := 4983230072969 + 3 ^ 40 * 6716310 * 2
def baseEnd_6716310 : Nat := 3448695254598722639937259

theorem tailTrace_6716310 : CollatzResearch.WordTrace tailWord_6716310 prefixEnd_6716310 3448695254598722639937259 := by
  unfold tailWord_6716310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15310246893622712454465149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163309300198642266180961589 15310246893622712454465149)
  ·
    refine ⟨5741342585108517170424431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15310246893622712454465149 5741342585108517170424431)
    ·
      refine ⟨8612013877662775755636647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5741342585108517170424431 8612013877662775755636647)
      ·
        refine ⟨12918020816494163633454971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8612013877662775755636647 12918020816494163633454971)
        ·
          refine ⟨19377031224741245450182457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12918020816494163633454971 19377031224741245450182457)
          ·
            refine ⟨14532773418555934087636843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19377031224741245450182457 14532773418555934087636843)
            ·
              refine ⟨21799160127833901131455265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14532773418555934087636843 21799160127833901131455265)
              ·
                refine ⟨16349370095875425848591449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21799160127833901131455265 16349370095875425848591449)
                ·
                  refine ⟨12262027571906569386443587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16349370095875425848591449 12262027571906569386443587)
                  ·
                    refine ⟨18393041357859854079665381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12262027571906569386443587 18393041357859854079665381)
                    ·
                      refine ⟨3448695254598722639937259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18393041357859854079665381 3448695254598722639937259)
                      ·
                        rfl

theorem cell23_6716310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6716310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716310 prefixEnd_6716310 := by exact prefixLift 6716310
  have htrace : WordTrace (prefixWord ++ tailWord_6716310) baseStart_6716310 baseEnd_6716310 := by
    simpa [prefixWord, tailWord_6716310, baseEnd_6716310] using wordTrace_append hprefix tailTrace_6716310
  have hstable : (prefixWord ++ tailWord_6716310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716310).length < 2 ^ (prefixWord ++ tailWord_6716310).sum := by decide
  have hdescent : baseEnd_6716310 < baseStart_6716310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716333 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 6]
def baseStart_6716333 : Nat := 118140960795 + 6716333 * 2 ^ 59
def prefixEnd_6716333 : Nat := 4983230072969 + 3 ^ 40 * 6716333 * 2
def baseEnd_6716333 : Nat := 383189673850419561105517

theorem tailTrace_6716333 : CollatzResearch.WordTrace tailWord_6716333 prefixEnd_6716333 383189673850419561105517 := by
  unfold tailWord_6716333
  simp only [CollatzResearch.WordTrace]
  refine ⟨244964789176880074199529653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163309859451253382799686435 244964789176880074199529653)
  ·
    refine ⟨22965448985332506956205905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 244964789176880074199529653 22965448985332506956205905)
    ·
      refine ⟨17224086738999380217154429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22965448985332506956205905 17224086738999380217154429)
      ·
        refine ⟨6459032527124767581432911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17224086738999380217154429 6459032527124767581432911)
        ·
          refine ⟨9688548790687151372149367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459032527124767581432911 9688548790687151372149367)
          ·
            refine ⟨14532823186030727058224051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9688548790687151372149367 14532823186030727058224051)
            ·
              refine ⟨21799234779046090587336077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14532823186030727058224051 21799234779046090587336077)
              ·
                refine ⟨8174713042142283970251029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21799234779046090587336077 8174713042142283970251029)
                ·
                  refine ⟨383189673850419561105517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8174713042142283970251029 383189673850419561105517)
                  ·
                    rfl

theorem cell23_6716333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_6716333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716333 prefixEnd_6716333 := by exact prefixLift 6716333
  have htrace : WordTrace (prefixWord ++ tailWord_6716333) baseStart_6716333 baseEnd_6716333 := by
    simpa [prefixWord, tailWord_6716333, baseEnd_6716333] using wordTrace_append hprefix tailTrace_6716333
  have hstable : (prefixWord ++ tailWord_6716333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716333).length < 2 ^ (prefixWord ++ tailWord_6716333).sum := by decide
  have hdescent : baseEnd_6716333 < baseStart_6716333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716359 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 6, 4]
def baseStart_6716359 : Nat := 118140960795 + 6716359 * 2 ^ 59
def prefixEnd_6716359 : Nat := 4983230072969 + 3 ^ 40 * 6716359 * 2
def baseEnd_6716359 : Nat := 1149573471716930982741511

theorem tailTrace_6716359 : CollatzResearch.WordTrace tailWord_6716359 prefixEnd_6716359 1149573471716930982741511 := by
  unfold tailWord_6716359
  simp only [CollatzResearch.WordTrace]
  refine ⟨244965737474785880639976131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163310491649857253759984087 244965737474785880639976131)
  ·
    refine ⟨367448606212178820959964197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244965737474785880639976131 367448606212178820959964197)
    ·
      refine ⟨68896613664783528929993287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367448606212178820959964197 68896613664783528929993287)
      ·
        refine ⟨103344920497175293394989931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68896613664783528929993287 103344920497175293394989931)
        ·
          refine ⟨155017380745762940092484897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103344920497175293394989931 155017380745762940092484897)
          ·
            refine ⟨116263035559322205069363673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155017380745762940092484897 116263035559322205069363673)
            ·
              refine ⟨87197276669491653802022755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116263035559322205069363673 87197276669491653802022755)
              ·
                refine ⟨130795915004237480703034133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87197276669491653802022755 130795915004237480703034133)
                ·
                  refine ⟨6131058515823631907954725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130795915004237480703034133 6131058515823631907954725)
                  ·
                    refine ⟨1149573471716930982741511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6131058515823631907954725 1149573471716930982741511)
                    ·
                      rfl

theorem cell23_6716359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_6716359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716359 prefixEnd_6716359 := by exact prefixLift 6716359
  have htrace : WordTrace (prefixWord ++ tailWord_6716359) baseStart_6716359 baseEnd_6716359 := by
    simpa [prefixWord, tailWord_6716359, baseEnd_6716359] using wordTrace_append hprefix tailTrace_6716359
  have hstable : (prefixWord ++ tailWord_6716359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716359).length < 2 ^ (prefixWord ++ tailWord_6716359).sum := by decide
  have hdescent : baseEnd_6716359 < baseStart_6716359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716376 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 2, 4]
def baseStart_6716376 : Nat := 118140960795 + 6716376 * 2 ^ 59
def prefixEnd_6716376 : Nat := 4983230072969 + 3 ^ 40 * 6716376 * 2
def baseEnd_6716376 : Nat := 1149576381440639793903985

theorem tailTrace_6716376 : CollatzResearch.WordTrace tailWord_6716376 prefixEnd_6716376 1149576381440639793903985 := by
  unfold tailWord_6716376
  simp only [CollatzResearch.WordTrace]
  refine ⟨122483178757862146271672491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163310905010482861695563321 122483178757862146271672491)
  ·
    refine ⟨183724768136793219407508737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122483178757862146271672491 183724768136793219407508737)
    ·
      refine ⟨137793576102594914555631553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183724768136793219407508737 137793576102594914555631553)
      ·
        refine ⟨103345182076946185916723665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137793576102594914555631553 103345182076946185916723665)
        ·
          refine ⟨77508886557709639437542749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103345182076946185916723665 77508886557709639437542749)
          ·
            refine ⟨29065832459141114789078531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77508886557709639437542749 29065832459141114789078531)
            ·
              refine ⟨43598748688711672183617797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29065832459141114789078531 43598748688711672183617797)
              ·
                refine ⟨8174765379133438534428337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43598748688711672183617797 8174765379133438534428337)
                ·
                  refine ⟨6131074034350078900821253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8174765379133438534428337 6131074034350078900821253)
                  ·
                    refine ⟨1149576381440639793903985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6131074034350078900821253 1149576381440639793903985)
                    ·
                      rfl

theorem cell23_6716376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_6716376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716376 prefixEnd_6716376 := by exact prefixLift 6716376
  have htrace : WordTrace (prefixWord ++ tailWord_6716376) baseStart_6716376 baseEnd_6716376 := by
    simpa [prefixWord, tailWord_6716376, baseEnd_6716376] using wordTrace_append hprefix tailTrace_6716376
  have hstable : (prefixWord ++ tailWord_6716376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716376).length < 2 ^ (prefixWord ++ tailWord_6716376).sum := by decide
  have hdescent : baseEnd_6716376 < baseStart_6716376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716377 : List Nat := [1, 2, 1, 2, 5, 3, 2, 2, 1, 1, 3]
def baseStart_6716377 : Nat := 118140960795 + 6716377 * 2 ^ 59
def prefixEnd_6716377 : Nat := 4983230072969 + 3 ^ 40 * 6716377 * 2
def baseEnd_6716377 : Nat := 3448729657802573877799451

theorem tailTrace_6716377 : CollatzResearch.WordTrace tailWord_6716377 prefixEnd_6716377 3448729657802573877799451 := by
  unfold tailWord_6716377
  simp only [CollatzResearch.WordTrace]
  refine ⟨244966393988720669714131385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163310929325813779809420923 244966393988720669714131385)
  ·
    refine ⟨183724795491540502285598539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244966393988720669714131385 183724795491540502285598539)
    ·
      refine ⟨275587193237310753428397809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183724795491540502285598539 275587193237310753428397809)
      ·
        refine ⟨206690394927983065071298357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275587193237310753428397809 206690394927983065071298357)
        ·
          refine ⟨19377224524498412350434221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206690394927983065071298357 19377224524498412350434221)
          ·
            refine ⟨7266459196686904631412833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19377224524498412350434221 7266459196686904631412833)
            ·
              refine ⟨5449844397515178473559625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7266459196686904631412833 5449844397515178473559625)
              ·
                refine ⟨4087383298136383855169719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5449844397515178473559625 4087383298136383855169719)
                ·
                  refine ⟨6131074947204575782754579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4087383298136383855169719 6131074947204575782754579)
                  ·
                    refine ⟨9196612420806863674131869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6131074947204575782754579 9196612420806863674131869)
                    ·
                      refine ⟨3448729657802573877799451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9196612420806863674131869 3448729657802573877799451)
                      ·
                        rfl

theorem cell23_6716377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 1, 3].length) (baseStart_6716377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716377 prefixEnd_6716377 := by exact prefixLift 6716377
  have htrace : WordTrace (prefixWord ++ tailWord_6716377) baseStart_6716377 baseEnd_6716377 := by
    simpa [prefixWord, tailWord_6716377, baseEnd_6716377] using wordTrace_append hprefix tailTrace_6716377
  have hstable : (prefixWord ++ tailWord_6716377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716377).length < 2 ^ (prefixWord ++ tailWord_6716377).sum := by decide
  have hdescent : baseEnd_6716377 < baseStart_6716377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716404 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6716404 : Nat := 118140960795 + 6716404 * 2 ^ 59
def prefixEnd_6716404 : Nat := 4983230072969 + 3 ^ 40 * 6716404 * 2
def baseEnd_6716404 : Nat := 3448743521780245272161827

theorem tailTrace_6716404 : CollatzResearch.WordTrace tailWord_6716404 prefixEnd_6716404 3448743521780245272161827 := by
  unfold tailWord_6716404
  simp only [CollatzResearch.WordTrace]
  refine ⟨122483689379811426662682133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163311585839748568883576177 122483689379811426662682133)
  ·
    refine ⟨5741422939678660624813225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122483689379811426662682133 5741422939678660624813225)
    ·
      refine ⟨4306067204758995468609919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5741422939678660624813225 4306067204758995468609919)
      ·
        refine ⟨6459100807138493202914879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306067204758995468609919 6459100807138493202914879)
        ·
          refine ⟨9688651210707739804372319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459100807138493202914879 9688651210707739804372319)
          ·
            refine ⟨14532976816061609706558479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9688651210707739804372319 14532976816061609706558479)
            ·
              refine ⟨21799465224092414559837719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14532976816061609706558479 21799465224092414559837719)
              ·
                refine ⟨32699197836138621839756579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21799465224092414559837719 32699197836138621839756579)
                ·
                  refine ⟨49048796754207932759634869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32699197836138621839756579 49048796754207932759634869)
                  ·
                    refine ⟨4598324695706993696215769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49048796754207932759634869 4598324695706993696215769)
                    ·
                      refine ⟨3448743521780245272161827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598324695706993696215769 3448743521780245272161827)
                      ·
                        rfl

theorem cell23_6716404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6716404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716404 prefixEnd_6716404 := by exact prefixLift 6716404
  have htrace : WordTrace (prefixWord ++ tailWord_6716404) baseStart_6716404 baseEnd_6716404 := by
    simpa [prefixWord, tailWord_6716404, baseEnd_6716404] using wordTrace_append hprefix tailTrace_6716404
  have hstable : (prefixWord ++ tailWord_6716404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716404).length < 2 ^ (prefixWord ++ tailWord_6716404).sum := by decide
  have hdescent : baseEnd_6716404 < baseStart_6716404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716417 : List Nat := [1, 2, 4, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_6716417 : Nat := 118140960795 + 6716417 * 2 ^ 59
def prefixEnd_6716417 : Nat := 4983230072969 + 3 ^ 40 * 6716417 * 2
def baseEnd_6716417 : Nat := 3448750197028753721299267

theorem tailTrace_6716417 : CollatzResearch.WordTrace tailWord_6716417 prefixEnd_6716417 3448750197028753721299267 := by
  unfold tailWord_6716417
  simp only [CollatzResearch.WordTrace]
  refine ⟨244967852908575756545587505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163311901939050504363725003 244967852908575756545587505)
  ·
    refine ⟨183725889681431817409190629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244967852908575756545587505 183725889681431817409190629)
    ·
      refine ⟨34448604315268465764223243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183725889681431817409190629 34448604315268465764223243)
      ·
        refine ⟨51672906472902698646334865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34448604315268465764223243 51672906472902698646334865)
        ·
          refine ⟨38754679854677023984751149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51672906472902698646334865 38754679854677023984751149)
          ·
            refine ⟨14533004945503883994281681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38754679854677023984751149 14533004945503883994281681)
            ·
              refine ⟨10899753709127912995711261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14533004945503883994281681 10899753709127912995711261)
              ·
                refine ⟨4087407640922967373391723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10899753709127912995711261 4087407640922967373391723)
                ·
                  refine ⟨6131111461384451060087585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4087407640922967373391723 6131111461384451060087585)
                  ·
                    refine ⟨4598333596038338295065689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6131111461384451060087585 4598333596038338295065689)
                    ·
                      refine ⟨3448750197028753721299267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598333596038338295065689 3448750197028753721299267)
                      ·
                        rfl

theorem cell23_6716417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_6716417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716417 prefixEnd_6716417 := by exact prefixLift 6716417
  have htrace : WordTrace (prefixWord ++ tailWord_6716417) baseStart_6716417 baseEnd_6716417 := by
    simpa [prefixWord, tailWord_6716417, baseEnd_6716417] using wordTrace_append hprefix tailTrace_6716417
  have hstable : (prefixWord ++ tailWord_6716417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716417).length < 2 ^ (prefixWord ++ tailWord_6716417).sum := by decide
  have hdescent : baseEnd_6716417 < baseStart_6716417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716459 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 5]
def baseStart_6716459 : Nat := 118140960795 + 6716459 * 2 ^ 59
def prefixEnd_6716459 : Nat := 4983230072969 + 3 ^ 40 * 6716459 * 2
def baseEnd_6716459 : Nat := 3448771763216242556974073

theorem tailTrace_6716459 : CollatzResearch.WordTrace tailWord_6716459 prefixEnd_6716459 3448771763216242556974073 := by
  unfold tailWord_6716459
  simp only [CollatzResearch.WordTrace]
  refine ⟨244969384774423597718616431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163312923182949065145744287 244969384774423597718616431)
  ·
    refine ⟨367454077161635396577924647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244969384774423597718616431 367454077161635396577924647)
    ·
      refine ⟨551181115742453094866886971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367454077161635396577924647 551181115742453094866886971)
      ·
        refine ⟨826771673613679642300330457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551181115742453094866886971 826771673613679642300330457)
        ·
          refine ⟨620078755210259731725247843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 826771673613679642300330457 620078755210259731725247843)
          ·
            refine ⟨930118132815389597587871765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620078755210259731725247843 930118132815389597587871765)
            ·
              refine ⟨43599287475721387386931489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 930118132815389597587871765 43599287475721387386931489)
              ·
                refine ⟨32699465606791040540198617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43599287475721387386931489 32699465606791040540198617)
                ·
                  refine ⟨24524599205093280405148963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32699465606791040540198617 24524599205093280405148963)
                  ·
                    refine ⟨36786898807639920607723445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24524599205093280405148963 36786898807639920607723445)
                    ·
                      refine ⟨3448771763216242556974073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36786898807639920607723445 3448771763216242556974073)
                      ·
                        rfl

theorem cell23_6716459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 5].length) (baseStart_6716459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716459 prefixEnd_6716459 := by exact prefixLift 6716459
  have htrace : WordTrace (prefixWord ++ tailWord_6716459) baseStart_6716459 baseEnd_6716459 := by
    simpa [prefixWord, tailWord_6716459, baseEnd_6716459] using wordTrace_append hprefix tailTrace_6716459
  have hstable : (prefixWord ++ tailWord_6716459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716459).length < 2 ^ (prefixWord ++ tailWord_6716459).sum := by decide
  have hdescent : baseEnd_6716459 < baseStart_6716459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716476 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_6716476 : Nat := 118140960795 + 6716476 * 2 ^ 59
def prefixEnd_6716476 : Nat := 4983230072969 + 3 ^ 40 * 6716476 * 2
def baseEnd_6716476 : Nat := 3448780492387368990461495

theorem tailTrace_6716476 : CollatzResearch.WordTrace tailWord_6716476 prefixEnd_6716476 3448780492387368990461495 := by
  unfold tailWord_6716476
  simp only [CollatzResearch.WordTrace]
  refine ⟨122485002407681004810992641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163313336543574673081323521 122485002407681004810992641)
  ·
    refine ⟨91863751805760753608244481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122485002407681004810992641 91863751805760753608244481)
    ·
      refine ⟨68897813854320565206183361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91863751805760753608244481 68897813854320565206183361)
      ·
        refine ⟨51673360390740423904637521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68897813854320565206183361 51673360390740423904637521)
        ·
          refine ⟨38755020293055317928478141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51673360390740423904637521 38755020293055317928478141)
          ·
            refine ⟨14533132609895744223179303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38755020293055317928478141 14533132609895744223179303)
            ·
              refine ⟨21799698914843616334768955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14533132609895744223179303 21799698914843616334768955)
              ·
                refine ⟨32699548372265424502153433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21799698914843616334768955 32699548372265424502153433)
                ·
                  refine ⟨24524661279199068376615075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32699548372265424502153433 24524661279199068376615075)
                  ·
                    refine ⟨36786991918798602564922613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24524661279199068376615075 36786991918798602564922613)
                    ·
                      refine ⟨3448780492387368990461495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36786991918798602564922613 3448780492387368990461495)
                      ·
                        rfl

theorem cell23_6716476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_6716476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716476 prefixEnd_6716476 := by exact prefixLift 6716476
  have htrace : WordTrace (prefixWord ++ tailWord_6716476) baseStart_6716476 baseEnd_6716476 := by
    simpa [prefixWord, tailWord_6716476, baseEnd_6716476] using wordTrace_append hprefix tailTrace_6716476
  have hstable : (prefixWord ++ tailWord_6716476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716476).length < 2 ^ (prefixWord ++ tailWord_6716476).sum := by decide
  have hdescent : baseEnd_6716476 < baseStart_6716476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716496 : List Nat := [2, 1, 1, 1, 1, 3, 1, 8, 5]
def baseStart_6716496 : Nat := 118140960795 + 6716496 * 2 ^ 59
def prefixEnd_6716496 : Nat := 4983230072969 + 3 ^ 40 * 6716496 * 2
def baseEnd_6716496 : Nat := 383198973555606545801267

theorem tailTrace_6716496 : CollatzResearch.WordTrace tailWord_6716496 prefixEnd_6716496 383198973555606545801267 := by
  unfold tailWord_6716496
  simp only [CollatzResearch.WordTrace]
  refine ⟨122485367137644776518856671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163313822850193035358475561 122485367137644776518856671)
  ·
    refine ⟨183728050706467164778285007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122485367137644776518856671 183728050706467164778285007)
    ·
      refine ⟨275592076059700747167427511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183728050706467164778285007 275592076059700747167427511)
      ·
        refine ⟨413388114089551120751141267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275592076059700747167427511 413388114089551120751141267)
        ·
          refine ⟨620082171134326681126711901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413388114089551120751141267 620082171134326681126711901)
          ·
            refine ⟨232530814175372505422516963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 620082171134326681126711901 232530814175372505422516963)
            ·
              refine ⟨348796221263058758133775445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232530814175372505422516963 348796221263058758133775445)
              ·
                refine ⟨4087455717926469821880181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 348796221263058758133775445 4087455717926469821880181)
                ·
                  refine ⟨383198973555606545801267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4087455717926469821880181 383198973555606545801267)
                  ·
                    rfl

theorem cell23_6716496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 5].length) (baseStart_6716496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716496 prefixEnd_6716496 := by exact prefixLift 6716496
  have htrace : WordTrace (prefixWord ++ tailWord_6716496) baseStart_6716496 baseEnd_6716496 := by
    simpa [prefixWord, tailWord_6716496, baseEnd_6716496] using wordTrace_append hprefix tailTrace_6716496
  have hstable : (prefixWord ++ tailWord_6716496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716496).length < 2 ^ (prefixWord ++ tailWord_6716496).sum := by decide
  have hdescent : baseEnd_6716496 < baseStart_6716496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716510 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6716510 : Nat := 118140960795 + 6716510 * 2 ^ 59
def prefixEnd_6716510 : Nat := 4983230072969 + 3 ^ 40 * 6716510 * 2
def baseEnd_6716510 : Nat := 3448797950729621857436339

theorem tailTrace_6716510 : CollatzResearch.WordTrace tailWord_6716510 prefixEnd_6716510 3448797950729621857436339 := by
  unfold tailWord_6716510
  simp only [CollatzResearch.WordTrace]
  refine ⟨30621405612154854178590373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163314163264825888952481989 30621405612154854178590373)
  ·
    refine ⟨5741513552279035158485695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30621405612154854178590373 5741513552279035158485695)
    ·
      refine ⟨8612270328418552737728543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5741513552279035158485695 8612270328418552737728543)
      ·
        refine ⟨12918405492627829106592815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8612270328418552737728543 12918405492627829106592815)
        ·
          refine ⟨19377608238941743659889223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12918405492627829106592815 19377608238941743659889223)
          ·
            refine ⟨29066412358412615489833835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19377608238941743659889223 29066412358412615489833835)
            ·
              refine ⟨43599618537618923234750753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29066412358412615489833835 43599618537618923234750753)
              ·
                refine ⟨32699713903214192426063065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43599618537618923234750753 32699713903214192426063065)
                ·
                  refine ⟨24524785427410644319547299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32699713903214192426063065 24524785427410644319547299)
                  ·
                    refine ⟨36787178141115966479320949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24524785427410644319547299 36787178141115966479320949)
                    ·
                      refine ⟨3448797950729621857436339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36787178141115966479320949 3448797950729621857436339)
                      ·
                        rfl

theorem cell23_6716510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6716510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716510 prefixEnd_6716510 := by exact prefixLift 6716510
  have htrace : WordTrace (prefixWord ++ tailWord_6716510) baseStart_6716510 baseEnd_6716510 := by
    simpa [prefixWord, tailWord_6716510, baseEnd_6716510] using wordTrace_append hprefix tailTrace_6716510
  have hstable : (prefixWord ++ tailWord_6716510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716510).length < 2 ^ (prefixWord ++ tailWord_6716510).sum := by decide
  have hdescent : baseEnd_6716510 < baseStart_6716510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716556 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_6716556 : Nat := 118140960795 + 6716556 * 2 ^ 59
def prefixEnd_6716556 : Nat := 4983230072969 + 3 ^ 40 * 6716556 * 2
def baseEnd_6716556 : Nat := 1149607190279909559153709

theorem tailTrace_6716556 : CollatzResearch.WordTrace tailWord_6716556 prefixEnd_6716556 1149607190279909559153709 := by
  unfold tailWord_6716556
  simp only [CollatzResearch.WordTrace]
  refine ⟨122486461327536091642448761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163315281770048122189931681 122486461327536091642448761)
  ·
    refine ⟨91864845995652068731836571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122486461327536091642448761 91864845995652068731836571)
    ·
      refine ⟨137797268993478103097754857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91864845995652068731836571 137797268993478103097754857)
      ·
        refine ⟨103347951745108577323316143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137797268993478103097754857 103347951745108577323316143)
        ·
          refine ⟨155021927617662865984974215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103347951745108577323316143 155021927617662865984974215)
          ·
            refine ⟨232532891426494298977461323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155021927617662865984974215 232532891426494298977461323)
            ·
              refine ⟨348799337139741448466191985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232532891426494298977461323 348799337139741448466191985)
              ·
                refine ⟨261599502854806086349643989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348799337139741448466191985 261599502854806086349643989)
                ·
                  refine ⟨6131238348159517648819781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 261599502854806086349643989 6131238348159517648819781)
                  ·
                    refine ⟨1149607190279909559153709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6131238348159517648819781 1149607190279909559153709)
                    ·
                      rfl

theorem cell23_6716556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_6716556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716556 prefixEnd_6716556 := by exact prefixLift 6716556
  have htrace : WordTrace (prefixWord ++ tailWord_6716556) baseStart_6716556 baseEnd_6716556 := by
    simpa [prefixWord, tailWord_6716556, baseEnd_6716556] using wordTrace_append hprefix tailTrace_6716556
  have hstable : (prefixWord ++ tailWord_6716556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716556).length < 2 ^ (prefixWord ++ tailWord_6716556).sum := by decide
  have hdescent : baseEnd_6716556 < baseStart_6716556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716569 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 12]
def baseStart_6716569 : Nat := 118140960795 + 6716569 * 2 ^ 59
def prefixEnd_6716569 : Nat := 4983230072969 + 3 ^ 40 * 6716569 * 2
def baseEnd_6716569 : Nat := 383203138454248569622063

theorem tailTrace_6716569 : CollatzResearch.WordTrace tailWord_6716569 prefixEnd_6716569 383203138454248569622063 := by
  unfold tailWord_6716569
  simp only [CollatzResearch.WordTrace]
  refine ⟨244973396804025086505120761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163315597869350057670080507 244973396804025086505120761)
  ·
    refine ⟨183730047603018814878840571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244973396804025086505120761 183730047603018814878840571)
    ·
      refine ⟨275595071404528222318260857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183730047603018814878840571 275595071404528222318260857)
      ·
        refine ⟨206696303553396166738695643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275595071404528222318260857 206696303553396166738695643)
        ·
          refine ⟨310044455330094250108043465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206696303553396166738695643 310044455330094250108043465)
          ·
            refine ⟨232533341497570687581032599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310044455330094250108043465 232533341497570687581032599)
            ·
              refine ⟨348800012246356031371548899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232533341497570687581032599 348800012246356031371548899)
              ·
                refine ⟨523200018369534047057323349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348800012246356031371548899 523200018369534047057323349)
                ·
                  refine ⟨383203138454248569622063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 523200018369534047057323349 383203138454248569622063)
                  ·
                    rfl

theorem cell23_6716569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 12].length) (baseStart_6716569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716569 prefixEnd_6716569 := by exact prefixLift 6716569
  have htrace : WordTrace (prefixWord ++ tailWord_6716569) baseStart_6716569 baseEnd_6716569 := by
    simpa [prefixWord, tailWord_6716569, baseEnd_6716569] using wordTrace_append hprefix tailTrace_6716569
  have hstable : (prefixWord ++ tailWord_6716569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716569).length < 2 ^ (prefixWord ++ tailWord_6716569).sum := by decide
  have hdescent : baseEnd_6716569 < baseStart_6716569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716573 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_6716573 : Nat := 118140960795 + 6716573 * 2 ^ 59
def prefixEnd_6716573 : Nat := 4983230072969 + 3 ^ 40 * 6716573 * 2
def baseEnd_6716573 : Nat := 1149610100003618370316183

theorem tailTrace_6716573 : CollatzResearch.WordTrace tailWord_6716573 prefixEnd_6716573 1149610100003618370316183 := by
  unfold tailWord_6716573
  simp only [CollatzResearch.WordTrace]
  refine ⟨244973542696010595188266373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163315695130673730125510915 244973542696010595188266373)
  ·
    refine ⟨45932539255501986597799945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 244973542696010595188266373 45932539255501986597799945)
    ·
      refine ⟨34449404441626489948349959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45932539255501986597799945 34449404441626489948349959)
      ·
        refine ⟨51674106662439734922524939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34449404441626489948349959 51674106662439734922524939)
        ·
          refine ⟨77511159993659602383787409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51674106662439734922524939 77511159993659602383787409)
          ·
            refine ⟨58133369995244701787840557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77511159993659602383787409 58133369995244701787840557)
            ·
              refine ⟨21800013748216763170440209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58133369995244701787840557 21800013748216763170440209)
              ·
                refine ⟨16350010311162572377830157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21800013748216763170440209 16350010311162572377830157)
                ·
                  refine ⟨6131253866685964641686309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16350010311162572377830157 6131253866685964641686309)
                  ·
                    refine ⟨1149610100003618370316183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6131253866685964641686309 1149610100003618370316183)
                    ·
                      rfl

theorem cell23_6716573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_6716573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716573 prefixEnd_6716573 := by exact prefixLift 6716573
  have htrace : WordTrace (prefixWord ++ tailWord_6716573) baseStart_6716573 baseEnd_6716573 := by
    simpa [prefixWord, tailWord_6716573, baseEnd_6716573] using wordTrace_append hprefix tailTrace_6716573
  have hstable : (prefixWord ++ tailWord_6716573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716573).length < 2 ^ (prefixWord ++ tailWord_6716573).sum := by decide
  have hdescent : baseEnd_6716573 < baseStart_6716573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716580 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_6716580 : Nat := 118140960795 + 6716580 * 2 ^ 59
def prefixEnd_6716580 : Nat := 4983230072969 + 3 ^ 40 * 6716580 * 2
def baseEnd_6716580 : Nat := 3448833894375436583561017

theorem tailTrace_6716580 : CollatzResearch.WordTrace tailWord_6716580 prefixEnd_6716580 3448833894375436583561017 := by
  unfold tailWord_6716580
  simp only [CollatzResearch.WordTrace]
  refine ⟨122486899003492617691885597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163315865337990156922514129 122486899003492617691885597)
  ·
    refine ⟨45932587126309731634457099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122486899003492617691885597 45932587126309731634457099)
    ·
      refine ⟨68898880689464597451685649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45932587126309731634457099 68898880689464597451685649)
      ·
        refine ⟨51674160517098448088764237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68898880689464597451685649 51674160517098448088764237)
        ·
          refine ⟨19377810193911918033286589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51674160517098448088764237 19377810193911918033286589)
          ·
            refine ⟨7266678822716969262482471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19377810193911918033286589 7266678822716969262482471)
            ·
              refine ⟨10900018234075453893723707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7266678822716969262482471 10900018234075453893723707)
              ·
                refine ⟨16350027351113180840585561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10900018234075453893723707 16350027351113180840585561)
                ·
                  refine ⟨12262520513334885630439171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16350027351113180840585561 12262520513334885630439171)
                  ·
                    refine ⟨18393780770002328445658757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12262520513334885630439171 18393780770002328445658757)
                    ·
                      refine ⟨3448833894375436583561017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18393780770002328445658757 3448833894375436583561017)
                      ·
                        rfl

theorem cell23_6716580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_6716580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716580 prefixEnd_6716580 := by exact prefixLift 6716580
  have htrace : WordTrace (prefixWord ++ tailWord_6716580) baseStart_6716580 baseEnd_6716580 := by
    simpa [prefixWord, tailWord_6716580, baseEnd_6716580] using wordTrace_append hprefix tailTrace_6716580
  have hstable : (prefixWord ++ tailWord_6716580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716580).length < 2 ^ (prefixWord ++ tailWord_6716580).sum := by decide
  have hdescent : baseEnd_6716580 < baseStart_6716580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716616 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 5, 5]
def baseStart_6716616 : Nat := 118140960795 + 6716616 * 2 ^ 59
def prefixEnd_6716616 : Nat := 4983230072969 + 3 ^ 40 * 6716616 * 2
def baseEnd_6716616 : Nat := 1149617459892999480903617

theorem tailTrace_6716616 : CollatzResearch.WordTrace tailWord_6716616 prefixEnd_6716616 1149617459892999480903617 := by
  unfold tailWord_6716616
  simp only [CollatzResearch.WordTrace]
  refine ⟨122487555517427406766040851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163316740689903209021387801 122487555517427406766040851)
  ·
    refine ⟨183731333276141110149061277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122487555517427406766040851 183731333276141110149061277)
    ·
      refine ⟨68899249978552916305897979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183731333276141110149061277 68899249978552916305897979)
      ·
        refine ⟨103348874967829374458846969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68899249978552916305897979 103348874967829374458846969)
        ·
          refine ⟨77511656225872030844135227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103348874967829374458846969 77511656225872030844135227)
          ·
            refine ⟨116267484338808046266202841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77511656225872030844135227 116267484338808046266202841)
            ·
              refine ⟨87200613254106034699652131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116267484338808046266202841 87200613254106034699652131)
              ·
                refine ⟨130800919881159052049478197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87200613254106034699652131 130800919881159052049478197)
                ·
                  refine ⟨12262586238858661129638581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130800919881159052049478197 12262586238858661129638581)
                  ·
                    refine ⟨1149617459892999480903617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12262586238858661129638581 1149617459892999480903617)
                    ·
                      rfl

theorem cell23_6716616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_6716616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716616 prefixEnd_6716616 := by exact prefixLift 6716616
  have htrace : WordTrace (prefixWord ++ tailWord_6716616) baseStart_6716616 baseEnd_6716616 := by
    simpa [prefixWord, tailWord_6716616, baseEnd_6716616] using wordTrace_append hprefix tailTrace_6716616
  have hstable : (prefixWord ++ tailWord_6716616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716616).length < 2 ^ (prefixWord ++ tailWord_6716616).sum := by decide
  have hdescent : baseEnd_6716616 < baseStart_6716616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716623 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 6, 3, 2]
def baseStart_6716623 : Nat := 118140960795 + 6716623 * 2 ^ 59
def prefixEnd_6716623 : Nat := 4983230072969 + 3 ^ 40 * 6716623 * 2
def baseEnd_6716623 : Nat := 3448855974043579915323319

theorem tailTrace_6716623 : CollatzResearch.WordTrace tailWord_6716623 prefixEnd_6716623 3448855974043579915323319 := by
  unfold tailWord_6716623
  simp only [CollatzResearch.WordTrace]
  refine ⟨244975366345829453727586523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163316910897219635818391015 244975366345829453727586523)
  ·
    refine ⟨367463049518744180591379785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244975366345829453727586523 367463049518744180591379785)
    ·
      refine ⟨275597287139058135443534839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367463049518744180591379785 275597287139058135443534839)
      ·
        refine ⟨413395930708587203165302259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275597287139058135443534839 413395930708587203165302259)
        ·
          refine ⟨620093896062880804747953389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413395930708587203165302259 620093896062880804747953389)
          ·
            refine ⟨232535211023580301780482521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 620093896062880804747953389 232535211023580301780482521)
            ·
              refine ⟨174401408267685226335361891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232535211023580301780482521 174401408267685226335361891)
              ·
                refine ⟨261602112401527839503042837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174401408267685226335361891 261602112401527839503042837)
                ·
                  refine ⟨12262599018821617476705133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261602112401527839503042837 12262599018821617476705133)
                  ·
                    refine ⟨4598474632058106553764425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12262599018821617476705133 4598474632058106553764425)
                    ·
                      refine ⟨3448855974043579915323319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598474632058106553764425 3448855974043579915323319)
                      ·
                        rfl

theorem cell23_6716623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 3, 2].length) (baseStart_6716623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716623 prefixEnd_6716623 := by exact prefixLift 6716623
  have htrace : WordTrace (prefixWord ++ tailWord_6716623) baseStart_6716623 baseEnd_6716623 := by
    simpa [prefixWord, tailWord_6716623, baseEnd_6716623] using wordTrace_append hprefix tailTrace_6716623
  have hstable : (prefixWord ++ tailWord_6716623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716623).length < 2 ^ (prefixWord ++ tailWord_6716623).sum := by decide
  have hdescent : baseEnd_6716623 < baseStart_6716623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716666 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_6716666 : Nat := 118140960795 + 6716666 * 2 ^ 59
def prefixEnd_6716666 : Nat := 4983230072969 + 3 ^ 40 * 6716666 * 2
def baseEnd_6716666 : Nat := 3448878053711723247085621

theorem tailTrace_6716666 : CollatzResearch.WordTrace tailWord_6716666 prefixEnd_6716666 3448878053711723247085621 := by
  unfold tailWord_6716666
  simp only [CollatzResearch.WordTrace]
  refine ⟨61244233671168418017850463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163317956456449114714267901 61244233671168418017850463)
  ·
    refine ⟨91866350506752627026775695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61244233671168418017850463 91866350506752627026775695)
    ·
      refine ⟨137799525760128940540163543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91866350506752627026775695 137799525760128940540163543)
      ·
        refine ⟨206699288640193410810245315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137799525760128940540163543 206699288640193410810245315)
        ·
          refine ⟨310048932960290116215367973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206699288640193410810245315 310048932960290116215367973)
          ·
            refine ⟨58134174930054396790381495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 310048932960290116215367973 58134174930054396790381495)
            ·
              refine ⟨87201262395081595185572243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58134174930054396790381495 87201262395081595185572243)
              ·
                refine ⟨130801893592622392778358365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87201262395081595185572243 130801893592622392778358365)
                ·
                  refine ⟨49050710097233397291884387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130801893592622392778358365 49050710097233397291884387)
                  ·
                    refine ⟨73576065145850095937826581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49050710097233397291884387 73576065145850095937826581)
                    ·
                      refine ⟨3448878053711723247085621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73576065145850095937826581 3448878053711723247085621)
                      ·
                        rfl

theorem cell23_6716666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_6716666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716666 prefixEnd_6716666 := by exact prefixLift 6716666
  have htrace : WordTrace (prefixWord ++ tailWord_6716666) baseStart_6716666 baseEnd_6716666 := by
    simpa [prefixWord, tailWord_6716666, baseEnd_6716666] using wordTrace_append hprefix tailTrace_6716666
  have hstable : (prefixWord ++ tailWord_6716666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716666).length < 2 ^ (prefixWord ++ tailWord_6716666).sum := by decide
  have hdescent : baseEnd_6716666 < baseStart_6716666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716673 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_6716673 : Nat := 118140960795 + 6716673 * 2 ^ 59
def prefixEnd_6716673 : Nat := 4983230072969 + 3 ^ 40 * 6716673 * 2
def baseEnd_6716673 : Nat := 3448881648076304719698089

theorem tailTrace_6716673 : CollatzResearch.WordTrace tailWord_6716673 prefixEnd_6716673 3448881648076304719698089 := by
  unfold tailWord_6716673
  simp only [CollatzResearch.WordTrace]
  refine ⟨244977189995648312266906673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163318126663765541511271115 244977189995648312266906673)
  ·
    refine ⟨183732892496736234200180005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244977189995648312266906673 183732892496736234200180005)
    ·
      refine ⟨34449917343138043912533751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183732892496736234200180005 34449917343138043912533751)
      ·
        refine ⟨51674876014707065868800627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34449917343138043912533751 51674876014707065868800627)
        ·
          refine ⟨77512314022060598803200941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51674876014707065868800627 77512314022060598803200941)
          ·
            refine ⟨29067117758272724551200353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77512314022060598803200941 29067117758272724551200353)
            ·
              refine ⟨21800338318704543413400265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29067117758272724551200353 21800338318704543413400265)
              ·
                refine ⟨16350253739028407560050199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21800338318704543413400265 16350253739028407560050199)
                ·
                  refine ⟨24525380608542611340075299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16350253739028407560050199 24525380608542611340075299)
                  ·
                    refine ⟨36788070912813917010112949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24525380608542611340075299 36788070912813917010112949)
                    ·
                      refine ⟨3448881648076304719698089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36788070912813917010112949 3448881648076304719698089)
                      ·
                        rfl

theorem cell23_6716673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_6716673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716673 prefixEnd_6716673 := by exact prefixLift 6716673
  have htrace : WordTrace (prefixWord ++ tailWord_6716673) baseStart_6716673 baseEnd_6716673 := by
    simpa [prefixWord, tailWord_6716673, baseEnd_6716673] using wordTrace_append hprefix tailTrace_6716673
  have hstable : (prefixWord ++ tailWord_6716673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716673).length < 2 ^ (prefixWord ++ tailWord_6716673).sum := by decide
  have hdescent : baseEnd_6716673 < baseStart_6716673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716707 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 1, 2, 3]
def baseStart_6716707 : Nat := 118140960795 + 6716707 * 2 ^ 59
def prefixEnd_6716707 : Nat := 4983230072969 + 3 ^ 40 * 6716707 * 2
def baseEnd_6716707 : Nat := 3448899106418557586672933

theorem tailTrace_6716707 : CollatzResearch.WordTrace tailWord_6716707 prefixEnd_6716707 3448899106418557586672933 := by
  unfold tailWord_6716707
  simp only [CollatzResearch.WordTrace]
  refine ⟨244978430077525136073644375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163318953385016757382429583 244978430077525136073644375)
  ·
    refine ⟨367467645116287704110466563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244978430077525136073644375 367467645116287704110466563)
    ·
      refine ⟨551201467674431556165699845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 367467645116287704110466563 551201467674431556165699845)
      ·
        refine ⟨103350275188955916781068721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 551201467674431556165699845 103350275188955916781068721)
        ·
          refine ⟨77512706391716937585801541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103350275188955916781068721 77512706391716937585801541)
          ·
            refine ⟨14533632448446925797337789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77512706391716937585801541 14533632448446925797337789)
            ·
              refine ⟨5450112168167597174001671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14533632448446925797337789 5450112168167597174001671)
              ·
                refine ⟨8175168252251395761002507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5450112168167597174001671 8175168252251395761002507)
                ·
                  refine ⟨12262752378377093641503761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175168252251395761002507 12262752378377093641503761)
                  ·
                    refine ⟨9197064283782820231127821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12262752378377093641503761 9197064283782820231127821)
                    ·
                      refine ⟨3448899106418557586672933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9197064283782820231127821 3448899106418557586672933)
                      ·
                        rfl

theorem cell23_6716707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_6716707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716707 prefixEnd_6716707 := by exact prefixLift 6716707
  have htrace : WordTrace (prefixWord ++ tailWord_6716707) baseStart_6716707 baseEnd_6716707 := by
    simpa [prefixWord, tailWord_6716707, baseEnd_6716707] using wordTrace_append hprefix tailTrace_6716707
  have hstable : (prefixWord ++ tailWord_6716707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716707).length < 2 ^ (prefixWord ++ tailWord_6716707).sum := by decide
  have hdescent : baseEnd_6716707 < baseStart_6716707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716713 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 4, 7, 2]
def baseStart_6716713 : Nat := 118140960795 + 6716713 * 2 ^ 59
def prefixEnd_6716713 : Nat := 4983230072969 + 3 ^ 40 * 6716713 * 2
def baseEnd_6716713 : Nat := 3448902187302484563197905

theorem tailTrace_6716713 : CollatzResearch.WordTrace tailWord_6716713 prefixEnd_6716713 3448902187302484563197905 := by
  unfold tailWord_6716713
  simp only [CollatzResearch.WordTrace]
  refine ⟨244978648915503399098362793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163319099277002266065575195 244978648915503399098362793)
  ·
    refine ⟨183733986686627549323772095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244978648915503399098362793 183733986686627549323772095)
    ·
      refine ⟨275600980029941323985658143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183733986686627549323772095 275600980029941323985658143)
      ·
        refine ⟨413401470044911985978487215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275600980029941323985658143 413401470044911985978487215)
        ·
          refine ⟨620102205067367978967730823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413401470044911985978487215 620102205067367978967730823)
          ·
            refine ⟨930153307601051968451596235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620102205067367978967730823 930153307601051968451596235)
            ·
              refine ⟨1395229961401577952677394353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930153307601051968451596235 1395229961401577952677394353)
              ·
                refine ⟨1046422471051183464508045765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395229961401577952677394353 1046422471051183464508045765)
                ·
                  refine ⟨196204213322096899595258581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046422471051183464508045765 196204213322096899595258581)
                  ·
                    refine ⟨4598536249736646084263873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 196204213322096899595258581 4598536249736646084263873)
                    ·
                      refine ⟨3448902187302484563197905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598536249736646084263873 3448902187302484563197905)
                      ·
                        rfl

theorem cell23_6716713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 7, 2].length) (baseStart_6716713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716713 prefixEnd_6716713 := by exact prefixLift 6716713
  have htrace : WordTrace (prefixWord ++ tailWord_6716713) baseStart_6716713 baseEnd_6716713 := by
    simpa [prefixWord, tailWord_6716713, baseEnd_6716713] using wordTrace_append hprefix tailTrace_6716713
  have hstable : (prefixWord ++ tailWord_6716713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716713).length < 2 ^ (prefixWord ++ tailWord_6716713).sum := by decide
  have hdescent : baseEnd_6716713 < baseStart_6716713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716721 : List Nat := [1, 2, 2, 3, 3, 1, 4, 2, 1, 2, 2]
def baseStart_6716721 : Nat := 118140960795 + 6716721 * 2 ^ 59
def prefixEnd_6716721 : Nat := 4983230072969 + 3 ^ 40 * 6716721 * 2
def baseEnd_6716721 : Nat := 3448906295147720531897869

theorem tailTrace_6716721 : CollatzResearch.WordTrace tailWord_6716721 prefixEnd_6716721 3448906295147720531897869 := by
  unfold tailWord_6716721
  simp only [CollatzResearch.WordTrace]
  refine ⟨244978940699474416464654017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163319293799649610976436011 244978940699474416464654017)
  ·
    refine ⟨183734205524605812348490513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244978940699474416464654017 183734205524605812348490513)
    ·
      refine ⟨137800654143454359261367885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183734205524605812348490513 137800654143454359261367885)
      ·
        refine ⟨51675245303795384723012957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137800654143454359261367885 51675245303795384723012957)
        ·
          refine ⟨19378216988923269271129859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51675245303795384723012957 19378216988923269271129859)
          ·
            refine ⟨29067325483384903906694789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19378216988923269271129859 29067325483384903906694789)
            ·
              refine ⟨5450123528134669482505273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29067325483384903906694789 5450123528134669482505273)
              ·
                refine ⟨4087592646101002111878955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450123528134669482505273 4087592646101002111878955)
                ·
                  refine ⟨6131388969151503167818433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4087592646101002111878955 6131388969151503167818433)
                  ·
                    refine ⟨4598541726863627375863825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6131388969151503167818433 4598541726863627375863825)
                    ·
                      refine ⟨3448906295147720531897869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598541726863627375863825 3448906295147720531897869)
                      ·
                        rfl

theorem cell23_6716721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_6716721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716721 prefixEnd_6716721 := by exact prefixLift 6716721
  have htrace : WordTrace (prefixWord ++ tailWord_6716721) baseStart_6716721 baseEnd_6716721 := by
    simpa [prefixWord, tailWord_6716721, baseEnd_6716721] using wordTrace_append hprefix tailTrace_6716721
  have hstable : (prefixWord ++ tailWord_6716721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716721).length < 2 ^ (prefixWord ++ tailWord_6716721).sum := by decide
  have hdescent : baseEnd_6716721 < baseStart_6716721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716730 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2]
def baseStart_6716730 : Nat := 118140960795 + 6716730 * 2 ^ 59
def prefixEnd_6716730 : Nat := 4983230072969 + 3 ^ 40 * 6716730 * 2
def baseEnd_6716730 : Nat := 3448910916473610996685327

theorem tailTrace_6716730 : CollatzResearch.WordTrace tailWord_6716730 prefixEnd_6716730 3448910916473610996685327 := by
  unfold tailWord_6716730
  simp only [CollatzResearch.WordTrace]
  refine ⟨61244817239110452750432911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163319512637627874001154429 61244817239110452750432911)
  ·
    refine ⟨91867225858665679125649367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61244817239110452750432911 91867225858665679125649367)
    ·
      refine ⟨137800838787998518688474051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91867225858665679125649367 137800838787998518688474051)
      ·
        refine ⟨206701258181997778032711077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137800838787998518688474051 206701258181997778032711077)
        ·
          refine ⟨38756485909124583381133327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206701258181997778032711077 38756485909124583381133327)
          ·
            refine ⟨58134728863686875071699991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38756485909124583381133327 58134728863686875071699991)
            ·
              refine ⟨87202093295530312607549987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58134728863686875071699991 87202093295530312607549987)
              ·
                refine ⟨130803139943295468911324981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87202093295530312607549987 130803139943295468911324981)
                ·
                  refine ⟨12262794369683950210436717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130803139943295468911324981 12262794369683950210436717)
                  ·
                    refine ⟨4598547888631481328913769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12262794369683950210436717 4598547888631481328913769)
                    ·
                      refine ⟨3448910916473610996685327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598547888631481328913769 3448910916473610996685327)
                      ·
                        rfl

theorem cell23_6716730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_6716730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716730 prefixEnd_6716730 := by exact prefixLift 6716730
  have htrace : WordTrace (prefixWord ++ tailWord_6716730) baseStart_6716730 baseEnd_6716730 := by
    simpa [prefixWord, tailWord_6716730, baseEnd_6716730] using wordTrace_append hprefix tailTrace_6716730
  have hstable : (prefixWord ++ tailWord_6716730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716730).length < 2 ^ (prefixWord ++ tailWord_6716730).sum := by decide
  have hdescent : baseEnd_6716730 < baseStart_6716730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716737 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6716737 : Nat := 118140960795 + 6716737 * 2 ^ 59
def prefixEnd_6716737 : Nat := 4983230072969 + 3 ^ 40 * 6716737 * 2
def baseEnd_6716737 : Nat := 3448914510838192469297795

theorem tailTrace_6716737 : CollatzResearch.WordTrace tailWord_6716737 prefixEnd_6716737 3448914510838192469297795 := by
  unfold tailWord_6716737
  simp only [CollatzResearch.WordTrace]
  refine ⟨244979524267416451197236465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163319682844944300798157643 244979524267416451197236465)
  ·
    refine ⟨183734643200562338397927349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244979524267416451197236465 183734643200562338397927349)
    ·
      refine ⟨17225122800052719224805689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183734643200562338397927349 17225122800052719224805689)
      ·
        refine ⟨12918842100039539418604267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17225122800052719224805689 12918842100039539418604267)
        ·
          refine ⟨19378263150059309127906401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12918842100039539418604267 19378263150059309127906401)
          ·
            refine ⟨14533697362544481845929801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19378263150059309127906401 14533697362544481845929801)
            ·
              refine ⟨10900273021908361384447351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14533697362544481845929801 10900273021908361384447351)
              ·
                refine ⟨16350409532862542076671027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10900273021908361384447351 16350409532862542076671027)
                ·
                  refine ⟨24525614299293813115006541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16350409532862542076671027 24525614299293813115006541)
                  ·
                    refine ⟨9197105362235179918127453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24525614299293813115006541 9197105362235179918127453)
                    ·
                      refine ⟨3448914510838192469297795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9197105362235179918127453 3448914510838192469297795)
                      ·
                        rfl

theorem cell23_6716737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6716737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716737 prefixEnd_6716737 := by exact prefixLift 6716737
  have htrace : WordTrace (prefixWord ++ tailWord_6716737) baseStart_6716737 baseEnd_6716737 := by
    simpa [prefixWord, tailWord_6716737, baseEnd_6716737] using wordTrace_append hprefix tailTrace_6716737
  have hstable : (prefixWord ++ tailWord_6716737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716737).length < 2 ^ (prefixWord ++ tailWord_6716737).sum := by decide
  have hdescent : baseEnd_6716737 < baseStart_6716737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716758 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6716758 : Nat := 118140960795 + 6716758 * 2 ^ 59
def prefixEnd_6716758 : Nat := 4983230072969 + 3 ^ 40 * 6716758 * 2
def baseEnd_6716758 : Nat := 3448925293931936887135199

theorem tailTrace_6716758 : CollatzResearch.WordTrace tailWord_6716758 prefixEnd_6716758 3448925293931936887135199 := by
  unfold tailWord_6716758
  simp only [CollatzResearch.WordTrace]
  refine ⟨15311268137521273236484433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 163320193466893581189167285 15311268137521273236484433)
  ·
    refine ⟨11483451103140954927363325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15311268137521273236484433 11483451103140954927363325)
    ·
      refine ⟨4306294163677858097761247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11483451103140954927363325 4306294163677858097761247)
      ·
        refine ⟨6459441245516787146641871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306294163677858097761247 6459441245516787146641871)
        ·
          refine ⟨9689161868275180719962807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459441245516787146641871 9689161868275180719962807)
          ·
            refine ⟨14533742802412771079944211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9689161868275180719962807 14533742802412771079944211)
            ·
              refine ⟨21800614203619156619916317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14533742802412771079944211 21800614203619156619916317)
              ·
                refine ⟨8175230326357183732468619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21800614203619156619916317 8175230326357183732468619)
                ·
                  refine ⟨12262845489535775598702929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175230326357183732468619 12262845489535775598702929)
                  ·
                    refine ⟨9197134117151831699027197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12262845489535775598702929 9197134117151831699027197)
                    ·
                      refine ⟨3448925293931936887135199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9197134117151831699027197 3448925293931936887135199)
                      ·
                        rfl

theorem cell23_6716758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6716758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716758 prefixEnd_6716758 := by exact prefixLift 6716758
  have htrace : WordTrace (prefixWord ++ tailWord_6716758) baseStart_6716758 baseEnd_6716758 := by
    simpa [prefixWord, tailWord_6716758, baseEnd_6716758] using wordTrace_append hprefix tailTrace_6716758
  have hstable : (prefixWord ++ tailWord_6716758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716758).length < 2 ^ (prefixWord ++ tailWord_6716758).sum := by decide
  have hdescent : baseEnd_6716758 < baseStart_6716758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716760 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 1, 4, 2]
def baseStart_6716760 : Nat := 118140960795 + 6716760 * 2 ^ 59
def prefixEnd_6716760 : Nat := 4983230072969 + 3 ^ 40 * 6716760 * 2
def baseEnd_6716760 : Nat := 3448926320893245879310189

theorem tailTrace_6716760 : CollatzResearch.WordTrace tailWord_6716760 prefixEnd_6716760 3448926320893245879310189 := by
  unfold tailWord_6716760
  simp only [CollatzResearch.WordTrace]
  refine ⟨122490181573166563062661867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163320242097555417416882489 122490181573166563062661867)
  ·
    refine ⟨183735272359749844593992801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122490181573166563062661867 183735272359749844593992801)
    ·
      refine ⟨137801454269812383445494601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183735272359749844593992801 137801454269812383445494601)
      ·
        refine ⟨103351090702359287584120951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137801454269812383445494601 103351090702359287584120951)
        ·
          refine ⟨155026636053538931376181427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103351090702359287584120951 155026636053538931376181427)
          ·
            refine ⟨232539954080308397064272141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155026636053538931376181427 232539954080308397064272141)
            ·
              refine ⟨87202482780115648899102053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232539954080308397064272141 87202482780115648899102053)
              ·
                refine ⟨16350465521271684168581635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87202482780115648899102053 16350465521271684168581635)
                ·
                  refine ⟨24525698281907526252872453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16350465521271684168581635 24525698281907526252872453)
                  ·
                    refine ⟨4598568427857661172413585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24525698281907526252872453 4598568427857661172413585)
                    ·
                      refine ⟨3448926320893245879310189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598568427857661172413585 3448926320893245879310189)
                      ·
                        rfl

theorem cell23_6716760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_6716760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716760 prefixEnd_6716760 := by exact prefixLift 6716760
  have htrace : WordTrace (prefixWord ++ tailWord_6716760) baseStart_6716760 baseEnd_6716760 := by
    simpa [prefixWord, tailWord_6716760, baseEnd_6716760] using wordTrace_append hprefix tailTrace_6716760
  have hstable : (prefixWord ++ tailWord_6716760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716760).length < 2 ^ (prefixWord ++ tailWord_6716760).sum := by decide
  have hdescent : baseEnd_6716760 < baseStart_6716760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716773 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_6716773 : Nat := 118140960795 + 6716773 * 2 ^ 59
def prefixEnd_6716773 : Nat := 4983230072969 + 3 ^ 40 * 6716773 * 2
def baseEnd_6716773 : Nat := 3448932996141754328447629

theorem tailTrace_6716773 : CollatzResearch.WordTrace tailWord_6716773 prefixEnd_6716773 3448932996141754328447629 := by
  unfold tailWord_6716773
  simp only [CollatzResearch.WordTrace]
  refine ⟨244980837295286029345546973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163320558196857352897031315 244980837295286029345546973)
  ·
    refine ⟨91867813985732261004580115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 244980837295286029345546973 91867813985732261004580115)
    ·
      refine ⟨137801720978598391506870173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91867813985732261004580115 137801720978598391506870173)
      ·
        refine ⟨51675645366974396815076315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137801720978598391506870173 51675645366974396815076315)
        ·
          refine ⟨77513468050461595222614473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51675645366974396815076315 77513468050461595222614473)
          ·
            refine ⟨58135101037846196416960855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77513468050461595222614473 58135101037846196416960855)
            ·
              refine ⟨87202651556769294625441283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58135101037846196416960855 87202651556769294625441283)
              ·
                refine ⟨130803977335153941938161925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87202651556769294625441283 130803977335153941938161925)
                ·
                  refine ⟨24525745750341364113405361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130803977335153941938161925 24525745750341364113405361)
                  ·
                    refine ⟨18394309312756023085054021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24525745750341364113405361 18394309312756023085054021)
                    ·
                      refine ⟨3448932996141754328447629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18394309312756023085054021 3448932996141754328447629)
                      ·
                        rfl

theorem cell23_6716773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_6716773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716773 prefixEnd_6716773 := by exact prefixLift 6716773
  have htrace : WordTrace (prefixWord ++ tailWord_6716773) baseStart_6716773 baseEnd_6716773 := by
    simpa [prefixWord, tailWord_6716773, baseEnd_6716773] using wordTrace_append hprefix tailTrace_6716773
  have hstable : (prefixWord ++ tailWord_6716773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716773).length < 2 ^ (prefixWord ++ tailWord_6716773).sum := by decide
  have hdescent : baseEnd_6716773 < baseStart_6716773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716777 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 2, 2, 2]
def baseStart_6716777 : Nat := 118140960795 + 6716777 * 2 ^ 59
def prefixEnd_6716777 : Nat := 4983230072969 + 3 ^ 40 * 6716777 * 2
def baseEnd_6716777 : Nat := 3448935050064372312797611

theorem tailTrace_6716777 : CollatzResearch.WordTrace tailWord_6716777 prefixEnd_6716777 3448935050064372312797611 := by
  unfold tailWord_6716777
  simp only [CollatzResearch.WordTrace]
  refine ⟨244980983187271538028692585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163320655458181025352461723 244980983187271538028692585)
  ·
    refine ⟨183735737390453653521519439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 244980983187271538028692585 183735737390453653521519439)
    ·
      refine ⟨275603606085680480282279159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183735737390453653521519439 275603606085680480282279159)
      ·
        refine ⟨413405409128520720423418739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275603606085680480282279159 413405409128520720423418739)
        ·
          refine ⟨620108113692781080635128109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413405409128520720423418739 620108113692781080635128109)
          ·
            refine ⟨232540542634792905238173041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 620108113692781080635128109 232540542634792905238173041)
            ·
              refine ⟨174405406976094678928629781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232540542634792905238173041 174405406976094678928629781)
              ·
                refine ⟨8175253452004438074779521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174405406976094678928629781 8175253452004438074779521)
                ·
                  refine ⟨6131440089003328556084641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8175253452004438074779521 6131440089003328556084641)
                  ·
                    refine ⟨4598580066752496417063481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6131440089003328556084641 4598580066752496417063481)
                    ·
                      refine ⟨3448935050064372312797611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598580066752496417063481 3448935050064372312797611)
                      ·
                        rfl

theorem cell23_6716777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 2, 2].length) (baseStart_6716777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716777 prefixEnd_6716777 := by exact prefixLift 6716777
  have htrace : WordTrace (prefixWord ++ tailWord_6716777) baseStart_6716777 baseEnd_6716777 := by
    simpa [prefixWord, tailWord_6716777, baseEnd_6716777] using wordTrace_append hprefix tailTrace_6716777
  have hstable : (prefixWord ++ tailWord_6716777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716777).length < 2 ^ (prefixWord ++ tailWord_6716777).sum := by decide
  have hdescent : baseEnd_6716777 < baseStart_6716777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716783 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 7]
def baseStart_6716783 : Nat := 118140960795 + 6716783 * 2 ^ 59
def prefixEnd_6716783 : Nat := 4983230072969 + 3 ^ 40 * 6716783 * 2
def baseEnd_6716783 : Nat := 383215347883144365480287

theorem tailTrace_6716783 : CollatzResearch.WordTrace tailWord_6716783 prefixEnd_6716783 383215347883144365480287 := by
  unfold tailWord_6716783
  simp only [CollatzResearch.WordTrace]
  refine ⟨244981202025249801053411003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163320801350166534035607335 244981202025249801053411003)
  ·
    refine ⟨367471803037874701580116505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244981202025249801053411003 367471803037874701580116505)
    ·
      refine ⟨275603852278406026185087379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367471803037874701580116505 275603852278406026185087379)
      ·
        refine ⟨413405778417609039277631069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275603852278406026185087379 413405778417609039277631069)
        ·
          refine ⟨155027166906603389729111651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413405778417609039277631069 155027166906603389729111651)
          ·
            refine ⟨232540750359905084593667477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155027166906603389729111651 232540750359905084593667477)
            ·
              refine ⟨10900347673120550840328163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232540750359905084593667477 10900347673120550840328163)
              ·
                refine ⟨16350521509680826260492245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10900347673120550840328163 16350521509680826260492245)
                ·
                  refine ⟨383215347883144365480287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16350521509680826260492245 383215347883144365480287)
                  ·
                    rfl

theorem cell23_6716783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 7].length) (baseStart_6716783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716783 prefixEnd_6716783 := by exact prefixLift 6716783
  have htrace : WordTrace (prefixWord ++ tailWord_6716783) baseStart_6716783 baseEnd_6716783 := by
    simpa [prefixWord, tailWord_6716783, baseEnd_6716783] using wordTrace_append hprefix tailTrace_6716783
  have hstable : (prefixWord ++ tailWord_6716783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716783).length < 2 ^ (prefixWord ++ tailWord_6716783).sum := by decide
  have hdescent : baseEnd_6716783 < baseStart_6716783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716798 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6716798 : Nat := 118140960795 + 6716798 * 2 ^ 59
def prefixEnd_6716798 : Nat := 4983230072969 + 3 ^ 40 * 6716798 * 2
def baseEnd_6716798 : Nat := 3448945833158116730635015

theorem tailTrace_6716798 : CollatzResearch.WordTrace tailWord_6716798 prefixEnd_6716798 3448945833158116730635015 := by
  unfold tailWord_6716798
  simp only [CollatzResearch.WordTrace]
  refine ⟨30622718640024432326900881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163321166080130305743471365 30622718640024432326900881)
  ·
    refine ⟨22967038980018324245175661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30622718640024432326900881 22967038980018324245175661)
    ·
      refine ⟨8612639617506871591940873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22967038980018324245175661 8612639617506871591940873)
      ·
        refine ⟨6459479713130153693955655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8612639617506871591940873 6459479713130153693955655)
        ·
          refine ⟨9689219569695230540933483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459479713130153693955655 9689219569695230540933483)
          ·
            refine ⟨14533829354542845811400225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9689219569695230540933483 14533829354542845811400225)
            ·
              refine ⟨10900372015907134358550169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14533829354542845811400225 10900372015907134358550169)
              ·
                refine ⟨8175279011930350768912627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10900372015907134358550169 8175279011930350768912627)
                ·
                  refine ⟨12262918517895526153368941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175279011930350768912627 12262918517895526153368941)
                  ·
                    refine ⟨4598594444210822307513353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12262918517895526153368941 4598594444210822307513353)
                    ·
                      refine ⟨3448945833158116730635015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598594444210822307513353 3448945833158116730635015)
                      ·
                        rfl

theorem cell23_6716798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6716798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716798 prefixEnd_6716798 := by exact prefixLift 6716798
  have htrace : WordTrace (prefixWord ++ tailWord_6716798) baseStart_6716798 baseEnd_6716798 := by
    simpa [prefixWord, tailWord_6716798, baseEnd_6716798] using wordTrace_append hprefix tailTrace_6716798
  have hstable : (prefixWord ++ tailWord_6716798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716798).length < 2 ^ (prefixWord ++ tailWord_6716798).sum := by decide
  have hdescent : baseEnd_6716798 < baseStart_6716798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716823 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 5]
def baseStart_6716823 : Nat := 118140960795 + 6716823 * 2 ^ 59
def prefixEnd_6716823 : Nat := 4983230072969 + 3 ^ 40 * 6716823 * 2
def baseEnd_6716823 : Nat := 3448958670174479132822399

theorem tailTrace_6716823 : CollatzResearch.WordTrace tailWord_6716823 prefixEnd_6716823 3448958670174479132822399 := by
  unfold tailWord_6716823
  simp only [CollatzResearch.WordTrace]
  refine ⟨244982660945104887884867123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163321773963403258589911415 244982660945104887884867123)
  ·
    refine ⟨367473991417657331827300685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244982660945104887884867123 367473991417657331827300685)
    ·
      refine ⟨137802746781621499435237757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 367473991417657331827300685 137802746781621499435237757)
      ·
        refine ⟨51676030043108062288214159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137802746781621499435237757 51676030043108062288214159)
        ·
          refine ⟨77514045064662093432321239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51676030043108062288214159 77514045064662093432321239)
          ·
            refine ⟨116271067596993140148481859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77514045064662093432321239 116271067596993140148481859)
            ·
              refine ⟨174406601395489710222722789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116271067596993140148481859 174406601395489710222722789)
              ·
                refine ⟨32701237761654320666760523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174406601395489710222722789 32701237761654320666760523)
                ·
                  refine ⟨49051856642481481000140785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32701237761654320666760523 49051856642481481000140785)
                  ·
                    refine ⟨36788892481861110750105589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49051856642481481000140785 36788892481861110750105589)
                    ·
                      refine ⟨3448958670174479132822399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36788892481861110750105589 3448958670174479132822399)
                      ·
                        rfl

theorem cell23_6716823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_6716823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716823 prefixEnd_6716823 := by exact prefixLift 6716823
  have htrace : WordTrace (prefixWord ++ tailWord_6716823) baseStart_6716823 baseEnd_6716823 := by
    simpa [prefixWord, tailWord_6716823, baseEnd_6716823] using wordTrace_append hprefix tailTrace_6716823
  have hstable : (prefixWord ++ tailWord_6716823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716823).length < 2 ^ (prefixWord ++ tailWord_6716823).sum := by decide
  have hdescent : baseEnd_6716823 < baseStart_6716823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716834 : List Nat := [3, 3, 1, 2, 1, 3, 3, 2, 5]
def baseStart_6716834 : Nat := 118140960795 + 6716834 * 2 ^ 59
def prefixEnd_6716834 : Nat := 4983230072969 + 3 ^ 40 * 6716834 * 2
def baseEnd_6716834 : Nat := 383218257606853176642761

theorem tailTrace_6716834 : CollatzResearch.WordTrace tailWord_6716834 prefixEnd_6716834 383218257606853176642761 := by
  unfold tailWord_6716834
  simp only [CollatzResearch.WordTrace]
  refine ⟨61245765537016259190879389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163322041432043357842345037 61245765537016259190879389)
  ·
    refine ⟨22967162076381097196579771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61245765537016259190879389 22967162076381097196579771)
    ·
      refine ⟨34450743114571645794869657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22967162076381097196579771 34450743114571645794869657)
      ·
        refine ⟨25838057335928734346152243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34450743114571645794869657 25838057335928734346152243)
        ·
          refine ⟨38757086003893101519228365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25838057335928734346152243 38757086003893101519228365)
          ·
            refine ⟨14533907251459913069710637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38757086003893101519228365 14533907251459913069710637)
            ·
              refine ⟨5450215219297467401141489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14533907251459913069710637 5450215219297467401141489)
              ·
                refine ⟨4087661414473100550856117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450215219297467401141489 4087661414473100550856117)
                ·
                  refine ⟨383218257606853176642761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4087661414473100550856117 383218257606853176642761)
                  ·
                    rfl

theorem cell23_6716834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_6716834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716834 prefixEnd_6716834 := by exact prefixLift 6716834
  have htrace : WordTrace (prefixWord ++ tailWord_6716834) baseStart_6716834 baseEnd_6716834 := by
    simpa [prefixWord, tailWord_6716834, baseEnd_6716834] using wordTrace_append hprefix tailTrace_6716834
  have hstable : (prefixWord ++ tailWord_6716834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716834).length < 2 ^ (prefixWord ++ tailWord_6716834).sum := by decide
  have hdescent : baseEnd_6716834 < baseStart_6716834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716863 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 4]
def baseStart_6716863 : Nat := 118140960795 + 6716863 * 2 ^ 59
def prefixEnd_6716863 : Nat := 4983230072969 + 3 ^ 40 * 6716863 * 2
def baseEnd_6716863 : Nat := 3448979209400658976322215

theorem tailTrace_6716863 : CollatzResearch.WordTrace tailWord_6716863 prefixEnd_6716863 3448979209400658976322215 := by
  unfold tailWord_6716863
  simp only [CollatzResearch.WordTrace]
  refine ⟨244984119864959974716323243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163322746576639983144215495 244984119864959974716323243)
  ·
    refine ⟨367476179797439962074484865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244984119864959974716323243 367476179797439962074484865)
    ·
      refine ⟨275607134848079971555863649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367476179797439962074484865 275607134848079971555863649)
      ·
        refine ⟨206705351136059978666897737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275607134848079971555863649 206705351136059978666897737)
        ·
          refine ⟨155029013352044984000173303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206705351136059978666897737 155029013352044984000173303)
          ·
            refine ⟨232543520028067476000259955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155029013352044984000173303 232543520028067476000259955)
            ·
              refine ⟨348815280042101214000389933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232543520028067476000259955 348815280042101214000389933)
              ·
                refine ⟨130805730015787955250146225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348815280042101214000389933 130805730015787955250146225)
                ·
                  refine ⟨98104297511840966437609669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130805730015787955250146225 98104297511840966437609669)
                  ·
                    refine ⟨18394555783470181207051813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98104297511840966437609669 18394555783470181207051813)
                    ·
                      refine ⟨3448979209400658976322215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18394555783470181207051813 3448979209400658976322215)
                      ·
                        rfl

theorem cell23_6716863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_6716863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716863 prefixEnd_6716863 := by exact prefixLift 6716863
  have htrace : WordTrace (prefixWord ++ tailWord_6716863) baseStart_6716863 baseEnd_6716863 := by
    simpa [prefixWord, tailWord_6716863, baseEnd_6716863] using wordTrace_append hprefix tailTrace_6716863
  have hstable : (prefixWord ++ tailWord_6716863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716863).length < 2 ^ (prefixWord ++ tailWord_6716863).sum := by decide
  have hdescent : baseEnd_6716863 < baseStart_6716863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716890 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 6]
def baseStart_6716890 : Nat := 118140960795 + 6716890 * 2 ^ 59
def prefixEnd_6716890 : Nat := 4983230072969 + 3 ^ 40 * 6716890 * 2
def baseEnd_6716890 : Nat := 383221452597592263409399

theorem tailTrace_6716890 : CollatzResearch.WordTrace tailWord_6716890 prefixEnd_6716890 383221452597592263409399 := by
  unfold tailWord_6716890
  simp only [CollatzResearch.WordTrace]
  refine ⟨61246276158965539581889031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163323403090574772218370749 61246276158965539581889031)
  ·
    refine ⟨91869414238448309372833547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61246276158965539581889031 91869414238448309372833547)
    ·
      refine ⟨137804121357672464059250321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91869414238448309372833547 137804121357672464059250321)
      ·
        refine ⟨103353091018254348044437741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137804121357672464059250321 103353091018254348044437741)
        ·
          refine ⟨38757409131845380516664153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103353091018254348044437741 38757409131845380516664153)
          ·
            refine ⟨29068056848884035387498115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38757409131845380516664153 29068056848884035387498115)
            ·
              refine ⟨43602085273326053081247173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29068056848884035387498115 43602085273326053081247173)
              ·
                refine ⟨8175390988748634952733845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43602085273326053081247173 8175390988748634952733845)
                ·
                  refine ⟨383221452597592263409399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8175390988748634952733845 383221452597592263409399)
                  ·
                    rfl

theorem cell23_6716890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_6716890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716890 prefixEnd_6716890 := by exact prefixLift 6716890
  have htrace : WordTrace (prefixWord ++ tailWord_6716890) baseStart_6716890 baseEnd_6716890 := by
    simpa [prefixWord, tailWord_6716890, baseEnd_6716890] using wordTrace_append hprefix tailTrace_6716890
  have hstable : (prefixWord ++ tailWord_6716890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716890).length < 2 ^ (prefixWord ++ tailWord_6716890).sum := by decide
  have hdescent : baseEnd_6716890 < baseStart_6716890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716920 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 3, 5]
def baseStart_6716920 : Nat := 118140960795 + 6716920 * 2 ^ 59
def prefixEnd_6716920 : Nat := 4983230072969 + 3 ^ 40 * 6716920 * 2
def baseEnd_6716920 : Nat := 1149669492599321751103151

theorem tailTrace_6716920 : CollatzResearch.WordTrace tailWord_6716920 prefixEnd_6716920 1149669492599321751103151 := by
  unfold tailWord_6716920
  simp only [CollatzResearch.WordTrace]
  refine ⟨122493099412876736725574107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163324132550502315634098809 122493099412876736725574107)
  ·
    refine ⟨183739649119315105088361161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122493099412876736725574107 183739649119315105088361161)
    ·
      refine ⟨137804736839486328816270871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183739649119315105088361161 137804736839486328816270871)
      ·
        refine ⟨206707105259229493224406307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137804736839486328816270871 206707105259229493224406307)
        ·
          refine ⟨310060657888844239836609461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206707105259229493224406307 310060657888844239836609461)
          ·
            refine ⟨29068186677079147484682137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310060657888844239836609461 29068186677079147484682137)
            ·
              refine ⟨21801140007809360613511603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29068186677079147484682137 21801140007809360613511603)
              ·
                refine ⟨32701710011714040920267405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21801140007809360613511603 32701710011714040920267405)
                ·
                  refine ⟨12263141254392765345100277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32701710011714040920267405 12263141254392765345100277)
                  ·
                    refine ⟨1149669492599321751103151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12263141254392765345100277 1149669492599321751103151)
                    ·
                      rfl

theorem cell23_6716920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_6716920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716920 prefixEnd_6716920 := by exact prefixLift 6716920
  have htrace : WordTrace (prefixWord ++ tailWord_6716920) baseStart_6716920 baseEnd_6716920 := by
    simpa [prefixWord, tailWord_6716920, baseEnd_6716920] using wordTrace_append hprefix tailTrace_6716920
  have hstable : (prefixWord ++ tailWord_6716920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716920).length < 2 ^ (prefixWord ++ tailWord_6716920).sum := by decide
  have hdescent : baseEnd_6716920 < baseStart_6716920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716927 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 2, 3, 2]
def baseStart_6716927 : Nat := 118140960795 + 6716927 * 2 ^ 59
def prefixEnd_6716927 : Nat := 4983230072969 + 3 ^ 40 * 6716927 * 2
def baseEnd_6716927 : Nat := 3449012072162546725921921

theorem tailTrace_6716927 : CollatzResearch.WordTrace tailWord_6716927 prefixEnd_6716927 3449012072162546725921921 := by
  unfold tailWord_6716927
  simp only [CollatzResearch.WordTrace]
  refine ⟨244986454136728113646653035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163324302757818742431102023 244986454136728113646653035)
  ·
    refine ⟨367479681205092170469979553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244986454136728113646653035 367479681205092170469979553)
    ·
      refine ⟨275609760903819127852484665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 367479681205092170469979553 275609760903819127852484665)
      ·
        refine ⟨206707320677864345889363499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275609760903819127852484665 206707320677864345889363499)
        ·
          refine ⟨310060981016796518834045249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206707320677864345889363499 310060981016796518834045249)
          ·
            refine ⟨232545735762597389125533937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310060981016796518834045249 232545735762597389125533937)
            ·
              refine ⟨174409301821948041844150453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232545735762597389125533937 174409301821948041844150453)
              ·
                refine ⟨16350872045807628922889105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174409301821948041844150453 16350872045807628922889105)
                ·
                  refine ⟨12263154034355721692166829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16350872045807628922889105 12263154034355721692166829)
                  ·
                    refine ⟨4598682762883395634562561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12263154034355721692166829 4598682762883395634562561)
                    ·
                      refine ⟨3449012072162546725921921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4598682762883395634562561 3449012072162546725921921)
                      ·
                        rfl

theorem cell23_6716927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_6716927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716927 prefixEnd_6716927 := by exact prefixLift 6716927
  have htrace : WordTrace (prefixWord ++ tailWord_6716927) baseStart_6716927 baseEnd_6716927 := by
    simpa [prefixWord, tailWord_6716927, baseEnd_6716927] using wordTrace_append hprefix tailTrace_6716927
  have hstable : (prefixWord ++ tailWord_6716927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716927).length < 2 ^ (prefixWord ++ tailWord_6716927).sum := by decide
  have hdescent : baseEnd_6716927 < baseStart_6716927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716974 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_6716974 : Nat := 118140960795 + 6716974 * 2 ^ 59
def prefixEnd_6716974 : Nat := 4983230072969 + 3 ^ 40 * 6716974 * 2
def baseEnd_6716974 : Nat := 3449036205753308042034205

theorem tailTrace_6716974 : CollatzResearch.WordTrace tailWord_6716974 prefixEnd_6716974 3449036205753308042034205 := by
  unfold tailWord_6716974
  simp only [CollatzResearch.WordTrace]
  refine ⟨30623521045944730084201747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163325445578371893782409317 30623521045944730084201747)
  ·
    refine ⟨45935281568917095126302621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30623521045944730084201747 45935281568917095126302621)
    ·
      refine ⟨17225730588343910672363483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45935281568917095126302621 17225730588343910672363483)
      ·
        refine ⟨25838595882515866008545225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17225730588343910672363483 25838595882515866008545225)
        ·
          refine ⟨19378946911886899506408919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25838595882515866008545225 19378946911886899506408919)
          ·
            refine ⟨29068420367830349259613379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19378946911886899506408919 29068420367830349259613379)
            ·
              refine ⟨43602630551745523889420069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29068420367830349259613379 43602630551745523889420069)
              ·
                refine ⟨8175493228452285729266263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43602630551745523889420069 8175493228452285729266263)
                ·
                  refine ⟨12263239842678428593899395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175493228452285729266263 12263239842678428593899395)
                  ·
                    refine ⟨18394859764017642890849093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12263239842678428593899395 18394859764017642890849093)
                    ·
                      refine ⟨3449036205753308042034205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18394859764017642890849093 3449036205753308042034205)
                      ·
                        rfl

theorem cell23_6716974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_6716974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6716974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6716974 prefixEnd_6716974 := by exact prefixLift 6716974
  have htrace : WordTrace (prefixWord ++ tailWord_6716974) baseStart_6716974 baseEnd_6716974 := by
    simpa [prefixWord, tailWord_6716974, baseEnd_6716974] using wordTrace_append hprefix tailTrace_6716974
  have hstable : (prefixWord ++ tailWord_6716974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716974).length < 2 ^ (prefixWord ++ tailWord_6716974).sum := by decide
  have hdescent : baseEnd_6716974 < baseStart_6716974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
