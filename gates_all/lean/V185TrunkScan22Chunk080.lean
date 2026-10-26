import V185TrunkScan22Chunk079

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_719335 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 4, 3]
def baseStart_719335 : Nat := 118140960795 + 719335 * 2 ^ 59
def prefixEnd_719335 : Nat := 4983230072969 + 3 ^ 40 * 719335 * 2
def baseEnd_719335 : Nat := 246243071068032221469563

theorem tailTrace_719335 : CollatzResearch.WordTrace tailWord_719335 prefixEnd_719335 246243071068032221469563 := by
  unfold tailWord_719335
  simp only [CollatzResearch.WordTrace]
  refine ⟨26236302848979622482311459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17490868565986414988207639 26236302848979622482311459)
  ·
    refine ⟨39354454273469433723467189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26236302848979622482311459 39354454273469433723467189)
    ·
      refine ⟨3689480088137759411575049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39354454273469433723467189 3689480088137759411575049)
      ·
        refine ⟨2767110066103319558681287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3689480088137759411575049 2767110066103319558681287)
        ·
          refine ⟨4150665099154979338021931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767110066103319558681287 4150665099154979338021931)
          ·
            refine ⟨6225997648732469007032897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150665099154979338021931 6225997648732469007032897)
            ·
              refine ⟨4669498236549351755274673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6225997648732469007032897 4669498236549351755274673)
              ·
                refine ⟨3502123677412013816456005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4669498236549351755274673 3502123677412013816456005)
                ·
                  refine ⟨656648189514752590585501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3502123677412013816456005 656648189514752590585501)
                  ·
                    refine ⟨246243071068032221469563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656648189514752590585501 246243071068032221469563)
                    ·
                      rfl

theorem cell22_719335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_719335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719335 prefixEnd_719335 := by exact prefixLift 719335
  have htrace : WordTrace (prefixWord ++ tailWord_719335) baseStart_719335 baseEnd_719335 := by
    simpa [prefixWord, tailWord_719335, baseEnd_719335] using wordTrace_append hprefix tailTrace_719335
  have hstable : (prefixWord ++ tailWord_719335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719335).length < 2 ^ (prefixWord ++ tailWord_719335).sum := by decide
  have hdescent : baseEnd_719335 < baseStart_719335 := by decide
  rcases family_descends (prefixWord ++ tailWord_719335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719350 : List Nat := [5, 1, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_719350 : Nat := 118140960795 + 719350 * 2 ^ 59
def prefixEnd_719350 : Nat := 4983230072969 + 3 ^ 40 * 719350 * 2
def baseEnd_719350 : Nat := 246248205874577182344517

theorem tailTrace_719350 : CollatzResearch.WordTrace tailWord_719350 prefixEnd_719350 246248205874577182344517 := by
  unfold tailWord_719350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639803121495330002756719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17491233295950186696071669 1639803121495330002756719)
  ·
    refine ⟨2459704682242995004135079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1639803121495330002756719 2459704682242995004135079)
    ·
      refine ⟨3689557023364492506202619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2459704682242995004135079 3689557023364492506202619)
      ·
        refine ⟨5534335535046738759303929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3689557023364492506202619 5534335535046738759303929)
        ·
          refine ⟨4150751651285054069477947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5534335535046738759303929 4150751651285054069477947)
          ·
            refine ⟨6226127476927581104216921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150751651285054069477947 6226127476927581104216921)
            ·
              refine ⟨4669595607695685828162691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6226127476927581104216921 4669595607695685828162691)
              ·
                refine ⟨7004393411543528742244037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669595607695685828162691 7004393411543528742244037)
                ·
                  refine ⟨1313323764664411639170757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7004393411543528742244037 1313323764664411639170757)
                  ·
                    refine ⟨246248205874577182344517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1313323764664411639170757 246248205874577182344517)
                    ·
                      rfl

theorem cell22_719350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_719350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719350 prefixEnd_719350 := by exact prefixLift 719350
  have htrace : WordTrace (prefixWord ++ tailWord_719350) baseStart_719350 baseEnd_719350 := by
    simpa [prefixWord, tailWord_719350, baseEnd_719350] using wordTrace_append hprefix tailTrace_719350
  have hstable : (prefixWord ++ tailWord_719350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719350).length < 2 ^ (prefixWord ++ tailWord_719350).sum := by decide
  have hdescent : baseEnd_719350 < baseStart_719350 := by decide
  rcases family_descends (prefixWord ++ tailWord_719350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719393 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 9]
def baseStart_719393 : Nat := 118140960795 + 719393 * 2 ^ 59
def prefixEnd_719393 : Nat := 4983230072969 + 3 ^ 40 * 719393 * 2
def baseEnd_719393 : Nat := 82087641884446467839795

theorem tailTrace_719393 : CollatzResearch.WordTrace tailWord_719393 prefixEnd_719393 82087641884446467839795 := by
  unfold tailWord_719393
  simp only [CollatzResearch.WordTrace]
  refine ⟨26238418282769498387922833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17492278855179665591948555 26238418282769498387922833)
  ·
    refine ⟨19678813712077123790942125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26238418282769498387922833 19678813712077123790942125)
    ·
      refine ⟨7379555142028921421603297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19678813712077123790942125 7379555142028921421603297)
      ·
        refine ⟨5534666356521691066202473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7379555142028921421603297 5534666356521691066202473)
        ·
          refine ⟨4150999767391268299651855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5534666356521691066202473 4150999767391268299651855)
          ·
            refine ⟨6226499651086902449477783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4150999767391268299651855 6226499651086902449477783)
            ·
              refine ⟨9339749476630353674216675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6226499651086902449477783 9339749476630353674216675)
              ·
                refine ⟨14009624214945530511325013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9339749476630353674216675 14009624214945530511325013)
                ·
                  refine ⟨82087641884446467839795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14009624214945530511325013 82087641884446467839795)
                  ·
                    rfl

theorem cell22_719393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_719393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719393 prefixEnd_719393 := by exact prefixLift 719393
  have htrace : WordTrace (prefixWord ++ tailWord_719393) baseStart_719393 baseEnd_719393 := by
    simpa [prefixWord, tailWord_719393, baseEnd_719393] using wordTrace_append hprefix tailTrace_719393
  have hstable : (prefixWord ++ tailWord_719393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719393).length < 2 ^ (prefixWord ++ tailWord_719393).sum := by decide
  have hdescent : baseEnd_719393 < baseStart_719393 := by decide
  rcases family_descends (prefixWord ++ tailWord_719393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719399 : List Nat := [1, 1, 7, 2, 2, 1, 8]
def baseStart_719399 : Nat := 118140960795 + 719399 * 2 ^ 59
def prefixEnd_719399 : Nat := 4983230072969 + 3 ^ 40 * 719399 * 2
def baseEnd_719399 : Nat := 9120925169479903254421

theorem tailTrace_719399 : CollatzResearch.WordTrace tailWord_719399 prefixEnd_719399 9120925169479903254421 := by
  unfold tailWord_719399
  simp only [CollatzResearch.WordTrace]
  refine ⟨26238637120747761412641251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17492424747165174275094167 26238637120747761412641251)
  ·
    refine ⟨39357955681121642118961877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26238637120747761412641251 39357955681121642118961877)
    ·
      refine ⟨922452086276288487163169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 39357955681121642118961877 922452086276288487163169)
      ·
        refine ⟨691839064707216365372377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 922452086276288487163169 691839064707216365372377)
        ·
          refine ⟨518879298530412274029283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691839064707216365372377 518879298530412274029283)
          ·
            refine ⟨778318947795618411043925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518879298530412274029283 778318947795618411043925)
            ·
              refine ⟨9120925169479903254421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 778318947795618411043925 9120925169479903254421)
              ·
                rfl

theorem cell22_719399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 8].length) (baseStart_719399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719399 prefixEnd_719399 := by exact prefixLift 719399
  have htrace : WordTrace (prefixWord ++ tailWord_719399) baseStart_719399 baseEnd_719399 := by
    simpa [prefixWord, tailWord_719399, baseEnd_719399] using wordTrace_append hprefix tailTrace_719399
  have hstable : (prefixWord ++ tailWord_719399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719399).length < 2 ^ (prefixWord ++ tailWord_719399).sum := by decide
  have hdescent : baseEnd_719399 < baseStart_719399 := by decide
  rcases family_descends (prefixWord ++ tailWord_719399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719408 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_719408 : Nat := 118140960795 + 719408 * 2 ^ 59
def prefixEnd_719408 : Nat := 4983230072969 + 3 ^ 40 * 719408 * 2
def baseEnd_719408 : Nat := 246268060459884364394339

theorem tailTrace_719408 : CollatzResearch.WordTrace tailWord_719408 prefixEnd_719408 246268060459884364394339 := by
  unfold tailWord_719408
  simp only [CollatzResearch.WordTrace]
  refine ⟨13119482688857577974859439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17492643585143437299812585 13119482688857577974859439)
  ·
    refine ⟨19679224033286366962289159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13119482688857577974859439 19679224033286366962289159)
    ·
      refine ⟨29518836049929550443433739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19679224033286366962289159 29518836049929550443433739)
      ·
        refine ⟨44278254074894325665150609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29518836049929550443433739 44278254074894325665150609)
        ·
          refine ⟨33208690556170744248862957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44278254074894325665150609 33208690556170744248862957)
          ·
            refine ⟨12453258958564029093323609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33208690556170744248862957 12453258958564029093323609)
            ·
              refine ⟨9339944218923021819992707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12453258958564029093323609 9339944218923021819992707)
              ·
                refine ⟨14009916328384532729989061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9339944218923021819992707 14009916328384532729989061)
                ·
                  refine ⟨2626859311572099886872949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14009916328384532729989061 2626859311572099886872949)
                  ·
                    refine ⟨246268060459884364394339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2626859311572099886872949 246268060459884364394339)
                    ·
                      rfl

theorem cell22_719408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_719408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719408 prefixEnd_719408 := by exact prefixLift 719408
  have htrace : WordTrace (prefixWord ++ tailWord_719408) baseStart_719408 baseEnd_719408 := by
    simpa [prefixWord, tailWord_719408, baseEnd_719408] using wordTrace_append hprefix tailTrace_719408
  have hstable : (prefixWord ++ tailWord_719408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719408).length < 2 ^ (prefixWord ++ tailWord_719408).sum := by decide
  have hdescent : baseEnd_719408 < baseStart_719408 := by decide
  rcases family_descends (prefixWord ++ tailWord_719408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719414 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_719414 : Nat := 118140960795 + 719414 * 2 ^ 59
def prefixEnd_719414 : Nat := 4983230072969 + 3 ^ 40 * 719414 * 2
def baseEnd_719414 : Nat := 246270114382502348744321

theorem tailTrace_719414 : CollatzResearch.WordTrace tailWord_719414 prefixEnd_719414 246270114382502348744321 := by
  unfold tailWord_719414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639949013480838685902331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17492789477128945982958197 1639949013480838685902331)
  ·
    refine ⟨2459923520221258028853497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1639949013480838685902331 2459923520221258028853497)
    ·
      refine ⟨1844942640165943521640123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2459923520221258028853497 1844942640165943521640123)
      ·
        refine ⟨2767413960248915282460185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844942640165943521640123 2767413960248915282460185)
        ·
          refine ⟨2075560470186686461845139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2767413960248915282460185 2075560470186686461845139)
          ·
            refine ⟨3113340705280029692767709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075560470186686461845139 3113340705280029692767709)
            ·
              refine ⟨1167502764480011134787891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3113340705280029692767709 1167502764480011134787891)
              ·
                refine ⟨1751254146720016702181837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167502764480011134787891 1751254146720016702181837)
                ·
                  refine ⟨656720305020006263318189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1751254146720016702181837 656720305020006263318189)
                  ·
                    refine ⟨246270114382502348744321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656720305020006263318189 246270114382502348744321)
                    ·
                      rfl

theorem cell22_719414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_719414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719414 prefixEnd_719414 := by exact prefixLift 719414
  have htrace : WordTrace (prefixWord ++ tailWord_719414) baseStart_719414 baseEnd_719414 := by
    simpa [prefixWord, tailWord_719414, baseEnd_719414] using wordTrace_append hprefix tailTrace_719414
  have hstable : (prefixWord ++ tailWord_719414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719414).length < 2 ^ (prefixWord ++ tailWord_719414).sum := by decide
  have hdescent : baseEnd_719414 < baseStart_719414 := by decide
  rcases family_descends (prefixWord ++ tailWord_719414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719440 : List Nat := [2, 1, 1, 1, 1, 3, 2, 6, 1, 4]
def baseStart_719440 : Nat := 118140960795 + 719440 * 2 ^ 59
def prefixEnd_719440 : Nat := 4983230072969 + 3 ^ 40 * 719440 * 2
def baseEnd_719440 : Nat := 246279014713846947594241

theorem tailTrace_719440 : CollatzResearch.WordTrace tailWord_719440 prefixEnd_719440 246279014713846947594241 := by
  unfold tailWord_719440
  simp only [CollatzResearch.WordTrace]
  refine ⟨13120066256799612707441887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17493421675732816943255849 13120066256799612707441887)
  ·
    refine ⟨19680099385199419061162831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13120066256799612707441887 19680099385199419061162831)
    ·
      refine ⟨29520149077799128591744247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19680099385199419061162831 29520149077799128591744247)
      ·
        refine ⟨44280223616698692887616371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29520149077799128591744247 44280223616698692887616371)
        ·
          refine ⟨66420335425048039331424557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44280223616698692887616371 66420335425048039331424557)
          ·
            refine ⟨24907625784393014749284209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66420335425048039331424557 24907625784393014749284209)
            ·
              refine ⟨18680719338294761061963157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24907625784393014749284209 18680719338294761061963157)
              ·
                refine ⟨875658718982566924779523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18680719338294761061963157 875658718982566924779523)
                ·
                  refine ⟨1313488078473850387169285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875658718982566924779523 1313488078473850387169285)
                  ·
                    refine ⟨246279014713846947594241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1313488078473850387169285 246279014713846947594241)
                    ·
                      rfl

theorem cell22_719440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_719440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719440 prefixEnd_719440 := by exact prefixLift 719440
  have htrace : WordTrace (prefixWord ++ tailWord_719440) baseStart_719440 baseEnd_719440 := by
    simpa [prefixWord, tailWord_719440, baseEnd_719440] using wordTrace_append hprefix tailTrace_719440
  have hstable : (prefixWord ++ tailWord_719440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719440).length < 2 ^ (prefixWord ++ tailWord_719440).sum := by decide
  have hdescent : baseEnd_719440 < baseStart_719440 := by decide
  rcases family_descends (prefixWord ++ tailWord_719440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719483 : List Nat := [1, 1, 1, 1, 1, 4, 2, 11]
def baseStart_719483 : Nat := 118140960795 + 719483 * 2 ^ 59
def prefixEnd_719483 : Nat := 4983230072969 + 3 ^ 40 * 719483 * 2
def baseEnd_719483 : Nat := 27365970499178796529901

theorem tailTrace_719483 : CollatzResearch.WordTrace tailWord_719483 prefixEnd_719483 27365970499178796529901 := by
  unfold tailWord_719483
  simp only [CollatzResearch.WordTrace]
  refine ⟨26241700852443443758699103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17494467234962295839132735 26241700852443443758699103)
  ·
    refine ⟨39362551278665165638048655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26241700852443443758699103 39362551278665165638048655)
    ·
      refine ⟨59043826917997748457072983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39362551278665165638048655 59043826917997748457072983)
      ·
        refine ⟨88565740376996622685609475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59043826917997748457072983 88565740376996622685609475)
        ·
          refine ⟨132848610565494934028414213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88565740376996622685609475 132848610565494934028414213)
          ·
            refine ⟨24909114481030300130327665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132848610565494934028414213 24909114481030300130327665)
            ·
              refine ⟨18681835860772725097745749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24909114481030300130327665 18681835860772725097745749)
              ·
                refine ⟨27365970499178796529901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 18681835860772725097745749 27365970499178796529901)
                ·
                  rfl

theorem cell22_719483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 11].length) (baseStart_719483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719483 prefixEnd_719483 := by exact prefixLift 719483
  have htrace : WordTrace (prefixWord ++ tailWord_719483) baseStart_719483 baseEnd_719483 := by
    simpa [prefixWord, tailWord_719483, baseEnd_719483] using wordTrace_append hprefix tailTrace_719483
  have hstable : (prefixWord ++ tailWord_719483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719483).length < 2 ^ (prefixWord ++ tailWord_719483).sum := by decide
  have hdescent : baseEnd_719483 < baseStart_719483 := by decide
  rcases family_descends (prefixWord ++ tailWord_719483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719521 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 2, 3]
def baseStart_719521 : Nat := 118140960795 + 719521 * 2 ^ 59
def prefixEnd_719521 : Nat := 4983230072969 + 3 ^ 40 * 719521 * 2
def baseEnd_719521 : Nat := 246306742669189736318993

theorem tailTrace_719521 : CollatzResearch.WordTrace tailWord_719521 prefixEnd_719521 246306742669189736318993 := by
  unfold tailWord_719521
  simp only [CollatzResearch.WordTrace]
  refine ⟨26243086826305776248582417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17495391217537184165721611 26243086826305776248582417)
  ·
    refine ⟨19682315119729332186436813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26243086826305776248582417 19682315119729332186436813)
    ·
      refine ⟨7380868169898499569913805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19682315119729332186436813 7380868169898499569913805)
      ·
        refine ⟨2767825563711937338717677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7380868169898499569913805 2767825563711937338717677)
        ·
          refine ⟨1037934586391976502019129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2767825563711937338717677 1037934586391976502019129)
          ·
            refine ⟨778450939793982376514347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037934586391976502019129 778450939793982376514347)
            ·
              refine ⟨1167676409690973564771521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778450939793982376514347 1167676409690973564771521)
              ·
                refine ⟨875757307268230173578641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167676409690973564771521 875757307268230173578641)
                ·
                  refine ⟨656817980451172630183981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 875757307268230173578641 656817980451172630183981)
                  ·
                    refine ⟨246306742669189736318993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656817980451172630183981 246306742669189736318993)
                    ·
                      rfl

theorem cell22_719521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_719521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719521 prefixEnd_719521 := by exact prefixLift 719521
  have htrace : WordTrace (prefixWord ++ tailWord_719521) baseStart_719521 baseEnd_719521 := by
    simpa [prefixWord, tailWord_719521, baseEnd_719521] using wordTrace_append hprefix tailTrace_719521
  have hstable : (prefixWord ++ tailWord_719521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719521).length < 2 ^ (prefixWord ++ tailWord_719521).sum := by decide
  have hdescent : baseEnd_719521 < baseStart_719521 := by decide
  rcases family_descends (prefixWord ++ tailWord_719521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719566 : List Nat := [4, 1, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_719566 : Nat := 118140960795 + 719566 * 2 ^ 59
def prefixEnd_719566 : Nat := 4983230072969 + 3 ^ 40 * 719566 * 2
def baseEnd_719566 : Nat := 246322147088824618943855

theorem tailTrace_719566 : CollatzResearch.WordTrace tailWord_719566 prefixEnd_719566 246322147088824618943855 := by
  unfold tailWord_719566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280591013892843616746319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17496485407428499289313701 3280591013892843616746319)
  ·
    refine ⟨4920886520839265425119479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3280591013892843616746319 4920886520839265425119479)
    ·
      refine ⟨7381329781258898137679219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4920886520839265425119479 7381329781258898137679219)
      ·
        refine ⟨11071994671888347206518829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7381329781258898137679219 11071994671888347206518829)
        ·
          refine ⟨4151998001958130202444561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11071994671888347206518829 4151998001958130202444561)
          ·
            refine ⟨3113998501468597651833421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4151998001958130202444561 3113998501468597651833421)
            ·
              refine ⟨1167749438050724119437533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3113998501468597651833421 1167749438050724119437533)
              ·
                refine ⟨437906039269021544789075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1167749438050724119437533 437906039269021544789075)
                ·
                  refine ⟨656859058903532317183613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437906039269021544789075 656859058903532317183613)
                  ·
                    refine ⟨246322147088824618943855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656859058903532317183613 246322147088824618943855)
                    ·
                      rfl

theorem cell22_719566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_719566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719566 prefixEnd_719566 := by exact prefixLift 719566
  have htrace : WordTrace (prefixWord ++ tailWord_719566) baseStart_719566 baseEnd_719566 := by
    simpa [prefixWord, tailWord_719566, baseEnd_719566] using wordTrace_append hprefix tailTrace_719566
  have hstable : (prefixWord ++ tailWord_719566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719566).length < 2 ^ (prefixWord ++ tailWord_719566).sum := by decide
  have hdescent : baseEnd_719566 < baseStart_719566 := by decide
  rcases family_descends (prefixWord ++ tailWord_719566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719637 : List Nat := [1, 3, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_719637 : Nat := 118140960795 + 719637 * 2 ^ 59
def prefixEnd_719637 : Nat := 4983230072969 + 3 ^ 40 * 719637 * 2
def baseEnd_719637 : Nat := 246346451839804100418637

theorem tailTrace_719637 : CollatzResearch.WordTrace tailWord_719637 prefixEnd_719637 246346451839804100418637 := by
  unfold tailWord_719637
  simp only [CollatzResearch.WordTrace]
  refine ⟨26247317693885528059805165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17498211795923685373203443 26247317693885528059805165)
  ·
    refine ⟨9842744135207073022426937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26247317693885528059805165 9842744135207073022426937)
    ·
      refine ⟨7382058101405304766820203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9842744135207073022426937 7382058101405304766820203)
      ·
        refine ⟨11073087152107957150230305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7382058101405304766820203 11073087152107957150230305)
        ·
          refine ⟨8304815364080967862672729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11073087152107957150230305 8304815364080967862672729)
          ·
            refine ⟨6228611523060725897004547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8304815364080967862672729 6228611523060725897004547)
            ·
              refine ⟨9342917284591088845506821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6228611523060725897004547 9342917284591088845506821)
              ·
                refine ⟨1751796990860829158532529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9342917284591088845506821 1751796990860829158532529)
                ·
                  refine ⟨1313847743145621868899397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1751796990860829158532529 1313847743145621868899397)
                  ·
                    refine ⟨246346451839804100418637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1313847743145621868899397 246346451839804100418637)
                    ·
                      rfl

theorem cell22_719637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_719637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719637 prefixEnd_719637 := by exact prefixLift 719637
  have htrace : WordTrace (prefixWord ++ tailWord_719637) baseStart_719637 baseEnd_719637 := by
    simpa [prefixWord, tailWord_719637, baseEnd_719637] using wordTrace_append hprefix tailTrace_719637
  have hstable : (prefixWord ++ tailWord_719637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719637).length < 2 ^ (prefixWord ++ tailWord_719637).sum := by decide
  have hdescent : baseEnd_719637 < baseStart_719637 := by decide
  rcases family_descends (prefixWord ++ tailWord_719637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719669 : List Nat := [1, 3, 3, 1, 3, 2, 3, 6]
def baseStart_719669 : Nat := 118140960795 + 719669 * 2 ^ 59
def prefixEnd_719669 : Nat := 4983230072969 + 3 ^ 40 * 719669 * 2
def baseEnd_719669 : Nat := 27373045121529631513171

theorem tailTrace_719669 : CollatzResearch.WordTrace tailWord_719669 prefixEnd_719669 27373045121529631513171 := by
  unfold tailWord_719669
  simp only [CollatzResearch.WordTrace]
  refine ⟨26248484829769597524970061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17498989886513065016646707 26248484829769597524970061)
  ·
    refine ⟨9843181811163599071863773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26248484829769597524970061 9843181811163599071863773)
    ·
      refine ⟨3691193179186349651948915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9843181811163599071863773 3691193179186349651948915)
      ·
        refine ⟨5536789768779524477923373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3691193179186349651948915 5536789768779524477923373)
        ·
          refine ⟨2076296163292321679221265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5536789768779524477923373 2076296163292321679221265)
          ·
            refine ⟨1557222122469241259415949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2076296163292321679221265 1557222122469241259415949)
            ·
              refine ⟨583958295925965472280981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1557222122469241259415949 583958295925965472280981)
              ·
                refine ⟨27373045121529631513171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 583958295925965472280981 27373045121529631513171)
                ·
                  rfl

theorem cell22_719669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 6].length) (baseStart_719669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719669 prefixEnd_719669 := by exact prefixLift 719669
  have htrace : WordTrace (prefixWord ++ tailWord_719669) baseStart_719669 baseEnd_719669 := by
    simpa [prefixWord, tailWord_719669, baseEnd_719669] using wordTrace_append hprefix tailTrace_719669
  have hstable : (prefixWord ++ tailWord_719669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719669).length < 2 ^ (prefixWord ++ tailWord_719669).sum := by decide
  have hdescent : baseEnd_719669 < baseStart_719669 := by decide
  rcases family_descends (prefixWord ++ tailWord_719669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719686 : List Nat := [6, 1, 1, 2, 2, 1, 9]
def baseStart_719686 : Nat := 118140960795 + 719686 * 2 ^ 59
def prefixEnd_719686 : Nat := 4983230072969 + 3 ^ 40 * 719686 * 2
def baseEnd_719686 : Nat := 9124563908932752071981

theorem tailTrace_719686 : CollatzResearch.WordTrace tailWord_719686 prefixEnd_719686 9124563908932752071981 := by
  unfold tailWord_719686
  simp only [CollatzResearch.WordTrace]
  refine ⟨820284527209625294635591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17499403247138672952225941 820284527209625294635591)
  ·
    refine ⟨1230426790814437941953387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 820284527209625294635591 1230426790814437941953387)
    ·
      refine ⟨1845640186221656912930081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230426790814437941953387 1845640186221656912930081)
      ·
        refine ⟨1384230139666242684697561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1845640186221656912930081 1384230139666242684697561)
        ·
          refine ⟨1038172604749682013523171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384230139666242684697561 1038172604749682013523171)
          ·
            refine ⟨1557258907124523020284757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038172604749682013523171 1557258907124523020284757)
            ·
              refine ⟨9124563908932752071981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1557258907124523020284757 9124563908932752071981)
              ·
                rfl

theorem cell22_719686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 9].length) (baseStart_719686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719686 prefixEnd_719686 := by exact prefixLift 719686
  have htrace : WordTrace (prefixWord ++ tailWord_719686) baseStart_719686 baseEnd_719686 := by
    simpa [prefixWord, tailWord_719686, baseEnd_719686] using wordTrace_append hprefix tailTrace_719686
  have hstable : (prefixWord ++ tailWord_719686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719686).length < 2 ^ (prefixWord ++ tailWord_719686).sum := by decide
  have hdescent : baseEnd_719686 < baseStart_719686 := by decide
  rcases family_descends (prefixWord ++ tailWord_719686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719701 : List Nat := [1, 3, 2, 2, 2, 1, 1, 6, 1, 3]
def baseStart_719701 : Nat := 118140960795 + 719701 * 2 ^ 59
def prefixEnd_719701 : Nat := 4983230072969 + 3 ^ 40 * 719701 * 2
def baseEnd_719701 : Nat := 246368360347729266818441

theorem tailTrace_719701 : CollatzResearch.WordTrace tailWord_719701 prefixEnd_719701 246368360347729266818441 := by
  unfold tailWord_719701
  simp only [CollatzResearch.WordTrace]
  refine ⟨26249651965653666990134957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17499767977102444660089971 26249651965653666990134957)
  ·
    refine ⟨9843619487120125121300609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26249651965653666990134957 9843619487120125121300609)
    ·
      refine ⟨7382714615340093840975457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9843619487120125121300609 7382714615340093840975457)
      ·
        refine ⟨5537035961505070380731593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7382714615340093840975457 5537035961505070380731593)
        ·
          refine ⟨4152776971128802785548695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5537035961505070380731593 4152776971128802785548695)
          ·
            refine ⟨6229165456693204178323043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152776971128802785548695 6229165456693204178323043)
            ·
              refine ⟨9343748185039806267484565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229165456693204178323043 9343748185039806267484565)
              ·
                refine ⟨437988196173740918788339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9343748185039806267484565 437988196173740918788339)
                ·
                  refine ⟨656982294260611378182509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437988196173740918788339 656982294260611378182509)
                  ·
                    refine ⟨246368360347729266818441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656982294260611378182509 246368360347729266818441)
                    ·
                      rfl

theorem cell22_719701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_719701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719701 prefixEnd_719701 := by exact prefixLift 719701
  have htrace : WordTrace (prefixWord ++ tailWord_719701) baseStart_719701 baseEnd_719701 := by
    simpa [prefixWord, tailWord_719701, baseEnd_719701] using wordTrace_append hprefix tailTrace_719701
  have hstable : (prefixWord ++ tailWord_719701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719701).length < 2 ^ (prefixWord ++ tailWord_719701).sum := by decide
  have hdescent : baseEnd_719701 < baseStart_719701 := by decide
  rcases family_descends (prefixWord ++ tailWord_719701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719712 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 2, 5]
def baseStart_719712 : Nat := 118140960795 + 719712 * 2 ^ 59
def prefixEnd_719712 : Nat := 4983230072969 + 3 ^ 40 * 719712 * 2
def baseEnd_719712 : Nat := 246372125872528904793407

theorem tailTrace_719712 : CollatzResearch.WordTrace tailWord_719712 prefixEnd_719712 246372125872528904793407 := by
  unfold tailWord_719712
  simp only [CollatzResearch.WordTrace]
  refine ⟨13125026584306907934392695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17500035445742543912523593 13125026584306907934392695)
  ·
    refine ⟨19687539876460361901589043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13125026584306907934392695 19687539876460361901589043)
    ·
      refine ⟨29531309814690542852383565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19687539876460361901589043 29531309814690542852383565)
      ·
        refine ⟨11074241180508953569643837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29531309814690542852383565 11074241180508953569643837)
        ·
          refine ⟨4152840442690857588616439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11074241180508953569643837 4152840442690857588616439)
          ·
            refine ⟨6229260664036286382924659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4152840442690857588616439 6229260664036286382924659)
            ·
              refine ⟨9343890996054429574386989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6229260664036286382924659 9343890996054429574386989)
              ·
                refine ⟨3503959123520411090395121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9343890996054429574386989 3503959123520411090395121)
                ·
                  refine ⟨2627969342640308317796341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3503959123520411090395121 2627969342640308317796341)
                  ·
                    refine ⟨246372125872528904793407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2627969342640308317796341 246372125872528904793407)
                    ·
                      rfl

theorem cell22_719712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_719712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719712 prefixEnd_719712 := by exact prefixLift 719712
  have htrace : WordTrace (prefixWord ++ tailWord_719712) baseStart_719712 baseEnd_719712 := by
    simpa [prefixWord, tailWord_719712, baseEnd_719712] using wordTrace_append hprefix tailTrace_719712
  have hstable : (prefixWord ++ tailWord_719712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719712).length < 2 ^ (prefixWord ++ tailWord_719712).sum := by decide
  have hdescent : baseEnd_719712 < baseStart_719712 := by decide
  rcases family_descends (prefixWord ++ tailWord_719712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719727 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 3, 4]
def baseStart_719727 : Nat := 118140960795 + 719727 * 2 ^ 59
def prefixEnd_719727 : Nat := 4983230072969 + 3 ^ 40 * 719727 * 2
def baseEnd_719727 : Nat := 246377260679073865668361

theorem tailTrace_719727 : CollatzResearch.WordTrace tailWord_719727 prefixEnd_719727 246377260679073865668361 := by
  unfold tailWord_719727
  simp only [CollatzResearch.WordTrace]
  refine ⟨26250600263559473430581435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17500400175706315620387623 26250600263559473430581435)
  ·
    refine ⟨39375900395339210145872153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26250600263559473430581435 39375900395339210145872153)
    ·
      refine ⟨29531925296504407609404115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39375900395339210145872153 29531925296504407609404115)
      ·
        refine ⟨44297887944756611414106173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29531925296504407609404115 44297887944756611414106173)
        ·
          refine ⟨16611707979283729280289815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44297887944756611414106173 16611707979283729280289815)
          ·
            refine ⟨24917561968925593920434723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16611707979283729280289815 24917561968925593920434723)
            ·
              refine ⟨37376342953388390880652085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24917561968925593920434723 37376342953388390880652085)
              ·
                refine ⟨3504032151880161645061133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37376342953388390880652085 3504032151880161645061133)
                ·
                  refine ⟨1314012056955060616897925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3504032151880161645061133 1314012056955060616897925)
                  ·
                    refine ⟨246377260679073865668361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1314012056955060616897925 246377260679073865668361)
                    ·
                      rfl

theorem cell22_719727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_719727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719727 prefixEnd_719727 := by exact prefixLift 719727
  have htrace : WordTrace (prefixWord ++ tailWord_719727) baseStart_719727 baseEnd_719727 := by
    simpa [prefixWord, tailWord_719727, baseEnd_719727] using wordTrace_append hprefix tailTrace_719727
  have hstable : (prefixWord ++ tailWord_719727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719727).length < 2 ^ (prefixWord ++ tailWord_719727).sum := by decide
  have hdescent : baseEnd_719727 < baseStart_719727 := by decide
  rcases family_descends (prefixWord ++ tailWord_719727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719778 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_719778 : Nat := 118140960795 + 719778 * 2 ^ 59
def prefixEnd_719778 : Nat := 4983230072969 + 3 ^ 40 * 719778 * 2
def baseEnd_719778 : Nat := 246394719021326732643205

theorem tailTrace_719778 : CollatzResearch.WordTrace tailWord_719778 prefixEnd_719778 246394719021326732643205 := by
  unfold tailWord_719778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563115096593677285171997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17501640257583139427125325 6563115096593677285171997)
  ·
    refine ⟨2461168161222628981939499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6563115096593677285171997 2461168161222628981939499)
    ·
      refine ⟨3691752241833943472909249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2461168161222628981939499 3691752241833943472909249)
      ·
        refine ⟨2768814181375457604681937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3691752241833943472909249 2768814181375457604681937)
        ·
          refine ⟨2076610636031593203511453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2768814181375457604681937 2076610636031593203511453)
          ·
            refine ⟨778728988511847451316795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2076610636031593203511453 778728988511847451316795)
            ·
              refine ⟨1168093482767771176975193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778728988511847451316795 1168093482767771176975193)
              ·
                refine ⟨876070112075828382731395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1168093482767771176975193 876070112075828382731395)
                ·
                  refine ⟨1314105168113742574097093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876070112075828382731395 1314105168113742574097093)
                  ·
                    refine ⟨246394719021326732643205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1314105168113742574097093 246394719021326732643205)
                    ·
                      rfl

theorem cell22_719778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_719778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719778 prefixEnd_719778 := by exact prefixLift 719778
  have htrace : WordTrace (prefixWord ++ tailWord_719778) baseStart_719778 baseEnd_719778 := by
    simpa [prefixWord, tailWord_719778, baseEnd_719778] using wordTrace_append hprefix tailTrace_719778
  have hstable : (prefixWord ++ tailWord_719778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719778).length < 2 ^ (prefixWord ++ tailWord_719778).sum := by decide
  have hdescent : baseEnd_719778 < baseStart_719778 := by decide
  rcases family_descends (prefixWord ++ tailWord_719778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719870 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_719870 : Nat := 118140960795 + 719870 * 2 ^ 59
def prefixEnd_719870 : Nat := 4983230072969 + 3 ^ 40 * 719870 * 2
def baseEnd_719870 : Nat := 246426212501469159342923

theorem tailTrace_719870 : CollatzResearch.WordTrace tailWord_719870 prefixEnd_719870 246426212501469159342923 := by
  unfold tailWord_719870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281976987755176106629633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17503877268027605902024709 3281976987755176106629633)
  ·
    refine ⟨2461482740816382079972225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3281976987755176106629633 2461482740816382079972225)
    ·
      refine ⟨1846112055612286559979169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2461482740816382079972225 1846112055612286559979169)
      ·
        refine ⟨1384584041709214919984377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846112055612286559979169 1384584041709214919984377)
        ·
          refine ⟨1038438031281911189988283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384584041709214919984377 1038438031281911189988283)
          ·
            refine ⟨1557657046922866784982425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038438031281911189988283 1557657046922866784982425)
            ·
              refine ⟨1168242785192150088736819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1557657046922866784982425 1168242785192150088736819)
              ·
                refine ⟨1752364177788225133105229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168242785192150088736819 1752364177788225133105229)
                ·
                  refine ⟨657136566670584424914461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1752364177788225133105229 657136566670584424914461)
                  ·
                    refine ⟨246426212501469159342923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 657136566670584424914461 246426212501469159342923)
                    ·
                      rfl

theorem cell22_719870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_719870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719870 prefixEnd_719870 := by exact prefixLift 719870
  have htrace : WordTrace (prefixWord ++ tailWord_719870) baseStart_719870 baseEnd_719870 := by
    simpa [prefixWord, tailWord_719870, baseEnd_719870] using wordTrace_append hprefix tailTrace_719870
  have hstable : (prefixWord ++ tailWord_719870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719870).length < 2 ^ (prefixWord ++ tailWord_719870).sum := by decide
  have hdescent : baseEnd_719870 < baseStart_719870 := by decide
  rcases family_descends (prefixWord ++ tailWord_719870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719896 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 1, 4]
def baseStart_719896 : Nat := 118140960795 + 719896 * 2 ^ 59
def prefixEnd_719896 : Nat := 4983230072969 + 3 ^ 40 * 719896 * 2
def baseEnd_719896 : Nat := 246435112832813758192843

theorem tailTrace_719896 : CollatzResearch.WordTrace tailWord_719896 prefixEnd_719896 246435112832813758192843 := by
  unfold tailWord_719896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13128382099973607646741771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17504509466631476862322361 13128382099973607646741771)
  ·
    refine ⟨19692573149960411470112657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13128382099973607646741771 19692573149960411470112657)
    ·
      refine ⟨14769429862470308602584493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19692573149960411470112657 14769429862470308602584493)
      ·
        refine ⟨5538536198426365725969185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14769429862470308602584493 5538536198426365725969185)
        ·
          refine ⟨4153902148819774294476889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5538536198426365725969185 4153902148819774294476889)
          ·
            refine ⟨3115426611614830720857667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4153902148819774294476889 3115426611614830720857667)
            ·
              refine ⟨4673139917422246081286501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3115426611614830720857667 4673139917422246081286501)
              ·
                refine ⟨876213734516671140241219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4673139917422246081286501 876213734516671140241219)
                ·
                  refine ⟨1314320601775006710361829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876213734516671140241219 1314320601775006710361829)
                  ·
                    refine ⟨246435112832813758192843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1314320601775006710361829 246435112832813758192843)
                    ·
                      rfl

theorem cell22_719896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_719896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719896 prefixEnd_719896 := by exact prefixLift 719896
  have htrace : WordTrace (prefixWord ++ tailWord_719896) baseStart_719896 baseEnd_719896 := by
    simpa [prefixWord, tailWord_719896, baseEnd_719896] using wordTrace_append hprefix tailTrace_719896
  have hstable : (prefixWord ++ tailWord_719896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719896).length < 2 ^ (prefixWord ++ tailWord_719896).sum := by decide
  have hdescent : baseEnd_719896 < baseStart_719896 := by decide
  rcases family_descends (prefixWord ++ tailWord_719896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719904 : List Nat := [2, 1, 1, 7, 2, 1, 1, 3, 1, 3]
def baseStart_719904 : Nat := 118140960795 + 719904 * 2 ^ 59
def prefixEnd_719904 : Nat := 4983230072969 + 3 ^ 40 * 719904 * 2
def baseEnd_719904 : Nat := 246437851396304403992819

theorem tailTrace_719904 : CollatzResearch.WordTrace tailWord_719904 prefixEnd_719904 246437851396304403992819 := by
  unfold tailWord_719904
  simp only [CollatzResearch.WordTrace]
  refine ⟨13128527991959116329887383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17504703989278821773183177 13128527991959116329887383)
  ·
    refine ⟨19692791987938674494831075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13128527991959116329887383 19692791987938674494831075)
    ·
      refine ⟨29539187981908011742246613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19692791987938674494831075 29539187981908011742246613)
      ·
        refine ⟨692324718325969025208905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 29539187981908011742246613 692324718325969025208905)
        ·
          refine ⟨519243538744476768906679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692324718325969025208905 519243538744476768906679)
          ·
            refine ⟨778865308116715153360019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519243538744476768906679 778865308116715153360019)
            ·
              refine ⟨1168297962175072730040029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778865308116715153360019 1168297962175072730040029)
              ·
                refine ⟨438111735815652273765011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1168297962175072730040029 438111735815652273765011)
                ·
                  refine ⟨657167603723478410647517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438111735815652273765011 657167603723478410647517)
                  ·
                    refine ⟨246437851396304403992819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 657167603723478410647517 246437851396304403992819)
                    ·
                      rfl

theorem cell22_719904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 3].length) (baseStart_719904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719904 prefixEnd_719904 := by exact prefixLift 719904
  have htrace : WordTrace (prefixWord ++ tailWord_719904) baseStart_719904 baseEnd_719904 := by
    simpa [prefixWord, tailWord_719904, baseEnd_719904] using wordTrace_append hprefix tailTrace_719904
  have hstable : (prefixWord ++ tailWord_719904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719904).length < 2 ^ (prefixWord ++ tailWord_719904).sum := by decide
  have hdescent : baseEnd_719904 < baseStart_719904 := by decide
  rcases family_descends (prefixWord ++ tailWord_719904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719909 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_719909 : Nat := 118140960795 + 719909 * 2 ^ 59
def prefixEnd_719909 : Nat := 4983230072969 + 3 ^ 40 * 719909 * 2
def baseEnd_719909 : Nat := 246439562998486057617803

theorem tailTrace_719909 : CollatzResearch.WordTrace tailWord_719909 prefixEnd_719909 246439562998486057617803 := by
  unfold tailWord_719909
  simp only [CollatzResearch.WordTrace]
  refine ⟨26257238348900118513706781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17504825565933412342471187 26257238348900118513706781)
  ·
    refine ⟨9846464380837544442640043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26257238348900118513706781 9846464380837544442640043)
    ·
      refine ⟨14769696571256316663960065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9846464380837544442640043 14769696571256316663960065)
      ·
        refine ⟨11077272428442237497970049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14769696571256316663960065 11077272428442237497970049)
        ·
          refine ⟨8307954321331678123477537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11077272428442237497970049 8307954321331678123477537)
          ·
            refine ⟨6230965740998758592608153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8307954321331678123477537 6230965740998758592608153)
            ·
              refine ⟨4673224305749068944456115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6230965740998758592608153 4673224305749068944456115)
              ·
                refine ⟨7009836458623603416684173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4673224305749068944456115 7009836458623603416684173)
                ·
                  refine ⟨2628688671983851281256565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7009836458623603416684173 2628688671983851281256565)
                  ·
                    refine ⟨246439562998486057617803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2628688671983851281256565 246439562998486057617803)
                    ·
                      rfl

theorem cell22_719909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_719909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719909 prefixEnd_719909 := by exact prefixLift 719909
  have htrace : WordTrace (prefixWord ++ tailWord_719909) baseStart_719909 baseEnd_719909 := by
    simpa [prefixWord, tailWord_719909, baseEnd_719909] using wordTrace_append hprefix tailTrace_719909
  have hstable : (prefixWord ++ tailWord_719909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719909).length < 2 ^ (prefixWord ++ tailWord_719909).sum := by decide
  have hdescent : baseEnd_719909 < baseStart_719909 := by decide
  rcases family_descends (prefixWord ++ tailWord_719909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719939 : List Nat := [1, 1, 1, 3, 1, 2, 6, 7]
def baseStart_719939 : Nat := 118140960795 + 719939 * 2 ^ 59
def prefixEnd_719939 : Nat := 4983230072969 + 3 ^ 40 * 719939 * 2
def baseEnd_719939 : Nat := 27383314734619553263079

theorem tailTrace_719939 : CollatzResearch.WordTrace tailWord_719939 prefixEnd_719939 27383314734619553263079 := by
  unfold tailWord_719939
  simp only [CollatzResearch.WordTrace]
  refine ⟨26258332538791433637298871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17505555025860955758199247 26258332538791433637298871)
  ·
    refine ⟨39387498808187150455948307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26258332538791433637298871 39387498808187150455948307)
    ·
      refine ⟨59081248212280725683922461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39387498808187150455948307 59081248212280725683922461)
      ·
        refine ⟨22155468079605272131470923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59081248212280725683922461 22155468079605272131470923)
        ·
          refine ⟨33233202119407908197206385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22155468079605272131470923 33233202119407908197206385)
          ·
            refine ⟨24924901589555931147904789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33233202119407908197206385 24924901589555931147904789)
            ·
              refine ⟨1168354762010434272558037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24924901589555931147904789 1168354762010434272558037)
              ·
                refine ⟨27383314734619553263079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1168354762010434272558037 27383314734619553263079)
                ·
                  rfl

theorem cell22_719939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 7].length) (baseStart_719939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719939 prefixEnd_719939 := by exact prefixLift 719939
  have htrace : WordTrace (prefixWord ++ tailWord_719939) baseStart_719939 baseEnd_719939 := by
    simpa [prefixWord, tailWord_719939, baseEnd_719939] using wordTrace_append hprefix tailTrace_719939
  have hstable : (prefixWord ++ tailWord_719939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719939).length < 2 ^ (prefixWord ++ tailWord_719939).sum := by decide
  have hdescent : baseEnd_719939 < baseStart_719939 := by decide
  rcases family_descends (prefixWord ++ tailWord_719939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719943 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 2, 3]
def baseStart_719943 : Nat := 118140960795 + 719943 * 2 ^ 59
def prefixEnd_719943 : Nat := 4983230072969 + 3 ^ 40 * 719943 * 2
def baseEnd_719943 : Nat := 246451201893321302267699

theorem tailTrace_719943 : CollatzResearch.WordTrace tailWord_719943 prefixEnd_719943 246451201893321302267699 := by
  unfold tailWord_719943
  simp only [CollatzResearch.WordTrace]
  refine ⟨26258478430776942320444483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17505652287184628213629655 26258478430776942320444483)
  ·
    refine ⟨39387717646165413480666725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26258478430776942320444483 39387717646165413480666725)
    ·
      refine ⟨7385197058656015027625011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39387717646165413480666725 7385197058656015027625011)
      ·
        refine ⟨11077795587984022541437517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7385197058656015027625011 11077795587984022541437517)
        ·
          refine ⟨4154173345494008453039069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11077795587984022541437517 4154173345494008453039069)
          ·
            refine ⟨1557815004560253169889651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4154173345494008453039069 1557815004560253169889651)
            ·
              refine ⟨2336722506840379754834477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557815004560253169889651 2336722506840379754834477)
              ·
                refine ⟨876270940065142408062929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2336722506840379754834477 876270940065142408062929)
                ·
                  refine ⟨657203205048856806047197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 876270940065142408062929 657203205048856806047197)
                  ·
                    refine ⟨246451201893321302267699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 657203205048856806047197 246451201893321302267699)
                    ·
                      rfl

theorem cell22_719943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_719943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719943 prefixEnd_719943 := by exact prefixLift 719943
  have htrace : WordTrace (prefixWord ++ tailWord_719943) baseStart_719943 baseEnd_719943 := by
    simpa [prefixWord, tailWord_719943, baseEnd_719943] using wordTrace_append hprefix tailTrace_719943
  have hstable : (prefixWord ++ tailWord_719943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719943).length < 2 ^ (prefixWord ++ tailWord_719943).sum := by decide
  have hdescent : baseEnd_719943 < baseStart_719943 := by decide
  rcases family_descends (prefixWord ++ tailWord_719943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720065 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_720065 : Nat := 118140960795 + 720065 * 2 ^ 59
def prefixEnd_720065 : Nat := 4983230072969 + 3 ^ 40 * 720065 * 2
def baseEnd_720065 : Nat := 246492964986553650717325

theorem tailTrace_720065 : CollatzResearch.WordTrace tailWord_720065 prefixEnd_720065 246492964986553650717325 := by
  unfold tailWord_720065
  simp only [CollatzResearch.WordTrace]
  refine ⟨26262928136334957156385649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17508618757556638104257099 26262928136334957156385649)
  ·
    refine ⟨19697196102251217867289237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26262928136334957156385649 19697196102251217867289237)
    ·
      refine ⟨923306067293025837529183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19697196102251217867289237 923306067293025837529183)
      ·
        refine ⟨1384959100939538756293775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923306067293025837529183 1384959100939538756293775)
        ·
          refine ⟨2077438651409308134440663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384959100939538756293775 2077438651409308134440663)
          ·
            refine ⟨3116157977113962201660995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077438651409308134440663 3116157977113962201660995)
            ·
              refine ⟨4674236965670943302491493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3116157977113962201660995 4674236965670943302491493)
              ·
                refine ⟨876419431063301869217155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4674236965670943302491493 876419431063301869217155)
                ·
                  refine ⟨1314629146594952803825733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876419431063301869217155 1314629146594952803825733)
                  ·
                    refine ⟨246492964986553650717325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1314629146594952803825733 246492964986553650717325)
                    ·
                      rfl

theorem cell22_720065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_720065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720065 prefixEnd_720065 := by exact prefixLift 720065
  have htrace : WordTrace (prefixWord ++ tailWord_720065) baseStart_720065 baseEnd_720065 := by
    simpa [prefixWord, tailWord_720065, baseEnd_720065] using wordTrace_append hprefix tailTrace_720065
  have hstable : (prefixWord ++ tailWord_720065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720065).length < 2 ^ (prefixWord ++ tailWord_720065).sum := by decide
  have hdescent : baseEnd_720065 < baseStart_720065 := by decide
  rcases family_descends (prefixWord ++ tailWord_720065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720116 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_720116 : Nat := 118140960795 + 720116 * 2 ^ 59
def prefixEnd_720116 : Nat := 4983230072969 + 3 ^ 40 * 720116 * 2
def baseEnd_720116 : Nat := 246510423328806517692169

theorem tailTrace_720116 : CollatzResearch.WordTrace tailWord_720116 prefixEnd_720116 246510423328806517692169 := by
  unfold tailWord_720116
  simp only [CollatzResearch.WordTrace]
  refine ⟨13132394129575096433246101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17509858839433461910994801 13132394129575096433246101)
  ·
    refine ⟨615580974823832645308411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13132394129575096433246101 615580974823832645308411)
    ·
      refine ⟨923371462235748967962617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615580974823832645308411 923371462235748967962617)
      ·
        refine ⟨692528596676811725971963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 923371462235748967962617 692528596676811725971963)
        ·
          refine ⟨1038792895015217588957945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692528596676811725971963 1038792895015217588957945)
          ·
            refine ⟨779094671261413191718459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1038792895015217588957945 779094671261413191718459)
            ·
              refine ⟨1168642006892119787577689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779094671261413191718459 1168642006892119787577689)
              ·
                refine ⟨876481505169089840683267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1168642006892119787577689 876481505169089840683267)
                ·
                  refine ⟨1314722257753634761024901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876481505169089840683267 1314722257753634761024901)
                  ·
                    refine ⟨246510423328806517692169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1314722257753634761024901 246510423328806517692169)
                    ·
                      rfl

theorem cell22_720116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_720116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720116 prefixEnd_720116 := by exact prefixLift 720116
  have htrace : WordTrace (prefixWord ++ tailWord_720116) baseStart_720116 baseEnd_720116 := by
    simpa [prefixWord, tailWord_720116, baseEnd_720116] using wordTrace_append hprefix tailTrace_720116
  have hstable : (prefixWord ++ tailWord_720116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720116).length < 2 ^ (prefixWord ++ tailWord_720116).sum := by decide
  have hdescent : baseEnd_720116 < baseStart_720116 := by decide
  rcases family_descends (prefixWord ++ tailWord_720116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720168 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 1, 7]
def baseStart_720168 : Nat := 118140960795 + 720168 * 2 ^ 59
def prefixEnd_720168 : Nat := 4983230072969 + 3 ^ 40 * 720168 * 2
def baseEnd_720168 : Nat := 246528223991495715392009

theorem tailTrace_720168 : CollatzResearch.WordTrace tailWord_720168 prefixEnd_720168 246528223991495715392009 := by
  unfold tailWord_720168
  simp only [CollatzResearch.WordTrace]
  refine ⟨13133342427480902873692579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17511123236641203831590105 13133342427480902873692579)
  ·
    refine ⟨19700013641221354310538869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13133342427480902873692579 19700013641221354310538869)
    ·
      refine ⟨1846876278864501966613019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19700013641221354310538869 1846876278864501966613019)
      ·
        refine ⟨2770314418296752949919529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1846876278864501966613019 2770314418296752949919529)
        ·
          refine ⟨2077735813722564712439647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2770314418296752949919529 2077735813722564712439647)
          ·
            refine ⟨3116603720583847068659471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077735813722564712439647 3116603720583847068659471)
            ·
              refine ⟨4674905580875770602989207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3116603720583847068659471 4674905580875770602989207)
              ·
                refine ⟨7012358371313655904483811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4674905580875770602989207 7012358371313655904483811)
                ·
                  refine ⟨10518537556970483856725717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7012358371313655904483811 10518537556970483856725717)
                  ·
                    refine ⟨246528223991495715392009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10518537556970483856725717 246528223991495715392009)
                    ·
                      rfl

theorem cell22_720168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_720168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720168 prefixEnd_720168 := by exact prefixLift 720168
  have htrace : WordTrace (prefixWord ++ tailWord_720168) baseStart_720168 baseEnd_720168 := by
    simpa [prefixWord, tailWord_720168, baseEnd_720168] using wordTrace_append hprefix tailTrace_720168
  have hstable : (prefixWord ++ tailWord_720168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720168).length < 2 ^ (prefixWord ++ tailWord_720168).sum := by decide
  have hdescent : baseEnd_720168 < baseStart_720168 := by decide
  rcases family_descends (prefixWord ++ tailWord_720168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720170 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_720170 : Nat := 118140960795 + 720170 * 2 ^ 59
def prefixEnd_720170 : Nat := 4983230072969 + 3 ^ 40 * 720170 * 2
def baseEnd_720170 : Nat := 82176302877456125614001

theorem tailTrace_720170 : CollatzResearch.WordTrace tailWord_720170 prefixEnd_720170 82176302877456125614001 := by
  unfold tailWord_720170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566689450238640022239491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17511171867303040059305309 6566689450238640022239491)
  ·
    refine ⟨9850034175357960033359237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6566689450238640022239491 9850034175357960033359237)
    ·
      refine ⟨1846881407879617506254857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9850034175357960033359237 1846881407879617506254857)
      ·
        refine ⟨1385161055909713129691143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846881407879617506254857 1385161055909713129691143)
        ·
          refine ⟨2077741583864569694536715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385161055909713129691143 2077741583864569694536715)
          ·
            refine ⟨3116612375796854541805073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077741583864569694536715 3116612375796854541805073)
            ·
              refine ⟨2337459281847640906353805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3116612375796854541805073 2337459281847640906353805)
              ·
                refine ⟨876547230692865339882677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2337459281847640906353805 876547230692865339882677)
                ·
                  refine ⟨82176302877456125614001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 876547230692865339882677 82176302877456125614001)
                  ·
                    rfl

theorem cell22_720170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_720170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720170 prefixEnd_720170 := by exact prefixLift 720170
  have htrace : WordTrace (prefixWord ++ tailWord_720170) baseStart_720170 baseEnd_720170 := by
    simpa [prefixWord, tailWord_720170, baseEnd_720170] using wordTrace_append hprefix tailTrace_720170
  have hstable : (prefixWord ++ tailWord_720170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720170).length < 2 ^ (prefixWord ++ tailWord_720170).sum := by decide
  have hdescent : baseEnd_720170 < baseStart_720170 := by decide
  rcases family_descends (prefixWord ++ tailWord_720170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720215 : List Nat := [1, 1, 3, 2, 3, 2, 2, 4, 4]
def baseStart_720215 : Nat := 118140960795 + 720215 * 2 ^ 59
def prefixEnd_720215 : Nat := 4983230072969 + 3 ^ 40 * 720215 * 2
def baseEnd_720215 : Nat := 82181437684001086488955

theorem tailTrace_720215 : CollatzResearch.WordTrace tailWord_720215 prefixEnd_720215 82181437684001086488955 := by
  unfold tailWord_720215
  simp only [CollatzResearch.WordTrace]
  refine ⟨26268399085791532774346099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17512266057194355182897399 26268399085791532774346099)
  ·
    refine ⟨39402598628687299161519149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26268399085791532774346099 39402598628687299161519149)
    ·
      refine ⟨14775974485757737185569681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39402598628687299161519149 14775974485757737185569681)
      ·
        refine ⟨11081980864318302889177261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14775974485757737185569681 11081980864318302889177261)
        ·
          refine ⟨4155742824119363583441473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11081980864318302889177261 4155742824119363583441473)
          ·
            refine ⟨3116807118089522687581105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4155742824119363583441473 3116807118089522687581105)
            ·
              refine ⟨2337605338567142015685829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3116807118089522687581105 2337605338567142015685829)
              ·
                refine ⟨438301000981339127941093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2337605338567142015685829 438301000981339127941093)
                ·
                  refine ⟨82181437684001086488955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 438301000981339127941093 82181437684001086488955)
                  ·
                    rfl

theorem cell22_720215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 4].length) (baseStart_720215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720215 prefixEnd_720215 := by exact prefixLift 720215
  have htrace : WordTrace (prefixWord ++ tailWord_720215) baseStart_720215 baseEnd_720215 := by
    simpa [prefixWord, tailWord_720215, baseEnd_720215] using wordTrace_append hprefix tailTrace_720215
  have hstable : (prefixWord ++ tailWord_720215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720215).length < 2 ^ (prefixWord ++ tailWord_720215).sum := by decide
  have hdescent : baseEnd_720215 < baseStart_720215 := by decide
  rcases family_descends (prefixWord ++ tailWord_720215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720221 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 5]
def baseStart_720221 : Nat := 118140960795 + 720221 * 2 ^ 59
def prefixEnd_720221 : Nat := 4983230072969 + 3 ^ 40 * 720221 * 2
def baseEnd_720221 : Nat := 82182122324873747938949

theorem tailTrace_720221 : CollatzResearch.WordTrace tailWord_720221 prefixEnd_720221 82182122324873747938949 := by
  unfold tailWord_720221
  simp only [CollatzResearch.WordTrace]
  refine ⟨26268617923769795799064517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17512411949179863866043011 26268617923769795799064517)
  ·
    refine ⟨4925365860706836712324597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26268617923769795799064517 4925365860706836712324597)
    ·
      refine ⟨461753049441265941780431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4925365860706836712324597 461753049441265941780431)
      ·
        refine ⟨692629574161898912670647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461753049441265941780431 692629574161898912670647)
        ·
          refine ⟨1038944361242848369005971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692629574161898912670647 1038944361242848369005971)
          ·
            refine ⟨1558416541864272553508957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038944361242848369005971 1558416541864272553508957)
            ·
              refine ⟨584406203199102207565859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1558416541864272553508957 584406203199102207565859)
              ·
                refine ⟨876609304798653311348789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584406203199102207565859 876609304798653311348789)
                ·
                  refine ⟨82182122324873747938949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 876609304798653311348789 82182122324873747938949)
                  ·
                    rfl

theorem cell22_720221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_720221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720221 prefixEnd_720221 := by exact prefixLift 720221
  have htrace : WordTrace (prefixWord ++ tailWord_720221) baseStart_720221 baseEnd_720221 := by
    simpa [prefixWord, tailWord_720221, baseEnd_720221] using wordTrace_append hprefix tailTrace_720221
  have hstable : (prefixWord ++ tailWord_720221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720221).length < 2 ^ (prefixWord ++ tailWord_720221).sum := by decide
  have hdescent : baseEnd_720221 < baseStart_720221 := by decide
  rcases family_descends (prefixWord ++ tailWord_720221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720228 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_720228 : Nat := 118140960795 + 720228 * 2 ^ 59
def prefixEnd_720228 : Nat := 4983230072969 + 3 ^ 40 * 720228 * 2
def baseEnd_720228 : Nat := 246548763217675558891825

theorem tailTrace_720228 : CollatzResearch.WordTrace tailWord_720228 prefixEnd_720228 246548763217675558891825 := by
  unfold tailWord_720228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13134436617372217997284669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17512582156496290663046225 13134436617372217997284669)
  ·
    refine ⟨4925413731514581748981751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13134436617372217997284669 4925413731514581748981751)
    ·
      refine ⟨7388120597271872623472627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4925413731514581748981751 7388120597271872623472627)
      ·
        refine ⟨11082180895907808935208941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7388120597271872623472627 11082180895907808935208941)
        ·
          refine ⟨4155817835965428350703353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11082180895907808935208941 4155817835965428350703353)
          ·
            refine ⟨3116863376974071263027515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4155817835965428350703353 3116863376974071263027515)
            ·
              refine ⟨4675295065461106894541273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3116863376974071263027515 4675295065461106894541273)
              ·
                refine ⟨3506471299095830170905955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4675295065461106894541273 3506471299095830170905955)
                ·
                  refine ⟨5259706948643745256358933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3506471299095830170905955 5259706948643745256358933)
                  ·
                    refine ⟨246548763217675558891825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5259706948643745256358933 246548763217675558891825)
                    ·
                      rfl

theorem cell22_720228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_720228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720228 prefixEnd_720228 := by exact prefixLift 720228
  have htrace : WordTrace (prefixWord ++ tailWord_720228) baseStart_720228 baseEnd_720228 := by
    simpa [prefixWord, tailWord_720228, baseEnd_720228] using wordTrace_append hprefix tailTrace_720228
  have hstable : (prefixWord ++ tailWord_720228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720228).length < 2 ^ (prefixWord ++ tailWord_720228).sum := by decide
  have hdescent : baseEnd_720228 < baseStart_720228 := by decide
  rcases family_descends (prefixWord ++ tailWord_720228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720369 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 1, 4]
def baseStart_720369 : Nat := 118140960795 + 720369 * 2 ^ 59
def prefixEnd_720369 : Nat := 4983230072969 + 3 ^ 40 * 720369 * 2
def baseEnd_720369 : Nat := 246597030399198191116393

theorem tailTrace_720369 : CollatzResearch.WordTrace tailWord_720369 prefixEnd_720369 246597030399198191116393 := by
  unfold tailWord_720369
  simp only [CollatzResearch.WordTrace]
  refine ⟨26274015927233617075452161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17516010618155744716968107 26274015927233617075452161)
  ·
    refine ⟨19705511945425212806589121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26274015927233617075452161 19705511945425212806589121)
    ·
      refine ⟨14779133959068909604941841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19705511945425212806589121 14779133959068909604941841)
      ·
        refine ⟨11084350469301682203706381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14779133959068909604941841 11084350469301682203706381)
        ·
          refine ⟨4156631425988130826389893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11084350469301682203706381 4156631425988130826389893)
          ·
            refine ⟨779368392372774529948105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4156631425988130826389893 779368392372774529948105)
            ·
              refine ⟨584526294279580897461079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779368392372774529948105 584526294279580897461079)
              ·
                refine ⟨876789441419371346191619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584526294279580897461079 876789441419371346191619)
                ·
                  refine ⟨1315184162129057019287429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876789441419371346191619 1315184162129057019287429)
                  ·
                    refine ⟨246597030399198191116393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1315184162129057019287429 246597030399198191116393)
                    ·
                      rfl

theorem cell22_720369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_720369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720369 prefixEnd_720369 := by exact prefixLift 720369
  have htrace : WordTrace (prefixWord ++ tailWord_720369) baseStart_720369 baseEnd_720369 := by
    simpa [prefixWord, tailWord_720369, baseEnd_720369] using wordTrace_append hprefix tailTrace_720369
  have hstable : (prefixWord ++ tailWord_720369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720369).length < 2 ^ (prefixWord ++ tailWord_720369).sum := by decide
  have hdescent : baseEnd_720369 < baseStart_720369 := by decide
  rcases family_descends (prefixWord ++ tailWord_720369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720378 : List Nat := [3, 1, 1, 1, 1, 2, 13]
def baseStart_720378 : Nat := 118140960795 + 720378 * 2 ^ 59
def prefixEnd_720378 : Nat := 4983230072969 + 3 ^ 40 * 720378 * 2
def baseEnd_720378 : Nat := 9133337454930561764495

theorem tailTrace_720378 : CollatzResearch.WordTrace tailWord_720378 prefixEnd_720378 9133337454930561764495 := by
  unfold tailWord_720378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6568586046050252903132447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17516229456134007741686525 6568586046050252903132447)
  ·
    refine ⟨9852879069075379354698671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6568586046050252903132447 9852879069075379354698671)
    ·
      refine ⟨14779318603613069032048007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9852879069075379354698671 14779318603613069032048007)
      ·
        refine ⟨22168977905419603548072011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14779318603613069032048007 22168977905419603548072011)
        ·
          refine ⟨33253466858129405322108017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22168977905419603548072011 33253466858129405322108017)
          ·
            refine ⟨24940100143597053991581013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33253466858129405322108017 24940100143597053991581013)
            ·
              refine ⟨9133337454930561764495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 24940100143597053991581013 9133337454930561764495)
              ·
                rfl

theorem cell22_720378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 13].length) (baseStart_720378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720378 prefixEnd_720378 := by exact prefixLift 720378
  have htrace : WordTrace (prefixWord ++ tailWord_720378) baseStart_720378 baseEnd_720378 := by
    simpa [prefixWord, tailWord_720378, baseEnd_720378] using wordTrace_append hprefix tailTrace_720378
  have hstable : (prefixWord ++ tailWord_720378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720378).length < 2 ^ (prefixWord ++ tailWord_720378).sum := by decide
  have hdescent : baseEnd_720378 < baseStart_720378 := by decide
  rcases family_descends (prefixWord ++ tailWord_720378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720380 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_720380 : Nat := 118140960795 + 720380 * 2 ^ 59
def prefixEnd_720380 : Nat := 4983230072969 + 3 ^ 40 * 720380 * 2
def baseEnd_720380 : Nat := 246600795923997829091359

theorem tailTrace_720380 : CollatzResearch.WordTrace tailWord_720380 prefixEnd_720380 246600795923997829091359 := by
  unfold tailWord_720380
  simp only [CollatzResearch.WordTrace]
  refine ⟨13137208565096882977051297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17516278086795843969401729 13137208565096882977051297)
  ·
    refine ⟨9852906423822662232788473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13137208565096882977051297 9852906423822662232788473)
    ·
      refine ⟨7389679817866996674591355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9852906423822662232788473 7389679817866996674591355)
      ·
        refine ⟨11084519726800495011887033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7389679817866996674591355 11084519726800495011887033)
        ·
          refine ⟨8313389795100371258915275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11084519726800495011887033 8313389795100371258915275)
          ·
            refine ⟨12470084692650556888372913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8313389795100371258915275 12470084692650556888372913)
            ·
              refine ⟨9352563519487917666279685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12470084692650556888372913 9352563519487917666279685)
              ·
                refine ⟨1753605659903984562427441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9352563519487917666279685 1753605659903984562427441)
                ·
                  refine ⟨1315204244927988421820581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1753605659903984562427441 1315204244927988421820581)
                  ·
                    refine ⟨246600795923997829091359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1315204244927988421820581 246600795923997829091359)
                    ·
                      rfl

theorem cell22_720380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_720380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720380 prefixEnd_720380 := by exact prefixLift 720380
  have htrace : WordTrace (prefixWord ++ tailWord_720380) baseStart_720380 baseEnd_720380 := by
    simpa [prefixWord, tailWord_720380, baseEnd_720380] using wordTrace_append hprefix tailTrace_720380
  have hstable : (prefixWord ++ tailWord_720380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720380).length < 2 ^ (prefixWord ++ tailWord_720380).sum := by decide
  have hdescent : baseEnd_720380 < baseStart_720380 := by decide
  rcases family_descends (prefixWord ++ tailWord_720380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720440 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 7]
def baseStart_720440 : Nat := 118140960795 + 720440 * 2 ^ 59
def prefixEnd_720440 : Nat := 4983230072969 + 3 ^ 40 * 720440 * 2
def baseEnd_720440 : Nat := 82207111716725890863725

theorem tailTrace_720440 : CollatzResearch.WordTrace tailWord_720440 prefixEnd_720440 82207111716725890863725 := by
  unfold tailWord_720440
  simp only [CollatzResearch.WordTrace]
  refine ⟨13138302754988198100643387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17517737006650930800857849 13138302754988198100643387)
  ·
    refine ⟨19707454132482297150965081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13138302754988198100643387 19707454132482297150965081)
    ·
      refine ⟨14780590599361722863223811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19707454132482297150965081 14780590599361722863223811)
      ·
        refine ⟨22170885899042584294835717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14780590599361722863223811 22170885899042584294835717)
        ·
          refine ⟨4157041106070484555281697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22170885899042584294835717 4157041106070484555281697)
          ·
            refine ⟨3117780829552863416461273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4157041106070484555281697 3117780829552863416461273)
            ·
              refine ⟨2338335622164647562345955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3117780829552863416461273 2338335622164647562345955)
              ·
                refine ⟨3507503433246971343518933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2338335622164647562345955 3507503433246971343518933)
                ·
                  refine ⟨82207111716725890863725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3507503433246971343518933 82207111716725890863725)
                  ·
                    rfl

theorem cell22_720440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_720440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720440 prefixEnd_720440 := by exact prefixLift 720440
  have htrace : WordTrace (prefixWord ++ tailWord_720440) baseStart_720440 baseEnd_720440 := by
    simpa [prefixWord, tailWord_720440, baseEnd_720440] using wordTrace_append hprefix tailTrace_720440
  have hstable : (prefixWord ++ tailWord_720440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720440).length < 2 ^ (prefixWord ++ tailWord_720440).sum := by decide
  have hdescent : baseEnd_720440 < baseStart_720440 := by decide
  rcases family_descends (prefixWord ++ tailWord_720440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720487 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 1, 4]
def baseStart_720487 : Nat := 118140960795 + 720487 * 2 ^ 59
def prefixEnd_720487 : Nat := 4983230072969 + 3 ^ 40 * 720487 * 2
def baseEnd_720487 : Nat := 246637424210685216666031

theorem tailTrace_720487 : CollatzResearch.WordTrace tailWord_720487 prefixEnd_720487 246637424210685216666031 := by
  unfold tailWord_720487
  simp only [CollatzResearch.WordTrace]
  refine ⟨26278319740806123228247715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17518879827204082152165143 26278319740806123228247715)
  ·
    refine ⟨39417479611209184842371573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26278319740806123228247715 39417479611209184842371573)
    ·
      refine ⟨3695388713550861078972335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39417479611209184842371573 3695388713550861078972335)
      ·
        refine ⟨5543083070326291618458503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3695388713550861078972335 5543083070326291618458503)
        ·
          refine ⟨8314624605489437427687755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5543083070326291618458503 8314624605489437427687755)
          ·
            refine ⟨12471936908234156141531633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8314624605489437427687755 12471936908234156141531633)
            ·
              refine ⟨9353952681175617106148725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12471936908234156141531633 9353952681175617106148725)
              ·
                refine ⟨876933063860214103701443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9353952681175617106148725 876933063860214103701443)
                ·
                  refine ⟨1315399595790321155552165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876933063860214103701443 1315399595790321155552165)
                  ·
                    refine ⟨246637424210685216666031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1315399595790321155552165 246637424210685216666031)
                    ·
                      rfl

theorem cell22_720487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_720487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720487 prefixEnd_720487 := by exact prefixLift 720487
  have htrace : WordTrace (prefixWord ++ tailWord_720487) baseStart_720487 baseEnd_720487 := by
    simpa [prefixWord, tailWord_720487, baseEnd_720487] using wordTrace_append hprefix tailTrace_720487
  have hstable : (prefixWord ++ tailWord_720487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720487).length < 2 ^ (prefixWord ++ tailWord_720487).sum := by decide
  have hdescent : baseEnd_720487 < baseStart_720487 := by decide
  rcases family_descends (prefixWord ++ tailWord_720487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720515 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 1, 6]
def baseStart_720515 : Nat := 118140960795 + 720515 * 2 ^ 59
def prefixEnd_720515 : Nat := 4983230072969 + 3 ^ 40 * 720515 * 2
def baseEnd_720515 : Nat := 246647009182902476965945

theorem tailTrace_720515 : CollatzResearch.WordTrace tailWord_720515 prefixEnd_720515 246647009182902476965945 := by
  unfold tailWord_720515
  simp only [CollatzResearch.WordTrace]
  refine ⟨26279340984704684010266999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17519560656469789340177999 26279340984704684010266999)
  ·
    refine ⟨39419011477057026015400499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26279340984704684010266999 39419011477057026015400499)
    ·
      refine ⟨59128517215585539023100749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39419011477057026015400499 59128517215585539023100749)
      ·
        refine ⟨22173193955844577133662781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59128517215585539023100749 22173193955844577133662781)
        ·
          refine ⟨8314947733441716425123543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22173193955844577133662781 8314947733441716425123543)
          ·
            refine ⟨12472421600162574637685315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8314947733441716425123543 12472421600162574637685315)
            ·
              refine ⟨18708632400243861956527973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12472421600162574637685315 18708632400243861956527973)
              ·
                refine ⟨3507868575045724116848995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18708632400243861956527973 3507868575045724116848995)
                ·
                  refine ⟨5261802862568586175273493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3507868575045724116848995 5261802862568586175273493)
                  ·
                    refine ⟨246647009182902476965945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5261802862568586175273493 246647009182902476965945)
                    ·
                      rfl

theorem cell22_720515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_720515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720515 prefixEnd_720515 := by exact prefixLift 720515
  have htrace : WordTrace (prefixWord ++ tailWord_720515) baseStart_720515 baseEnd_720515 := by
    simpa [prefixWord, tailWord_720515, baseEnd_720515] using wordTrace_append hprefix tailTrace_720515
  have hstable : (prefixWord ++ tailWord_720515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720515).length < 2 ^ (prefixWord ++ tailWord_720515).sum := by decide
  have hdescent : baseEnd_720515 < baseStart_720515 := by decide
  rcases family_descends (prefixWord ++ tailWord_720515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720517 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_720517 : Nat := 118140960795 + 720517 * 2 ^ 59
def prefixEnd_720517 : Nat := 4983230072969 + 3 ^ 40 * 720517 * 2
def baseEnd_720517 : Nat := 246647693823775138415939

theorem tailTrace_720517 : CollatzResearch.WordTrace tailWord_720517 prefixEnd_720517 246647693823775138415939 := by
  unfold tailWord_720517
  simp only [CollatzResearch.WordTrace]
  refine ⟨26279413930697438351839805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17519609287131625567893203 26279413930697438351839805)
  ·
    refine ⟨9854780224011539381939927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26279413930697438351839805 9854780224011539381939927)
    ·
      refine ⟨14782170336017309072909891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9854780224011539381939927 14782170336017309072909891)
      ·
        refine ⟨22173255504025963609364837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14782170336017309072909891 22173255504025963609364837)
        ·
          refine ⟨4157485407004868176755907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22173255504025963609364837 4157485407004868176755907)
          ·
            refine ⟨6236228110507302265133861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4157485407004868176755907 6236228110507302265133861)
            ·
              refine ⟨1169292770720119174712599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6236228110507302265133861 1169292770720119174712599)
              ·
                refine ⟨1753939156080178762068899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169292770720119174712599 1753939156080178762068899)
                ·
                  refine ⟨2630908734120268143103349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1753939156080178762068899 2630908734120268143103349)
                  ·
                    refine ⟨246647693823775138415939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2630908734120268143103349 246647693823775138415939)
                    ·
                      rfl

theorem cell22_720517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_720517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720517 prefixEnd_720517 := by exact prefixLift 720517
  have htrace : WordTrace (prefixWord ++ tailWord_720517) baseStart_720517 baseEnd_720517 := by
    simpa [prefixWord, tailWord_720517, baseEnd_720517] using wordTrace_append hprefix tailTrace_720517
  have hstable : (prefixWord ++ tailWord_720517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720517).length < 2 ^ (prefixWord ++ tailWord_720517).sum := by decide
  have hdescent : baseEnd_720517 < baseStart_720517 := by decide
  rcases family_descends (prefixWord ++ tailWord_720517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720560 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_720560 : Nat := 118140960795 + 720560 * 2 ^ 59
def prefixEnd_720560 : Nat := 4983230072969 + 3 ^ 40 * 720560 * 2
def baseEnd_720560 : Nat := 246662413602537359590807

theorem tailTrace_720560 : CollatzResearch.WordTrace tailWord_720560 prefixEnd_720560 246662413602537359590807 := by
  unfold tailWord_720560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13140491134770828347827567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17520654846361104463770089 13140491134770828347827567)
  ·
    refine ⟨19710736702156242521741351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13140491134770828347827567 19710736702156242521741351)
    ·
      refine ⟨29566105053234363782612027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19710736702156242521741351 29566105053234363782612027)
      ·
        refine ⟨44349157579851545673918041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29566105053234363782612027 44349157579851545673918041)
        ·
          refine ⟨33261868184888659255438531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44349157579851545673918041 33261868184888659255438531)
          ·
            refine ⟨49892802277332988883157797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33261868184888659255438531 49892802277332988883157797)
            ·
              refine ⟨9354900426999935415592087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49892802277332988883157797 9354900426999935415592087)
              ·
                refine ⟨14032350640499903123388131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9354900426999935415592087 14032350640499903123388131)
                ·
                  refine ⟨21048525960749854685082197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14032350640499903123388131 21048525960749854685082197)
                  ·
                    refine ⟨246662413602537359590807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21048525960749854685082197 246662413602537359590807)
                    ·
                      rfl

theorem cell22_720560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_720560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720560 prefixEnd_720560 := by exact prefixLift 720560
  have htrace : WordTrace (prefixWord ++ tailWord_720560) baseStart_720560 baseEnd_720560 := by
    simpa [prefixWord, tailWord_720560, baseEnd_720560] using wordTrace_append hprefix tailTrace_720560
  have hstable : (prefixWord ++ tailWord_720560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720560).length < 2 ^ (prefixWord ++ tailWord_720560).sum := by decide
  have hdescent : baseEnd_720560 < baseStart_720560 := by decide
  rcases family_descends (prefixWord ++ tailWord_720560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720598 : List Nat := [5, 2, 1, 3, 2, 1, 8]
def baseStart_720598 : Nat := 118140960795 + 720598 * 2 ^ 59
def prefixEnd_720598 : Nat := 4983230072969 + 3 ^ 40 * 720598 * 2
def baseEnd_720598 : Nat := 9136126732559923227433

theorem tailTrace_720598 : CollatzResearch.WordTrace tailWord_720598 prefixEnd_720598 9136126732559923227433 := by
  unfold tailWord_720598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1642648015212749324096153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17521578828935992790358965 1642648015212749324096153)
  ·
    refine ⟨1231986011409561993072115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1642648015212749324096153 1231986011409561993072115)
    ·
      refine ⟨1847979017114342989608173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1231986011409561993072115 1847979017114342989608173)
      ·
        refine ⟨692992131417878621103065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1847979017114342989608173 692992131417878621103065)
        ·
          refine ⟨519744098563408965827299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692992131417878621103065 519744098563408965827299)
          ·
            refine ⟨779616147845113448740949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519744098563408965827299 779616147845113448740949)
            ·
              refine ⟨9136126732559923227433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 779616147845113448740949 9136126732559923227433)
              ·
                rfl

theorem cell22_720598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 8].length) (baseStart_720598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720598 prefixEnd_720598 := by exact prefixLift 720598
  have htrace : WordTrace (prefixWord ++ tailWord_720598) baseStart_720598 baseEnd_720598 := by
    simpa [prefixWord, tailWord_720598, baseEnd_720598] using wordTrace_append hprefix tailTrace_720598
  have hstable : (prefixWord ++ tailWord_720598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720598).length < 2 ^ (prefixWord ++ tailWord_720598).sum := by decide
  have hdescent : baseEnd_720598 < baseStart_720598 := by decide
  rcases family_descends (prefixWord ++ tailWord_720598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720613 : List Nat := [1, 3, 1, 4, 1, 1, 5, 2, 1, 3]
def baseStart_720613 : Nat := 118140960795 + 720613 * 2 ^ 59
def prefixEnd_720613 : Nat := 4983230072969 + 3 ^ 40 * 720613 * 2
def baseEnd_720613 : Nat := 246680556585662888015645

theorem tailTrace_720613 : CollatzResearch.WordTrace tailWord_720613 prefixEnd_720613 246680556585662888015645 := by
  unfold tailWord_720613
  simp only [CollatzResearch.WordTrace]
  refine ⟨26282915338349646747334493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17521943558899764498222995 26282915338349646747334493)
  ·
    refine ⟨9856093251881117530250435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26282915338349646747334493 9856093251881117530250435)
    ·
      refine ⟨14784139877821676295375653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9856093251881117530250435 14784139877821676295375653)
      ·
        refine ⟨2772026227091564305382935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14784139877821676295375653 2772026227091564305382935)
        ·
          refine ⟨4158039340637346458074403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772026227091564305382935 4158039340637346458074403)
          ·
            refine ⟨6237059010956019687111605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158039340637346458074403 6237059010956019687111605)
            ·
              refine ⟨584724282277126845666713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6237059010956019687111605 584724282277126845666713)
              ·
                refine ⟨438543211707845134250035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584724282277126845666713 438543211707845134250035)
                ·
                  refine ⟨657814817561767701375053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438543211707845134250035 657814817561767701375053)
                  ·
                    refine ⟨246680556585662888015645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 657814817561767701375053 246680556585662888015645)
                    ·
                      rfl

theorem cell22_720613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_720613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720613 prefixEnd_720613 := by exact prefixLift 720613
  have htrace : WordTrace (prefixWord ++ tailWord_720613) baseStart_720613 baseEnd_720613 := by
    simpa [prefixWord, tailWord_720613, baseEnd_720613] using wordTrace_append hprefix tailTrace_720613
  have hstable : (prefixWord ++ tailWord_720613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720613).length < 2 ^ (prefixWord ++ tailWord_720613).sum := by decide
  have hdescent : baseEnd_720613 < baseStart_720613 := by decide
  rcases family_descends (prefixWord ++ tailWord_720613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720639 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 1, 4]
def baseStart_720639 : Nat := 118140960795 + 720639 * 2 ^ 59
def prefixEnd_720639 : Nat := 4983230072969 + 3 ^ 40 * 720639 * 2
def baseEnd_720639 : Nat := 246689456917007486865565

theorem tailTrace_720639 : CollatzResearch.WordTrace tailWord_720639 prefixEnd_720639 246689456917007486865565 := by
  unfold tailWord_720639
  simp only [CollatzResearch.WordTrace]
  refine ⟨26283863636255453187780971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17522575757503635458520647 26283863636255453187780971)
  ·
    refine ⟨39425795454383179781671457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26283863636255453187780971 39425795454383179781671457)
    ·
      refine ⟨29569346590787384836253593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39425795454383179781671457 29569346590787384836253593)
      ·
        refine ⟨22177009943090538627190195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29569346590787384836253593 22177009943090538627190195)
        ·
          refine ⟨33265514914635807940785293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22177009943090538627190195 33265514914635807940785293)
          ·
            refine ⟨12474568092988427977794485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33265514914635807940785293 12474568092988427977794485)
            ·
              refine ⟨1169490758717665122918233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12474568092988427977794485 1169490758717665122918233)
              ·
                refine ⟨877118069038248842188675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169490758717665122918233 877118069038248842188675)
                ·
                  refine ⟨1315677103557373263283013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 877118069038248842188675 1315677103557373263283013)
                  ·
                    refine ⟨246689456917007486865565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1315677103557373263283013 246689456917007486865565)
                    ·
                      rfl

theorem cell22_720639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_720639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720639 prefixEnd_720639 := by exact prefixLift 720639
  have htrace : WordTrace (prefixWord ++ tailWord_720639) baseStart_720639 baseEnd_720639 := by
    simpa [prefixWord, tailWord_720639, baseEnd_720639] using wordTrace_append hprefix tailTrace_720639
  have hstable : (prefixWord ++ tailWord_720639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720639).length < 2 ^ (prefixWord ++ tailWord_720639).sum := by decide
  have hdescent : baseEnd_720639 < baseStart_720639 := by decide
  rcases family_descends (prefixWord ++ tailWord_720639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720652 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 3, 5]
def baseStart_720652 : Nat := 118140960795 + 720652 * 2 ^ 59
def prefixEnd_720652 : Nat := 4983230072969 + 3 ^ 40 * 720652 * 2
def baseEnd_720652 : Nat := 246693907082679786290525

theorem tailTrace_720652 : CollatzResearch.WordTrace tailWord_720652 prefixEnd_720652 246693907082679786290525 := by
  unfold tailWord_720652
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142168892604178204002105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17522891856805570938669473 13142168892604178204002105)
  ·
    refine ⟨9856626669453133653001579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13142168892604178204002105 9856626669453133653001579)
    ·
      refine ⟨14784940004179700479502369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9856626669453133653001579 14784940004179700479502369)
      ·
        refine ⟨11088705003134775359626777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14784940004179700479502369 11088705003134775359626777)
        ·
          refine ⟨8316528752351081519720083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11088705003134775359626777 8316528752351081519720083)
          ·
            refine ⟨12474793128526622279580125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8316528752351081519720083 12474793128526622279580125)
            ·
              refine ⟨4678047423197483354842547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12474793128526622279580125 4678047423197483354842547)
              ·
                refine ⟨7017071134796225032263821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678047423197483354842547 7017071134796225032263821)
                ·
                  refine ⟨2631401675548584387098933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7017071134796225032263821 2631401675548584387098933)
                  ·
                    refine ⟨246693907082679786290525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2631401675548584387098933 246693907082679786290525)
                    ·
                      rfl

theorem cell22_720652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_720652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720652 prefixEnd_720652 := by exact prefixLift 720652
  have htrace : WordTrace (prefixWord ++ tailWord_720652) baseStart_720652 baseEnd_720652 := by
    simpa [prefixWord, tailWord_720652, baseEnd_720652] using wordTrace_append hprefix tailTrace_720652
  have hstable : (prefixWord ++ tailWord_720652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720652).length < 2 ^ (prefixWord ++ tailWord_720652).sum := by decide
  have hdescent : baseEnd_720652 < baseStart_720652 := by decide
  rcases family_descends (prefixWord ++ tailWord_720652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720660 : List Nat := [2, 4, 4, 1, 1, 1, 2, 2, 5]
def baseStart_720660 : Nat := 118140960795 + 720660 * 2 ^ 59
def prefixEnd_720660 : Nat := 4983230072969 + 3 ^ 40 * 720660 * 2
def baseEnd_720660 : Nat := 82232215215390144030167

theorem tailTrace_720660 : CollatzResearch.WordTrace tailWord_720660 prefixEnd_720660 82232215215390144030167 := by
  unfold tailWord_720660
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142314784589686887147717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17523086379452915849530289 13142314784589686887147717)
  ·
    refine ⟨2464184022110566291340197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13142314784589686887147717 2464184022110566291340197)
    ·
      refine ⟨462034504145731179626287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2464184022110566291340197 462034504145731179626287)
      ·
        refine ⟨693051756218596769439431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462034504145731179626287 693051756218596769439431)
        ·
          refine ⟨1039577634327895154159147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693051756218596769439431 1039577634327895154159147)
          ·
            refine ⟨1559366451491842731238721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039577634327895154159147 1559366451491842731238721)
            ·
              refine ⟨1169524838618882048429041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559366451491842731238721 1169524838618882048429041)
              ·
                refine ⟨877143628964161536321781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169524838618882048429041 877143628964161536321781)
                ·
                  refine ⟨82232215215390144030167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 877143628964161536321781 82232215215390144030167)
                  ·
                    rfl

theorem cell22_720660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_720660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720660 prefixEnd_720660 := by exact prefixLift 720660
  have htrace : WordTrace (prefixWord ++ tailWord_720660) baseStart_720660 baseEnd_720660 := by
    simpa [prefixWord, tailWord_720660, baseEnd_720660] using wordTrace_append hprefix tailTrace_720660
  have hstable : (prefixWord ++ tailWord_720660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720660).length < 2 ^ (prefixWord ++ tailWord_720660).sum := by decide
  have hdescent : baseEnd_720660 < baseStart_720660 := by decide
  rcases family_descends (prefixWord ++ tailWord_720660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720701 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_720701 : Nat := 118140960795 + 720701 * 2 ^ 59
def prefixEnd_720701 : Nat := 4983230072969 + 3 ^ 40 * 720701 * 2
def baseEnd_720701 : Nat := 246710680784059991815375

theorem tailTrace_720701 : CollatzResearch.WordTrace tailWord_720701 prefixEnd_720701 246710680784059991815375 := by
  unfold tailWord_720701
  simp only [CollatzResearch.WordTrace]
  refine ⟨26286124962030837776537957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17524083308020558517691971 26286124962030837776537957)
  ·
    refine ⟨4928648430380782083100867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26286124962030837776537957 4928648430380782083100867)
    ·
      refine ⟨7392972645571173124651301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4928648430380782083100867 7392972645571173124651301)
      ·
        refine ⟨1386182371044594960872119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7392972645571173124651301 1386182371044594960872119)
        ·
          refine ⟨2079273556566892441308179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386182371044594960872119 2079273556566892441308179)
          ·
            refine ⟨3118910334850338661962269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2079273556566892441308179 3118910334850338661962269)
            ·
              refine ⟨1169591375568876998235851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3118910334850338661962269 1169591375568876998235851)
              ·
                refine ⟨1754387063353315497353777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169591375568876998235851 1754387063353315497353777)
                ·
                  refine ⟨1315790297514986623015333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1754387063353315497353777 1315790297514986623015333)
                  ·
                    refine ⟨246710680784059991815375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1315790297514986623015333 246710680784059991815375)
                    ·
                      rfl

theorem cell22_720701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_720701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720701 prefixEnd_720701 := by exact prefixLift 720701
  have htrace : WordTrace (prefixWord ++ tailWord_720701) baseStart_720701 baseEnd_720701 := by
    simpa [prefixWord, tailWord_720701, baseEnd_720701] using wordTrace_append hprefix tailTrace_720701
  have hstable : (prefixWord ++ tailWord_720701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720701).length < 2 ^ (prefixWord ++ tailWord_720701).sum := by decide
  have hdescent : baseEnd_720701 < baseStart_720701 := by decide
  rcases family_descends (prefixWord ++ tailWord_720701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720714 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 5, 3]
def baseStart_720714 : Nat := 118140960795 + 720714 * 2 ^ 59
def prefixEnd_720714 : Nat := 4983230072969 + 3 ^ 40 * 720714 * 2
def baseEnd_720714 : Nat := 246715130949732291240335

theorem tailTrace_720714 : CollatzResearch.WordTrace tailWord_720714 prefixEnd_720714 246715130949732291240335 := by
  unfold tailWord_720714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571649777745935249190299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17524399407322493997840797 6571649777745935249190299)
  ·
    refine ⟨9857474666618902873785449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6571649777745935249190299 9857474666618902873785449)
    ·
      refine ⟨7393105999964177155339087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9857474666618902873785449 7393105999964177155339087)
      ·
        refine ⟨11089658999946265733008631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7393105999964177155339087 11089658999946265733008631)
        ·
          refine ⟨16634488499919398599512947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11089658999946265733008631 16634488499919398599512947)
          ·
            refine ⟨24951732749879097899269421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16634488499919398599512947 24951732749879097899269421)
            ·
              refine ⟨9356899781204661712226033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24951732749879097899269421 9356899781204661712226033)
              ·
                refine ⟨7017674835903496284169525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9356899781204661712226033 7017674835903496284169525)
                ·
                  refine ⟨657907015865952776640893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7017674835903496284169525 657907015865952776640893)
                  ·
                    refine ⟨246715130949732291240335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 657907015865952776640893 246715130949732291240335)
                    ·
                      rfl

theorem cell22_720714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_720714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720714 prefixEnd_720714 := by exact prefixLift 720714
  have htrace : WordTrace (prefixWord ++ tailWord_720714) baseStart_720714 baseEnd_720714 := by
    simpa [prefixWord, tailWord_720714, baseEnd_720714] using wordTrace_append hprefix tailTrace_720714
  have hstable : (prefixWord ++ tailWord_720714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720714).length < 2 ^ (prefixWord ++ tailWord_720714).sum := by decide
  have hdescent : baseEnd_720714 < baseStart_720714 := by decide
  rcases family_descends (prefixWord ++ tailWord_720714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720782 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_720782 : Nat := 118140960795 + 720782 * 2 ^ 59
def prefixEnd_720782 : Nat := 4983230072969 + 3 ^ 40 * 720782 * 2
def baseEnd_720782 : Nat := 246738408739402780540127

theorem tailTrace_720782 : CollatzResearch.WordTrace tailWord_720782 prefixEnd_720782 246738408739402780540127 := by
  unfold tailWord_720782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286134909342173576279575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17526052849824925740157733 3286134909342173576279575)
  ·
    refine ⟨4929202364013260364419363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3286134909342173576279575 4929202364013260364419363)
    ·
      refine ⟨7393803546019890546629045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4929202364013260364419363 7393803546019890546629045)
      ·
        refine ⟨693169082439364738746473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7393803546019890546629045 693169082439364738746473)
        ·
          refine ⟨519876811829523554059855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 693169082439364738746473 519876811829523554059855)
          ·
            refine ⟨779815217744285331089783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519876811829523554059855 779815217744285331089783)
            ·
              refine ⟨1169722826616427996634675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779815217744285331089783 1169722826616427996634675)
              ·
                refine ⟨1754584239924641994952013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1169722826616427996634675 1754584239924641994952013)
                ·
                  refine ⟨657969089971740748107005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1754584239924641994952013 657969089971740748107005)
                  ·
                    refine ⟨246738408739402780540127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 657969089971740748107005 246738408739402780540127)
                    ·
                      rfl

theorem cell22_720782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_720782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720782 prefixEnd_720782 := by exact prefixLift 720782
  have htrace : WordTrace (prefixWord ++ tailWord_720782) baseStart_720782 baseEnd_720782 := by
    simpa [prefixWord, tailWord_720782, baseEnd_720782] using wordTrace_append hprefix tailTrace_720782
  have hstable : (prefixWord ++ tailWord_720782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720782).length < 2 ^ (prefixWord ++ tailWord_720782).sum := by decide
  have hdescent : baseEnd_720782 < baseStart_720782 := by decide
  rcases family_descends (prefixWord ++ tailWord_720782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720821 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_720821 : Nat := 118140960795 + 720821 * 2 ^ 59
def prefixEnd_720821 : Nat := 4983230072969 + 3 ^ 40 * 720821 * 2
def baseEnd_720821 : Nat := 246751759236419678815007

theorem tailTrace_720821 : CollatzResearch.WordTrace tailWord_720821 prefixEnd_720821 246751759236419678815007 := by
  unfold tailWord_720821
  simp only [CollatzResearch.WordTrace]
  refine ⟨26290501721596098270906317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17527001147730732180604211 26290501721596098270906317)
  ·
    refine ⟨9858938145598536851589869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26290501721596098270906317 9858938145598536851589869)
    ·
      refine ⟨3697101804599451319346201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9858938145598536851589869 3697101804599451319346201)
      ·
        refine ⟨2772826353449588489509651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3697101804599451319346201 2772826353449588489509651)
        ·
          refine ⟨4159239530174382734264477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772826353449588489509651 4159239530174382734264477)
          ·
            refine ⟨1559714823815393525349179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4159239530174382734264477 1559714823815393525349179)
            ·
              refine ⟨2339572235723090288023769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559714823815393525349179 2339572235723090288023769)
              ·
                refine ⟨1754679176792317716017827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339572235723090288023769 1754679176792317716017827)
                ·
                  refine ⟨2632018765188476574026741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754679176792317716017827 2632018765188476574026741)
                  ·
                    refine ⟨246751759236419678815007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2632018765188476574026741 246751759236419678815007)
                    ·
                      rfl

theorem cell22_720821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_720821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720821 prefixEnd_720821 := by exact prefixLift 720821
  have htrace : WordTrace (prefixWord ++ tailWord_720821) baseStart_720821 baseEnd_720821 := by
    simpa [prefixWord, tailWord_720821, baseEnd_720821] using wordTrace_append hprefix tailTrace_720821
  have hstable : (prefixWord ++ tailWord_720821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720821).length < 2 ^ (prefixWord ++ tailWord_720821).sum := by decide
  have hdescent : baseEnd_720821 < baseStart_720821 := by decide
  rcases family_descends (prefixWord ++ tailWord_720821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720840 : List Nat := [2, 1, 3, 1, 4, 3, 2, 2, 4]
def baseStart_720840 : Nat := 118140960795 + 720840 * 2 ^ 59
def prefixEnd_720840 : Nat := 4983230072969 + 3 ^ 40 * 720840 * 2
def baseEnd_720840 : Nat := 82252754441569987529983

theorem tailTrace_720840 : CollatzResearch.WordTrace tailWord_720840 prefixEnd_720840 82252754441569987529983 := by
  unfold tailWord_720840
  simp only [CollatzResearch.WordTrace]
  refine ⟨13145597354263632257923987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17527463139018176343898649 13145597354263632257923987)
  ·
    refine ⟨19718396031395448386885981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13145597354263632257923987 19718396031395448386885981)
    ·
      refine ⟨7394398511773293145082243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19718396031395448386885981 7394398511773293145082243)
      ·
        refine ⟨11091597767659939717623365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7394398511773293145082243 11091597767659939717623365)
        ·
          refine ⟨2079674581436238697054381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11091597767659939717623365 2079674581436238697054381)
          ·
            refine ⟨779877968038589511395393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2079674581436238697054381 779877968038589511395393)
            ·
              refine ⟨584908476028942133546545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779877968038589511395393 584908476028942133546545)
              ·
                refine ⟨438681357021706600159909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584908476028942133546545 438681357021706600159909)
                ·
                  refine ⟨82252754441569987529983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 438681357021706600159909 82252754441569987529983)
                  ·
                    rfl

theorem cell22_720840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 4].length) (baseStart_720840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720840 prefixEnd_720840 := by exact prefixLift 720840
  have htrace : WordTrace (prefixWord ++ tailWord_720840) baseStart_720840 baseEnd_720840 := by
    simpa [prefixWord, tailWord_720840, baseEnd_720840] using wordTrace_append hprefix tailTrace_720840
  have hstable : (prefixWord ++ tailWord_720840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720840).length < 2 ^ (prefixWord ++ tailWord_720840).sum := by decide
  have hdescent : baseEnd_720840 < baseStart_720840 := by decide
  rcases family_descends (prefixWord ++ tailWord_720840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720879 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 7]
def baseStart_720879 : Nat := 118140960795 + 720879 * 2 ^ 59
def prefixEnd_720879 : Nat := 4983230072969 + 3 ^ 40 * 720879 * 2
def baseEnd_720879 : Nat := 82257204607242286954943

theorem tailTrace_720879 : CollatzResearch.WordTrace tailWord_720879 prefixEnd_720879 82257204607242286954943 := by
  unfold tailWord_720879
  simp only [CollatzResearch.WordTrace]
  refine ⟨26292617155385974176517691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17528411436923982784345127 26292617155385974176517691)
  ·
    refine ⟨39438925733078961264776537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26292617155385974176517691 39438925733078961264776537)
    ·
      refine ⟨29579194299809220948582403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39438925733078961264776537 29579194299809220948582403)
      ·
        refine ⟨44368791449713831422873605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29579194299809220948582403 44368791449713831422873605)
        ·
          refine ⟨8319148396821343391788801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44368791449713831422873605 8319148396821343391788801)
          ·
            refine ⟨6239361297616007543841601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8319148396821343391788801 6239361297616007543841601)
            ·
              refine ⟨4679520973212005657881201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6239361297616007543841601 4679520973212005657881201)
              ·
                refine ⟨3509640729909004243410901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4679520973212005657881201 3509640729909004243410901)
                ·
                  refine ⟨82257204607242286954943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3509640729909004243410901 82257204607242286954943)
                  ·
                    rfl

theorem cell22_720879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 7].length) (baseStart_720879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720879 prefixEnd_720879 := by exact prefixLift 720879
  have htrace : WordTrace (prefixWord ++ tailWord_720879) baseStart_720879 baseEnd_720879 := by
    simpa [prefixWord, tailWord_720879, baseEnd_720879] using wordTrace_append hprefix tailTrace_720879
  have hstable : (prefixWord ++ tailWord_720879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720879).length < 2 ^ (prefixWord ++ tailWord_720879).sum := by decide
  have hdescent : baseEnd_720879 < baseStart_720879 := by decide
  rcases family_descends (prefixWord ++ tailWord_720879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720973 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_720973 : Nat := 118140960795 + 720973 * 2 ^ 59
def prefixEnd_720973 : Nat := 4983230072969 + 3 ^ 40 * 720973 * 2
def baseEnd_720973 : Nat := 246803791942741949014541

theorem tailTrace_720973 : CollatzResearch.WordTrace tailWord_720973 prefixEnd_720973 246803791942741949014541 := by
  unfold tailWord_720973
  simp only [CollatzResearch.WordTrace]
  refine ⟨26296045617045428230439573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17530697078030285486959715 26296045617045428230439573)
  ·
    refine ⟨1232627138299004448301855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26296045617045428230439573 1232627138299004448301855)
    ·
      refine ⟨1848940707448506672452783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1232627138299004448301855 1848940707448506672452783)
      ·
        refine ⟨2773411061172760008679175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848940707448506672452783 2773411061172760008679175)
        ·
          refine ⟨4160116591759140013018763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773411061172760008679175 4160116591759140013018763)
          ·
            refine ⟨6240174887638710019528145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160116591759140013018763 6240174887638710019528145)
            ·
              refine ⟨4680131165729032514646109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6240174887638710019528145 4680131165729032514646109)
              ·
                refine ⟨1755049187148387192992291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4680131165729032514646109 1755049187148387192992291)
                ·
                  refine ⟨2632573780722580789488437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755049187148387192992291 2632573780722580789488437)
                  ·
                    refine ⟨246803791942741949014541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2632573780722580789488437 246803791942741949014541)
                    ·
                      rfl

theorem cell22_720973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_720973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720973 prefixEnd_720973 := by exact prefixLift 720973
  have htrace : WordTrace (prefixWord ++ tailWord_720973) baseStart_720973 baseEnd_720973 := by
    simpa [prefixWord, tailWord_720973, baseEnd_720973] using wordTrace_append hprefix tailTrace_720973
  have hstable : (prefixWord ++ tailWord_720973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720973).length < 2 ^ (prefixWord ++ tailWord_720973).sum := by decide
  have hdescent : baseEnd_720973 < baseStart_720973 := by decide
  rcases family_descends (prefixWord ++ tailWord_720973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_720988 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_720988 : Nat := 118140960795 + 720988 * 2 ^ 59
def prefixEnd_720988 : Nat := 4983230072969 + 3 ^ 40 * 720988 * 2
def baseEnd_720988 : Nat := 246808926749286909889495

theorem tailTrace_720988 : CollatzResearch.WordTrace tailWord_720988 prefixEnd_720988 246808926749286909889495 := by
  unfold tailWord_720988
  simp only [CollatzResearch.WordTrace]
  refine ⟨13148296355995542896117809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17531061807994057194823745 13148296355995542896117809)
  ·
    refine ⟨9861222266996657172088357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13148296355995542896117809 9861222266996657172088357)
    ·
      refine ⟨1848979175061873219766567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9861222266996657172088357 1848979175061873219766567)
      ·
        refine ⟨2773468762592809829649851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848979175061873219766567 2773468762592809829649851)
        ·
          refine ⟨4160203143889214744474777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773468762592809829649851 4160203143889214744474777)
          ·
            refine ⟨3120152357916911058356083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4160203143889214744474777 3120152357916911058356083)
            ·
              refine ⟨4680228536875366587534125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120152357916911058356083 4680228536875366587534125)
              ·
                refine ⟨1755085701328262470325297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4680228536875366587534125 1755085701328262470325297)
                ·
                  refine ⟨1316314275996196852743973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1755085701328262470325297 1316314275996196852743973)
                  ·
                    refine ⟨246808926749286909889495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1316314275996196852743973 246808926749286909889495)
                    ·
                      rfl

theorem cell22_720988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_720988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_720988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_720988 prefixEnd_720988 := by exact prefixLift 720988
  have htrace : WordTrace (prefixWord ++ tailWord_720988) baseStart_720988 baseEnd_720988 := by
    simpa [prefixWord, tailWord_720988, baseEnd_720988] using wordTrace_append hprefix tailTrace_720988
  have hstable : (prefixWord ++ tailWord_720988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_720988).length < 2 ^ (prefixWord ++ tailWord_720988).sum := by decide
  have hdescent : baseEnd_720988 < baseStart_720988 := by decide
  rcases family_descends (prefixWord ++ tailWord_720988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721052 : List Nat := [2, 2, 3, 2, 1, 1, 4, 3, 1, 3]
def baseStart_721052 : Nat := 118140960795 + 721052 * 2 ^ 59
def prefixEnd_721052 : Nat := 4983230072969 + 3 ^ 40 * 721052 * 2
def baseEnd_721052 : Nat := 246830835257212076289299

theorem tailTrace_721052 : CollatzResearch.WordTrace tailWord_721052 prefixEnd_721052 246830835257212076289299 := by
  unfold tailWord_721052
  simp only [CollatzResearch.WordTrace]
  refine ⟨13149463491879612361282705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17532617989172816481710273 13149463491879612361282705)
  ·
    refine ⟨9862097618909709270962029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13149463491879612361282705 9862097618909709270962029)
    ·
      refine ⟨3698286607091140976610761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9862097618909709270962029 3698286607091140976610761)
      ·
        refine ⟨2773714955318355732458071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3698286607091140976610761 2773714955318355732458071)
        ·
          refine ⟨4160572432977533598687107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773714955318355732458071 4160572432977533598687107)
          ·
            refine ⟨6240858649466300398030661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160572432977533598687107 6240858649466300398030661)
            ·
              refine ⟨1170160996774931324630749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6240858649466300398030661 1170160996774931324630749)
              ·
                refine ⟨438810373790599246736531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1170160996774931324630749 438810373790599246736531)
                ·
                  refine ⟨658215560685898870104797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438810373790599246736531 658215560685898870104797)
                  ·
                    refine ⟨246830835257212076289299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658215560685898870104797 246830835257212076289299)
                    ·
                      rfl

theorem cell22_721052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_721052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721052 prefixEnd_721052 := by exact prefixLift 721052
  have htrace : WordTrace (prefixWord ++ tailWord_721052) baseStart_721052 baseEnd_721052 := by
    simpa [prefixWord, tailWord_721052, baseEnd_721052] using wordTrace_append hprefix tailTrace_721052
  have hstable : (prefixWord ++ tailWord_721052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721052).length < 2 ^ (prefixWord ++ tailWord_721052).sum := by decide
  have hdescent : baseEnd_721052 < baseStart_721052 := by decide
  rcases family_descends (prefixWord ++ tailWord_721052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721125 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_721125 : Nat := 118140960795 + 721125 * 2 ^ 59
def prefixEnd_721125 : Nat := 4983230072969 + 3 ^ 40 * 721125 * 2
def baseEnd_721125 : Nat := 246855824649064219214075

theorem tailTrace_721125 : CollatzResearch.WordTrace tailWord_721125 prefixEnd_721125 246855824649064219214075 := by
  unfold tailWord_721125
  simp only [CollatzResearch.WordTrace]
  refine ⟨26301589512494758189972829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17534393008329838793315219 26301589512494758189972829)
  ·
    refine ⟨9863096067185534321239811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26301589512494758189972829 9863096067185534321239811)
    ·
      refine ⟨14794644100778301481859717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9863096067185534321239811 14794644100778301481859717)
      ·
        refine ⟨2773995768895931527848697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14794644100778301481859717 2773995768895931527848697)
        ·
          refine ⟨2080496826671948645886523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2773995768895931527848697 2080496826671948645886523)
          ·
            refine ⟨3120745240007922968829785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080496826671948645886523 3120745240007922968829785)
            ·
              refine ⟨2340558930005942226622339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120745240007922968829785 2340558930005942226622339)
              ·
                refine ⟨3510838395008913339933509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340558930005942226622339 3510838395008913339933509)
                ·
                  refine ⟨658282199064171251237533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3510838395008913339933509 658282199064171251237533)
                  ·
                    refine ⟨246855824649064219214075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658282199064171251237533 246855824649064219214075)
                    ·
                      rfl

theorem cell22_721125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_721125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721125 prefixEnd_721125 := by exact prefixLift 721125
  have htrace : WordTrace (prefixWord ++ tailWord_721125) baseStart_721125 baseEnd_721125 := by
    simpa [prefixWord, tailWord_721125, baseEnd_721125] using wordTrace_append hprefix tailTrace_721125
  have hstable : (prefixWord ++ tailWord_721125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721125).length < 2 ^ (prefixWord ++ tailWord_721125).sum := by decide
  have hdescent : baseEnd_721125 < baseStart_721125 := by decide
  rcases family_descends (prefixWord ++ tailWord_721125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721138 : List Nat := [3, 2, 1, 3, 2, 1, 1, 9]
def baseStart_721138 : Nat := 118140960795 + 721138 * 2 ^ 59
def prefixEnd_721138 : Nat := 4983230072969 + 3 ^ 40 * 721138 * 2
def baseEnd_721138 : Nat := 27428919423859613182115

theorem tailTrace_721138 : CollatzResearch.WordTrace tailWord_721138 prefixEnd_721138 27428919423859613182115 := by
  unfold tailWord_721138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6575515915361915352549017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17534709107631774273464045 6575515915361915352549017)
  ·
    refine ⟨4931636936521436514411763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6575515915361915352549017 4931636936521436514411763)
    ·
      refine ⟨7397455404782154771617645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4931636936521436514411763 7397455404782154771617645)
      ·
        refine ⟨2774045776793308039356617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7397455404782154771617645 2774045776793308039356617)
        ·
          refine ⟨2080534332594981029517463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2774045776793308039356617 2080534332594981029517463)
          ·
            refine ⟨3120801498892471544276195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080534332594981029517463 3120801498892471544276195)
            ·
              refine ⟨4681202248338707316414293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120801498892471544276195 4681202248338707316414293)
              ·
                refine ⟨27428919423859613182115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4681202248338707316414293 27428919423859613182115)
                ·
                  rfl

theorem cell22_721138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_721138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721138 prefixEnd_721138 := by exact prefixLift 721138
  have htrace : WordTrace (prefixWord ++ tailWord_721138) baseStart_721138 baseEnd_721138 := by
    simpa [prefixWord, tailWord_721138, baseEnd_721138] using wordTrace_append hprefix tailTrace_721138
  have hstable : (prefixWord ++ tailWord_721138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721138).length < 2 ^ (prefixWord ++ tailWord_721138).sum := by decide
  have hdescent : baseEnd_721138 < baseStart_721138 := by decide
  rcases family_descends (prefixWord ++ tailWord_721138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721187 : List Nat := [1, 1, 1, 4, 2, 2, 3, 4, 1, 3]
def baseStart_721187 : Nat := 118140960795 + 721187 * 2 ^ 59
def prefixEnd_721187 : Nat := 4983230072969 + 3 ^ 40 * 721187 * 2
def baseEnd_721187 : Nat := 246877048516116724163885

theorem tailTrace_721187 : CollatzResearch.WordTrace tailWord_721187 prefixEnd_721187 246877048516116724163885 := by
  unfold tailWord_721187
  simp only [CollatzResearch.WordTrace]
  refine ⟨26303850838270142778729815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17535900558846761852486543 26303850838270142778729815)
  ·
    refine ⟨39455776257405214168094723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26303850838270142778729815 39455776257405214168094723)
    ·
      refine ⟨59183664386107821252142085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39455776257405214168094723 59183664386107821252142085)
      ·
        refine ⟨11096937072395216484776641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59183664386107821252142085 11096937072395216484776641)
        ·
          refine ⟨8322702804296412363582481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11096937072395216484776641 8322702804296412363582481)
          ·
            refine ⟨6242027103222309272686861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8322702804296412363582481 6242027103222309272686861)
            ·
              refine ⟨2340760163708365977257573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6242027103222309272686861 2340760163708365977257573)
              ·
                refine ⟨438892530695318620735795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2340760163708365977257573 438892530695318620735795)
                ·
                  refine ⟨658338796042977931103693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438892530695318620735795 658338796042977931103693)
                  ·
                    refine ⟨246877048516116724163885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658338796042977931103693 246877048516116724163885)
                    ·
                      rfl

theorem cell22_721187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 3].length) (baseStart_721187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721187 prefixEnd_721187 := by exact prefixLift 721187
  have htrace : WordTrace (prefixWord ++ tailWord_721187) baseStart_721187 baseEnd_721187 := by
    simpa [prefixWord, tailWord_721187, baseEnd_721187] using wordTrace_append hprefix tailTrace_721187
  have hstable : (prefixWord ++ tailWord_721187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721187).length < 2 ^ (prefixWord ++ tailWord_721187).sum := by decide
  have hdescent : baseEnd_721187 < baseStart_721187 := by decide
  rcases family_descends (prefixWord ++ tailWord_721187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721228 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 8]
def baseStart_721228 : Nat := 118140960795 + 721228 * 2 ^ 59
def prefixEnd_721228 : Nat := 4983230072969 + 3 ^ 40 * 721228 * 2
def baseEnd_721228 : Nat := 82297027884668761296253

theorem tailTrace_721228 : CollatzResearch.WordTrace tailWord_721228 prefixEnd_721228 82297027884668761296253 := by
  unfold tailWord_721228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13152673115560803390486169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17536897487414404520648225 13152673115560803390486169)
  ·
    refine ⟨9864504836670602542864627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13152673115560803390486169 9864504836670602542864627)
    ·
      refine ⟨14796757255005903814296941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9864504836670602542864627 14796757255005903814296941)
      ·
        refine ⟨5548783970627213930361353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14796757255005903814296941 5548783970627213930361353)
        ·
          refine ⟨4161587977970410447771015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5548783970627213930361353 4161587977970410447771015)
          ·
            refine ⟨6242381966955615671656523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161587977970410447771015 6242381966955615671656523)
            ·
              refine ⟨9363572950433423507484785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6242381966955615671656523 9363572950433423507484785)
              ·
                refine ⟨7022679712825067630613589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9363572950433423507484785 7022679712825067630613589)
                ·
                  refine ⟨82297027884668761296253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7022679712825067630613589 82297027884668761296253)
                  ·
                    rfl

theorem cell22_721228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_721228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721228 prefixEnd_721228 := by exact prefixLift 721228
  have htrace : WordTrace (prefixWord ++ tailWord_721228) baseStart_721228 baseEnd_721228 := by
    simpa [prefixWord, tailWord_721228, baseEnd_721228] using wordTrace_append hprefix tailTrace_721228
  have hstable : (prefixWord ++ tailWord_721228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721228).length < 2 ^ (prefixWord ++ tailWord_721228).sum := by decide
  have hdescent : baseEnd_721228 < baseStart_721228 := by decide
  rcases family_descends (prefixWord ++ tailWord_721228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721352 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 5]
def baseStart_721352 : Nat := 118140960795 + 721352 * 2 ^ 59
def prefixEnd_721352 : Nat := 4983230072969 + 3 ^ 40 * 721352 * 2
def baseEnd_721352 : Nat := 82311177129370431262793

theorem tailTrace_721352 : CollatzResearch.WordTrace tailWord_721352 prefixEnd_721352 82311177129370431262793 := by
  unfold tailWord_721352
  simp only [CollatzResearch.WordTrace]
  refine ⟨13154934441336187979243155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17539912588448250638990873 13154934441336187979243155)
  ·
    refine ⟨19732401662004281968864733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13154934441336187979243155 19732401662004281968864733)
    ·
      refine ⟨7399650623251605738324275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19732401662004281968864733 7399650623251605738324275)
      ·
        refine ⟨11099475934877408607486413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7399650623251605738324275 11099475934877408607486413)
        ·
          refine ⟨4162303475579028227807405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11099475934877408607486413 4162303475579028227807405)
          ·
            refine ⟨1560863803342135585427777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4162303475579028227807405 1560863803342135585427777)
            ·
              refine ⟨1170647852506601689070833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560863803342135585427777 1170647852506601689070833)
              ·
                refine ⟨877985889379951266803125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170647852506601689070833 877985889379951266803125)
                ·
                  refine ⟨82311177129370431262793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 877985889379951266803125 82311177129370431262793)
                  ·
                    rfl

theorem cell22_721352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_721352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721352 prefixEnd_721352 := by exact prefixLift 721352
  have htrace : WordTrace (prefixWord ++ tailWord_721352) baseStart_721352 baseEnd_721352 := by
    simpa [prefixWord, tailWord_721352, baseEnd_721352] using wordTrace_append hprefix tailTrace_721352
  have hstable : (prefixWord ++ tailWord_721352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721352).length < 2 ^ (prefixWord ++ tailWord_721352).sum := by decide
  have hdescent : baseEnd_721352 < baseStart_721352 := by decide
  rcases family_descends (prefixWord ++ tailWord_721352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721356 : List Nat := [2, 2, 1, 4, 3, 1, 1, 4, 1, 3]
def baseStart_721356 : Nat := 118140960795 + 721356 * 2 ^ 59
def prefixEnd_721356 : Nat := 4983230072969 + 3 ^ 40 * 721356 * 2
def baseEnd_721356 : Nat := 246934900669856616688367

theorem tailTrace_721356 : CollatzResearch.WordTrace tailWord_721356 prefixEnd_721356 246934900669856616688367 := by
  unfold tailWord_721356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13155007387328942320815961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17540009849771923094421281 13155007387328942320815961)
  ·
    refine ⟨9866255540496706740611971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13155007387328942320815961 9866255540496706740611971)
    ·
      refine ⟨14799383310745060110917957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9866255540496706740611971 14799383310745060110917957)
      ·
        refine ⟨2774884370764698770797117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14799383310745060110917957 2774884370764698770797117)
        ·
          refine ⟨1040581639036762039048919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2774884370764698770797117 1040581639036762039048919)
          ·
            refine ⟨1560872458555143058573379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040581639036762039048919 1560872458555143058573379)
            ·
              refine ⟨2341308687832714587860069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1560872458555143058573379 2341308687832714587860069)
              ·
                refine ⟨438995378968633985223763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2341308687832714587860069 438995378968633985223763)
                ·
                  refine ⟨658493068452950977835645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438995378968633985223763 658493068452950977835645)
                  ·
                    refine ⟨246934900669856616688367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658493068452950977835645 246934900669856616688367)
                    ·
                      rfl

theorem cell22_721356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_721356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721356 prefixEnd_721356 := by exact prefixLift 721356
  have htrace : WordTrace (prefixWord ++ tailWord_721356) baseStart_721356 baseEnd_721356 := by
    simpa [prefixWord, tailWord_721356, baseEnd_721356] using wordTrace_append hprefix tailTrace_721356
  have hstable : (prefixWord ++ tailWord_721356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721356).length < 2 ^ (prefixWord ++ tailWord_721356).sum := by decide
  have hdescent : baseEnd_721356 < baseStart_721356 := by decide
  rcases family_descends (prefixWord ++ tailWord_721356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721395 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 1, 5]
def baseStart_721395 : Nat := 118140960795 + 721395 * 2 ^ 59
def prefixEnd_721395 : Nat := 4983230072969 + 3 ^ 40 * 721395 * 2
def baseEnd_721395 : Nat := 246948251166873514963247

theorem tailTrace_721395 : CollatzResearch.WordTrace tailWord_721395 prefixEnd_721395 246948251166873514963247 := by
  unfold tailWord_721395
  simp only [CollatzResearch.WordTrace]
  refine ⟨26311437221516594302301639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17540958147677729534867759 26311437221516594302301639)
  ·
    refine ⟨39467155832274891453452459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26311437221516594302301639 39467155832274891453452459)
    ·
      refine ⟨59200733748412337180178689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39467155832274891453452459 59200733748412337180178689)
      ·
        refine ⟨44400550311309252885134017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59200733748412337180178689 44400550311309252885134017)
        ·
          refine ⟨33300412733481939663850513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44400550311309252885134017 33300412733481939663850513)
          ·
            refine ⟨24975309550111454747887885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33300412733481939663850513 24975309550111454747887885)
            ·
              refine ⟨9365741081291795530457957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24975309550111454747887885 9365741081291795530457957)
              ·
                refine ⟨1756076452742211661960867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9365741081291795530457957 1756076452742211661960867)
                ·
                  refine ⟨2634114679113317492941301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756076452742211661960867 2634114679113317492941301)
                  ·
                    refine ⟨246948251166873514963247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2634114679113317492941301 246948251166873514963247)
                    ·
                      rfl

theorem cell22_721395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 5].length) (baseStart_721395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721395 prefixEnd_721395 := by exact prefixLift 721395
  have htrace : WordTrace (prefixWord ++ tailWord_721395) baseStart_721395 baseEnd_721395 := by
    simpa [prefixWord, tailWord_721395, baseEnd_721395] using wordTrace_append hprefix tailTrace_721395
  have hstable : (prefixWord ++ tailWord_721395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721395).length < 2 ^ (prefixWord ++ tailWord_721395).sum := by decide
  have hdescent : baseEnd_721395 < baseStart_721395 := by decide
  rcases family_descends (prefixWord ++ tailWord_721395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721457 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 5, 3]
def baseStart_721457 : Nat := 118140960795 + 721457 * 2 ^ 59
def prefixEnd_721457 : Nat := 4983230072969 + 3 ^ 40 * 721457 * 2
def baseEnd_721457 : Nat := 246969475033926019913057

theorem tailTrace_721457 : CollatzResearch.WordTrace tailWord_721457 prefixEnd_721457 246969475033926019913057 := by
  unfold tailWord_721457
  simp only [CollatzResearch.WordTrace]
  refine ⟨26313698547291978891058625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17542465698194652594039083 26313698547291978891058625)
  ·
    refine ⟨19735273910468984168293969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26313698547291978891058625 19735273910468984168293969)
    ·
      refine ⟨14801455432851738126220477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19735273910468984168293969 14801455432851738126220477)
      ·
        refine ⟨5550545787319401797332679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14801455432851738126220477 5550545787319401797332679)
        ·
          refine ⟨8325818680979102695999019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5550545787319401797332679 8325818680979102695999019)
          ·
            refine ⟨12488728021468654043998529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8325818680979102695999019 12488728021468654043998529)
            ·
              refine ⟨9366546016101490532998897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12488728021468654043998529 9366546016101490532998897)
              ·
                refine ⟨7024909512076117899749173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9366546016101490532998897 7024909512076117899749173)
                ·
                  refine ⟨658585266757136053101485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7024909512076117899749173 658585266757136053101485)
                  ·
                    refine ⟨246969475033926019913057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658585266757136053101485 246969475033926019913057)
                    ·
                      rfl

theorem cell22_721457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_721457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721457 prefixEnd_721457 := by exact prefixLift 721457
  have htrace : WordTrace (prefixWord ++ tailWord_721457) baseStart_721457 baseEnd_721457 := by
    simpa [prefixWord, tailWord_721457, baseEnd_721457] using wordTrace_append hprefix tailTrace_721457
  have hstable : (prefixWord ++ tailWord_721457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721457).length < 2 ^ (prefixWord ++ tailWord_721457).sum := by decide
  have hdescent : baseEnd_721457 < baseStart_721457 := by decide
  rcases family_descends (prefixWord ++ tailWord_721457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721515 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 10]
def baseStart_721515 : Nat := 118140960795 + 721515 * 2 ^ 59
def prefixEnd_721515 : Nat := 4983230072969 + 3 ^ 40 * 721515 * 2
def baseEnd_721515 : Nat := 82329776539744400654293

theorem tailTrace_721515 : CollatzResearch.WordTrace tailWord_721515 prefixEnd_721515 82329776539744400654293 := by
  unfold tailWord_721515
  simp only [CollatzResearch.WordTrace]
  refine ⟨26315813981081854796669999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17543875987387903197779999 26315813981081854796669999)
  ·
    refine ⟨39473720971622782195004999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26315813981081854796669999 39473720971622782195004999)
    ·
      refine ⟨59210581457434173292507499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39473720971622782195004999 59210581457434173292507499)
      ·
        refine ⟨88815872186151259938761249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59210581457434173292507499 88815872186151259938761249)
        ·
          refine ⟨66611904139613444954070937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88815872186151259938761249 66611904139613444954070937)
          ·
            refine ⟨49958928104710083715553203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66611904139613444954070937 49958928104710083715553203)
            ·
              refine ⟨74938392157065125573329805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49958928104710083715553203 74938392157065125573329805)
              ·
                refine ⟨28101897058899422089998677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74938392157065125573329805 28101897058899422089998677)
                ·
                  refine ⟨82329776539744400654293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 28101897058899422089998677 82329776539744400654293)
                  ·
                    rfl

theorem cell22_721515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 10].length) (baseStart_721515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721515 prefixEnd_721515 := by exact prefixLift 721515
  have htrace : WordTrace (prefixWord ++ tailWord_721515) baseStart_721515 baseEnd_721515 := by
    simpa [prefixWord, tailWord_721515, baseEnd_721515] using wordTrace_append hprefix tailTrace_721515
  have hstable : (prefixWord ++ tailWord_721515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721515).length < 2 ^ (prefixWord ++ tailWord_721515).sum := by decide
  have hdescent : baseEnd_721515 < baseStart_721515 := by decide
  rcases family_descends (prefixWord ++ tailWord_721515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721564 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_721564 : Nat := 118140960795 + 721564 * 2 ^ 59
def prefixEnd_721564 : Nat := 4983230072969 + 3 ^ 40 * 721564 * 2
def baseEnd_721564 : Nat := 247006103320613407487729

theorem tailTrace_721564 : CollatzResearch.WordTrace tailWord_721564 prefixEnd_721564 247006103320613407487729 := by
  unfold tailWord_721564
  simp only [CollatzResearch.WordTrace]
  refine ⟨13158800578952168082601873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17545067438602890776802497 13158800578952168082601873)
  ·
    refine ⟨9869100434214126061951405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13158800578952168082601873 9869100434214126061951405)
    ·
      refine ⟨3700912662830297273231777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9869100434214126061951405 3700912662830297273231777)
      ·
        refine ⟨2775684497122722954923833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3700912662830297273231777 2775684497122722954923833)
        ·
          refine ⟨2081763372842042216192875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2775684497122722954923833 2081763372842042216192875)
          ·
            refine ⟨3122645059263063324289313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081763372842042216192875 3122645059263063324289313)
            ·
              refine ⟨2341983794447297493216985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3122645059263063324289313 2341983794447297493216985)
              ·
                refine ⟨1756487845835473119912739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341983794447297493216985 1756487845835473119912739)
                ·
                  refine ⟨2634731768753209679869109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756487845835473119912739 2634731768753209679869109)
                  ·
                    refine ⟨247006103320613407487729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2634731768753209679869109 247006103320613407487729)
                    ·
                      rfl

theorem cell22_721564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_721564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721564 prefixEnd_721564 := by exact prefixLift 721564
  have htrace : WordTrace (prefixWord ++ tailWord_721564) baseStart_721564 baseEnd_721564 := by
    simpa [prefixWord, tailWord_721564, baseEnd_721564] using wordTrace_append hprefix tailTrace_721564
  have hstable : (prefixWord ++ tailWord_721564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721564).length < 2 ^ (prefixWord ++ tailWord_721564).sum := by decide
  have hdescent : baseEnd_721564 < baseStart_721564 := by decide
  rcases family_descends (prefixWord ++ tailWord_721564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721568 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 1, 4]
def baseStart_721568 : Nat := 118140960795 + 721568 * 2 ^ 59
def prefixEnd_721568 : Nat := 4983230072969 + 3 ^ 40 * 721568 * 2
def baseEnd_721568 : Nat := 247007472602358730387717

theorem tailTrace_721568 : CollatzResearch.WordTrace tailWord_721568 prefixEnd_721568 247007472602358730387717 := by
  unfold tailWord_721568
  simp only [CollatzResearch.WordTrace]
  refine ⟨13158873524944922424174679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17545164699926563232232905 13158873524944922424174679)
  ·
    refine ⟨19738310287417383636262019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13158873524944922424174679 19738310287417383636262019)
    ·
      refine ⟨29607465431126075454393029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19738310287417383636262019 29607465431126075454393029)
      ·
        refine ⟨5551399768336139147698693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29607465431126075454393029 5551399768336139147698693)
        ·
          refine ⟨1040887456563026090193505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5551399768336139147698693 1040887456563026090193505)
          ·
            refine ⟨780665592422269567645129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1040887456563026090193505 780665592422269567645129)
            ·
              refine ⟨585499194316702175733847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780665592422269567645129 585499194316702175733847)
              ·
                refine ⟨878248791475053263600771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585499194316702175733847 878248791475053263600771)
                ·
                  refine ⟨1317373187212579895401157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878248791475053263600771 1317373187212579895401157)
                  ·
                    refine ⟨247007472602358730387717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1317373187212579895401157 247007472602358730387717)
                    ·
                      rfl

theorem cell22_721568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 4].length) (baseStart_721568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721568 prefixEnd_721568 := by exact prefixLift 721568
  have htrace : WordTrace (prefixWord ++ tailWord_721568) baseStart_721568 baseEnd_721568 := by
    simpa [prefixWord, tailWord_721568, baseEnd_721568] using wordTrace_append hprefix tailTrace_721568
  have hstable : (prefixWord ++ tailWord_721568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721568).length < 2 ^ (prefixWord ++ tailWord_721568).sum := by decide
  have hdescent : baseEnd_721568 < baseStart_721568 := by decide
  rcases family_descends (prefixWord ++ tailWord_721568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721581 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_721581 : Nat := 118140960795 + 721581 * 2 ^ 59
def prefixEnd_721581 : Nat := 4983230072969 + 3 ^ 40 * 721581 * 2
def baseEnd_721581 : Nat := 247011922768031029812677

theorem tailTrace_721581 : CollatzResearch.WordTrace tailWord_721581 prefixEnd_721581 247011922768031029812677 := by
  unfold tailWord_721581
  simp only [CollatzResearch.WordTrace]
  refine ⟨26318221198842748068572597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17545480799228498712381731 26318221198842748068572597)
  ·
    refine ⟨2467333237391507631428681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26318221198842748068572597 2467333237391507631428681)
    ·
      refine ⟨1850499928043630723571511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2467333237391507631428681 1850499928043630723571511)
      ·
        refine ⟨2775749892065446085357267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1850499928043630723571511 2775749892065446085357267)
        ·
          refine ⟨4163624838098169128035901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775749892065446085357267 4163624838098169128035901)
          ·
            refine ⟨1561359314286813423013463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4163624838098169128035901 1561359314286813423013463)
            ·
              refine ⟨2342038971430220134520195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561359314286813423013463 2342038971430220134520195)
              ·
                refine ⟨3513058457145330201780293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342038971430220134520195 3513058457145330201780293)
                ·
                  refine ⟨658698460714749412833805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3513058457145330201780293 658698460714749412833805)
                  ·
                    refine ⟨247011922768031029812677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658698460714749412833805 247011922768031029812677)
                    ·
                      rfl

theorem cell22_721581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_721581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721581 prefixEnd_721581 := by exact prefixLift 721581
  have htrace : WordTrace (prefixWord ++ tailWord_721581) baseStart_721581 baseEnd_721581 := by
    simpa [prefixWord, tailWord_721581, baseEnd_721581] using wordTrace_append hprefix tailTrace_721581
  have hstable : (prefixWord ++ tailWord_721581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721581).length < 2 ^ (prefixWord ++ tailWord_721581).sum := by decide
  have hdescent : baseEnd_721581 < baseStart_721581 := by decide
  rcases family_descends (prefixWord ++ tailWord_721581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721598 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_721598 : Nat := 118140960795 + 721598 * 2 ^ 59
def prefixEnd_721598 : Nat := 4983230072969 + 3 ^ 40 * 721598 * 2
def baseEnd_721598 : Nat := 247017742215448652137625

theorem tailTrace_721598 : CollatzResearch.WordTrace tailWord_721598 prefixEnd_721598 247017742215448652137625 := by
  unfold tailWord_721598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3289855154972644996492681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17545894159854106647960965 3289855154972644996492681)
  ·
    refine ⟨2467391366229483747369511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3289855154972644996492681 2467391366229483747369511)
    ·
      refine ⟨3701087049344225621054267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467391366229483747369511 3701087049344225621054267)
      ·
        refine ⟨5551630574016338431581401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3701087049344225621054267 5551630574016338431581401)
        ·
          refine ⟨4163722930512253823686051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5551630574016338431581401 4163722930512253823686051)
          ·
            refine ⟨6245584395768380735529077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163722930512253823686051 6245584395768380735529077)
            ·
              refine ⟨585523537103285693955851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6245584395768380735529077 585523537103285693955851)
              ·
                refine ⟨878285305654928540933777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585523537103285693955851 878285305654928540933777)
                ·
                  refine ⟨658713979241196405700333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 878285305654928540933777 658713979241196405700333)
                  ·
                    refine ⟨247017742215448652137625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658713979241196405700333 247017742215448652137625)
                    ·
                      rfl

theorem cell22_721598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_721598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721598 prefixEnd_721598 := by exact prefixLift 721598
  have htrace : WordTrace (prefixWord ++ tailWord_721598) baseStart_721598 baseEnd_721598 := by
    simpa [prefixWord, tailWord_721598, baseEnd_721598] using wordTrace_append hprefix tailTrace_721598
  have hstable : (prefixWord ++ tailWord_721598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721598).length < 2 ^ (prefixWord ++ tailWord_721598).sum := by decide
  have hdescent : baseEnd_721598 < baseStart_721598 := by decide
  rcases family_descends (prefixWord ++ tailWord_721598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721654 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_721654 : Nat := 118140960795 + 721654 * 2 ^ 59
def prefixEnd_721654 : Nat := 4983230072969 + 3 ^ 40 * 721654 * 2
def baseEnd_721654 : Nat := 247036912159883172737453

theorem tailTrace_721654 : CollatzResearch.WordTrace tailWord_721654 prefixEnd_721654 247036912159883172737453 := by
  unfold tailWord_721654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1645055232973642595998751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17547255818385521023986677 1645055232973642595998751)
  ·
    refine ⟨2467582849460463893998127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1645055232973642595998751 2467582849460463893998127)
    ·
      refine ⟨3701374274190695840997191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467582849460463893998127 3701374274190695840997191)
      ·
        refine ⟨5552061411286043761495787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3701374274190695840997191 5552061411286043761495787)
        ·
          refine ⟨8328092116929065642243681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552061411286043761495787 8328092116929065642243681)
          ·
            refine ⟨6246069087696799231682761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328092116929065642243681 6246069087696799231682761)
            ·
              refine ⟨4684551815772599423762071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246069087696799231682761 4684551815772599423762071)
              ·
                refine ⟨7026827723658899135643107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684551815772599423762071 7026827723658899135643107)
                ·
                  refine ⟨10540241585488348703464661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7026827723658899135643107 10540241585488348703464661)
                  ·
                    refine ⟨247036912159883172737453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10540241585488348703464661 247036912159883172737453)
                    ·
                      rfl

theorem cell22_721654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_721654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721654 prefixEnd_721654 := by exact prefixLift 721654
  have htrace : WordTrace (prefixWord ++ tailWord_721654) baseStart_721654 baseEnd_721654 := by
    simpa [prefixWord, tailWord_721654, baseEnd_721654] using wordTrace_append hprefix tailTrace_721654
  have hstable : (prefixWord ++ tailWord_721654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721654).length < 2 ^ (prefixWord ++ tailWord_721654).sum := by decide
  have hdescent : baseEnd_721654 < baseStart_721654 := by decide
  rcases family_descends (prefixWord ++ tailWord_721654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721667 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 8]
def baseStart_721667 : Nat := 118140960795 + 721667 * 2 ^ 59
def prefixEnd_721667 : Nat := 4983230072969 + 3 ^ 40 * 721667 * 2
def baseEnd_721667 : Nat := 82347120775185157387471

theorem tailTrace_721667 : CollatzResearch.WordTrace tailWord_721667 prefixEnd_721667 82347120775185157387471 := by
  unfold tailWord_721667
  simp only [CollatzResearch.WordTrace]
  refine ⟨26321357876531184756203255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17547571917687456504135503 26321357876531184756203255)
  ·
    refine ⟨39482036814796777134304883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26321357876531184756203255 39482036814796777134304883)
    ·
      refine ⟨59223055222195165701457325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39482036814796777134304883 59223055222195165701457325)
      ·
        refine ⟨22208645708323187138046497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59223055222195165701457325 22208645708323187138046497)
        ·
          refine ⟨16656484281242390353534873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22208645708323187138046497 16656484281242390353534873)
          ·
            refine ⟨12492363210931792765151155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16656484281242390353534873 12492363210931792765151155)
            ·
              refine ⟨18738544816397689147726733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12492363210931792765151155 18738544816397689147726733)
              ·
                refine ⟨7026954306149133430397525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18738544816397689147726733 7026954306149133430397525)
                ·
                  refine ⟨82347120775185157387471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7026954306149133430397525 82347120775185157387471)
                  ·
                    rfl

theorem cell22_721667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 8].length) (baseStart_721667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721667 prefixEnd_721667 := by exact prefixLift 721667
  have htrace : WordTrace (prefixWord ++ tailWord_721667) baseStart_721667 baseEnd_721667 := by
    simpa [prefixWord, tailWord_721667, baseEnd_721667] using wordTrace_append hprefix tailTrace_721667
  have hstable : (prefixWord ++ tailWord_721667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721667).length < 2 ^ (prefixWord ++ tailWord_721667).sum := by decide
  have hdescent : baseEnd_721667 < baseStart_721667 := by decide
  rcases family_descends (prefixWord ++ tailWord_721667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721701 : List Nat := [1, 3, 1, 2, 3, 1, 3, 4, 4]
def baseStart_721701 : Nat := 118140960795 + 721701 * 2 ^ 59
def prefixEnd_721701 : Nat := 4983230072969 + 3 ^ 40 * 721701 * 2
def baseEnd_721701 : Nat := 82351000406796905604103

theorem tailTrace_721701 : CollatzResearch.WordTrace tailWord_721701 prefixEnd_721701 82351000406796905604103 := by
  unfold tailWord_721701
  simp only [CollatzResearch.WordTrace]
  refine ⟨26322597958408008562940957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17548398638938672375293971 26322597958408008562940957)
  ·
    refine ⟨9870974234403003211102859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26322597958408008562940957 9870974234403003211102859)
    ·
      refine ⟨14806461351604504816654289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9870974234403003211102859 14806461351604504816654289)
      ·
        refine ⟨11104846013703378612490717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14806461351604504816654289 11104846013703378612490717)
        ·
          refine ⟨4164317255138766979684019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11104846013703378612490717 4164317255138766979684019)
          ·
            refine ⟨6246475882708150469526029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164317255138766979684019 6246475882708150469526029)
            ·
              refine ⟨2342428456015556426072261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6246475882708150469526029 2342428456015556426072261)
              ·
                refine ⟨439205335502916829888549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2342428456015556426072261 439205335502916829888549)
                ·
                  refine ⟨82351000406796905604103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439205335502916829888549 82351000406796905604103)
                  ·
                    rfl

theorem cell22_721701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_721701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721701 prefixEnd_721701 := by exact prefixLift 721701
  have htrace : WordTrace (prefixWord ++ tailWord_721701) baseStart_721701 baseEnd_721701 := by
    simpa [prefixWord, tailWord_721701, baseEnd_721701] using wordTrace_append hprefix tailTrace_721701
  have hstable : (prefixWord ++ tailWord_721701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721701).length < 2 ^ (prefixWord ++ tailWord_721701).sum := by decide
  have hdescent : baseEnd_721701 < baseStart_721701 := by decide
  rcases family_descends (prefixWord ++ tailWord_721701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721714 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_721714 : Nat := 118140960795 + 721714 * 2 ^ 59
def prefixEnd_721714 : Nat := 4983230072969 + 3 ^ 40 * 721714 * 2
def baseEnd_721714 : Nat := 247057451386063016237269

theorem tailTrace_721714 : CollatzResearch.WordTrace tailWord_721714 prefixEnd_721714 247057451386063016237269 := by
  unfold tailWord_721714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6580768026840227945791049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17548714738240607855442797 6580768026840227945791049)
  ·
    refine ⟨4935576020130170959343287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6580768026840227945791049 4935576020130170959343287)
    ·
      refine ⟨7403364030195256439014931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4935576020130170959343287 7403364030195256439014931)
      ·
        refine ⟨11105046045292884658522397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7403364030195256439014931 11105046045292884658522397)
        ·
          refine ⟨4164392266984831746945899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11105046045292884658522397 4164392266984831746945899)
          ·
            refine ⟨6246588400477247620418849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164392266984831746945899 6246588400477247620418849)
            ·
              refine ⟨4684941300357935715314137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246588400477247620418849 4684941300357935715314137)
              ·
                refine ⟨3513705975268451786485603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4684941300357935715314137 3513705975268451786485603)
                ·
                  refine ⟨5270558962902677679728405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3513705975268451786485603 5270558962902677679728405)
                  ·
                    refine ⟨247057451386063016237269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5270558962902677679728405 247057451386063016237269)
                    ·
                      rfl

theorem cell22_721714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_721714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721714 prefixEnd_721714 := by exact prefixLift 721714
  have htrace : WordTrace (prefixWord ++ tailWord_721714) baseStart_721714 baseEnd_721714 := by
    simpa [prefixWord, tailWord_721714, baseEnd_721714] using wordTrace_append hprefix tailTrace_721714
  have hstable : (prefixWord ++ tailWord_721714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721714).length < 2 ^ (prefixWord ++ tailWord_721714).sum := by decide
  have hdescent : baseEnd_721714 < baseStart_721714 := by decide
  rcases family_descends (prefixWord ++ tailWord_721714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721718 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_721718 : Nat := 118140960795 + 721718 * 2 ^ 59
def prefixEnd_721718 : Nat := 4983230072969 + 3 ^ 40 * 721718 * 2
def baseEnd_721718 : Nat := 82352940222602779712419

theorem tailTrace_721718 : CollatzResearch.WordTrace tailWord_721718 prefixEnd_721718 82352940222602779712419 := by
  unfold tailWord_721718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1645201124959151279144363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17548811999564280310873205 1645201124959151279144363)
  ·
    refine ⟨2467801687438726918716545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1645201124959151279144363 2467801687438726918716545)
    ·
      refine ⟨1850851265579045189037409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2467801687438726918716545 1850851265579045189037409)
      ·
        refine ⟨1388138449184283891778057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1850851265579045189037409 1388138449184283891778057)
        ·
          refine ⟨1041103836888212918833543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388138449184283891778057 1041103836888212918833543)
          ·
            refine ⟨1561655755332319378250315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041103836888212918833543 1561655755332319378250315)
            ·
              refine ⟨2342483632998479067375473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1561655755332319378250315 2342483632998479067375473)
              ·
                refine ⟨1756862724748859300531605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342483632998479067375473 1756862724748859300531605)
                ·
                  refine ⟨82352940222602779712419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1756862724748859300531605 82352940222602779712419)
                  ·
                    rfl

theorem cell22_721718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_721718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721718 prefixEnd_721718 := by exact prefixLift 721718
  have htrace : WordTrace (prefixWord ++ tailWord_721718) baseStart_721718 baseEnd_721718 := by
    simpa [prefixWord, tailWord_721718, baseEnd_721718] using wordTrace_append hprefix tailTrace_721718
  have hstable : (prefixWord ++ tailWord_721718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721718).length < 2 ^ (prefixWord ++ tailWord_721718).sum := by decide
  have hdescent : baseEnd_721718 < baseStart_721718 := by decide
  rcases family_descends (prefixWord ++ tailWord_721718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721789 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_721789 : Nat := 118140960795 + 721789 * 2 ^ 59
def prefixEnd_721789 : Nat := 4983230072969 + 3 ^ 40 * 721789 * 2
def baseEnd_721789 : Nat := 247083125418787820612039

theorem tailTrace_721789 : CollatzResearch.WordTrace tailWord_721789 prefixEnd_721789 247083125418787820612039 := by
  unfold tailWord_721789
  simp only [CollatzResearch.WordTrace]
  refine ⟨26325807582089199592144421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17550538388059466394762947 26325807582089199592144421)
  ·
    refine ⟨4936088921641724923527079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26325807582089199592144421 4936088921641724923527079)
    ·
      refine ⟨7404133382462587385290619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4936088921641724923527079 7404133382462587385290619)
      ·
        refine ⟨11106200073693881077935929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7404133382462587385290619 11106200073693881077935929)
        ·
          refine ⟨8329650055270410808451947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11106200073693881077935929 8329650055270410808451947)
          ·
            refine ⟨12494475082905616212677921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8329650055270410808451947 12494475082905616212677921)
            ·
              refine ⟨9370856312179212159508441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12494475082905616212677921 9370856312179212159508441)
              ·
                refine ⟨7028142234134409119631331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9370856312179212159508441 7028142234134409119631331)
                ·
                  refine ⟨10542213351201613679446997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7028142234134409119631331 10542213351201613679446997)
                  ·
                    refine ⟨247083125418787820612039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10542213351201613679446997 247083125418787820612039)
                    ·
                      rfl

theorem cell22_721789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_721789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721789 prefixEnd_721789 := by exact prefixLift 721789
  have htrace : WordTrace (prefixWord ++ tailWord_721789) baseStart_721789 baseEnd_721789 := by
    simpa [prefixWord, tailWord_721789, baseEnd_721789] using wordTrace_append hprefix tailTrace_721789
  have hstable : (prefixWord ++ tailWord_721789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721789).length < 2 ^ (prefixWord ++ tailWord_721789).sum := by decide
  have hdescent : baseEnd_721789 < baseStart_721789 := by decide
  rcases family_descends (prefixWord ++ tailWord_721789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721812 : List Nat := [2, 4, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_721812 : Nat := 118140960795 + 721812 * 2 ^ 59
def prefixEnd_721812 : Nat := 4983230072969 + 3 ^ 40 * 721812 * 2
def baseEnd_721812 : Nat := 247090998788823427286969

theorem tailTrace_721812 : CollatzResearch.WordTrace tailWord_721812 prefixEnd_721812 247090998788823427286969 := by
  unfold tailWord_721812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13163323230502937260115845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17551097640670583013487793 13163323230502937260115845)
  ·
    refine ⟨2468123105719300736271721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13163323230502937260115845 2468123105719300736271721)
    ·
      refine ⟨1851092329289475552203791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2468123105719300736271721 1851092329289475552203791)
      ·
        refine ⟨2776638493934213328305687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1851092329289475552203791 2776638493934213328305687)
        ·
          refine ⟨4164957740901319992458531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2776638493934213328305687 4164957740901319992458531)
          ·
            refine ⟨6247436611351979988687797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164957740901319992458531 6247436611351979988687797)
            ·
              refine ⟨585697182314248123939481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6247436611351979988687797 585697182314248123939481)
              ·
                refine ⟨439272886735686092954611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585697182314248123939481 439272886735686092954611)
                ·
                  refine ⟨658909330103529139431917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439272886735686092954611 658909330103529139431917)
                  ·
                    refine ⟨247090998788823427286969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658909330103529139431917 247090998788823427286969)
                    ·
                      rfl

theorem cell22_721812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_721812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721812 prefixEnd_721812 := by exact prefixLift 721812
  have htrace : WordTrace (prefixWord ++ tailWord_721812) baseStart_721812 baseEnd_721812 := by
    simpa [prefixWord, tailWord_721812, baseEnd_721812] using wordTrace_append hprefix tailTrace_721812
  have hstable : (prefixWord ++ tailWord_721812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721812).length < 2 ^ (prefixWord ++ tailWord_721812).sum := by decide
  have hdescent : baseEnd_721812 < baseStart_721812 := by decide
  rcases family_descends (prefixWord ++ tailWord_721812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721821 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_721821 : Nat := 118140960795 + 721821 * 2 ^ 59
def prefixEnd_721821 : Nat := 4983230072969 + 3 ^ 40 * 721821 * 2
def baseEnd_721821 : Nat := 247094079672750403811941

theorem tailTrace_721821 : CollatzResearch.WordTrace tailWord_721821 prefixEnd_721821 247094079672750403811941 := by
  unfold tailWord_721821
  simp only [CollatzResearch.WordTrace]
  refine ⟨26326974717973269057309317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17551316478648846038206211 26326974717973269057309317)
  ·
    refine ⟨4936307759619987948245497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26326974717973269057309317 4936307759619987948245497)
    ·
      refine ⟨3702230819714990961184123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4936307759619987948245497 3702230819714990961184123)
      ·
        refine ⟨5553346229572486441776185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3702230819714990961184123 5553346229572486441776185)
        ·
          refine ⟨4165009672179364831332139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5553346229572486441776185 4165009672179364831332139)
          ·
            refine ⟨6247514508269047246998209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4165009672179364831332139 6247514508269047246998209)
            ·
              refine ⟨4685635881201785435248657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6247514508269047246998209 4685635881201785435248657)
              ·
                refine ⟨3514226910901339076436493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685635881201785435248657 3514226910901339076436493)
                ·
                  refine ⟨1317835091588002153663685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3514226910901339076436493 1317835091588002153663685)
                  ·
                    refine ⟨247094079672750403811941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1317835091588002153663685 247094079672750403811941)
                    ·
                      rfl

theorem cell22_721821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_721821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721821 prefixEnd_721821 := by exact prefixLift 721821
  have htrace : WordTrace (prefixWord ++ tailWord_721821) baseStart_721821 baseEnd_721821 := by
    simpa [prefixWord, tailWord_721821, baseEnd_721821] using wordTrace_append hprefix tailTrace_721821
  have hstable : (prefixWord ++ tailWord_721821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721821).length < 2 ^ (prefixWord ++ tailWord_721821).sum := by decide
  have hdescent : baseEnd_721821 < baseStart_721821 := by decide
  rcases family_descends (prefixWord ++ tailWord_721821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721825 : List Nat := [1, 2, 3, 4, 1, 3, 2, 1, 5]
def baseStart_721825 : Nat := 118140960795 + 721825 * 2 ^ 59
def prefixEnd_721825 : Nat := 4983230072969 + 3 ^ 40 * 721825 * 2
def baseEnd_721825 : Nat := 82365149651498575570643

theorem tailTrace_721825 : CollatzResearch.WordTrace tailWord_721825 prefixEnd_721825 82365149651498575570643 := by
  unfold tailWord_721825
  simp only [CollatzResearch.WordTrace]
  refine ⟨26327120609958777740454929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17551413739972518493636619 26327120609958777740454929)
  ·
    refine ⟨19745340457469083305341197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26327120609958777740454929 19745340457469083305341197)
    ·
      refine ⟨7404502671550906239502949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19745340457469083305341197 7404502671550906239502949)
      ·
        refine ⟨1388344250915794919906803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7404502671550906239502949 1388344250915794919906803)
        ·
          refine ⟨2082516376373692379860205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388344250915794919906803 2082516376373692379860205)
          ·
            refine ⟨780943641140134642447577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2082516376373692379860205 780943641140134642447577)
            ·
              refine ⟨585707730855100981835683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780943641140134642447577 585707730855100981835683)
              ·
                refine ⟨878561596282651472753525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585707730855100981835683 878561596282651472753525)
                ·
                  refine ⟨82365149651498575570643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 878561596282651472753525 82365149651498575570643)
                  ·
                    rfl

theorem cell22_721825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 5].length) (baseStart_721825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721825 prefixEnd_721825 := by exact prefixLift 721825
  have htrace : WordTrace (prefixWord ++ tailWord_721825) baseStart_721825 baseEnd_721825 := by
    simpa [prefixWord, tailWord_721825, baseEnd_721825] using wordTrace_append hprefix tailTrace_721825
  have hstable : (prefixWord ++ tailWord_721825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721825).length < 2 ^ (prefixWord ++ tailWord_721825).sum := by decide
  have hdescent : baseEnd_721825 < baseStart_721825 := by decide
  rcases family_descends (prefixWord ++ tailWord_721825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721864 : List Nat := [2, 1, 3, 1, 15]
def baseStart_721864 : Nat := 118140960795 + 721864 * 2 ^ 59
def prefixEnd_721864 : Nat := 4983230072969 + 3 ^ 40 * 721864 * 2
def baseEnd_721864 : Nat := 1016908639718158950563

theorem tailTrace_721864 : CollatzResearch.WordTrace tailWord_721864 prefixEnd_721864 1016908639718158950563 := by
  unfold tailWord_721864
  simp only [CollatzResearch.WordTrace]
  refine ⟨13164271528408743700562323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17552362037878324934083097 13164271528408743700562323)
  ·
    refine ⟨19746407292613115550843485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13164271528408743700562323 19746407292613115550843485)
    ·
      refine ⟨7404902734729918331566307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19746407292613115550843485 7404902734729918331566307)
      ·
        refine ⟨11107354102094877497349461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7404902734729918331566307 11107354102094877497349461)
        ·
          refine ⟨1016908639718158950563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 11107354102094877497349461 1016908639718158950563)
          ·
            rfl

theorem cell22_721864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 15].length) (baseStart_721864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721864 prefixEnd_721864 := by exact prefixLift 721864
  have htrace : WordTrace (prefixWord ++ tailWord_721864) baseStart_721864 baseEnd_721864 := by
    simpa [prefixWord, tailWord_721864, baseEnd_721864] using wordTrace_append hprefix tailTrace_721864
  have hstable : (prefixWord ++ tailWord_721864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721864).length < 2 ^ (prefixWord ++ tailWord_721864).sum := by decide
  have hdescent : baseEnd_721864 < baseStart_721864 := by decide
  rcases family_descends (prefixWord ++ tailWord_721864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721870 : List Nat := [4, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_721870 : Nat := 118140960795 + 721870 * 2 ^ 59
def prefixEnd_721870 : Nat := 4983230072969 + 3 ^ 40 * 721870 * 2
def baseEnd_721870 : Nat := 82370284458043536445597

theorem tailTrace_721870 : CollatzResearch.WordTrace tailWord_721870 prefixEnd_721870 82370284458043536445597 := by
  unfold tailWord_721870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3291095236849468803230383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17552507929863833617228709 3291095236849468803230383)
  ·
    refine ⟨4936642855274203204845575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3291095236849468803230383 4936642855274203204845575)
    ·
      refine ⟨7404964282911304807268363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4936642855274203204845575 7404964282911304807268363)
      ·
        refine ⟨11107446424366957210902545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7404964282911304807268363 11107446424366957210902545)
        ·
          refine ⟨8330584818275217908176909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11107446424366957210902545 8330584818275217908176909)
          ·
            refine ⟨3123969306853206715566341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8330584818275217908176909 3123969306853206715566341)
            ·
              refine ⟨585744245034976259168689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3123969306853206715566341 585744245034976259168689)
              ·
                refine ⟨439308183776232194376517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 585744245034976259168689 439308183776232194376517)
                ·
                  refine ⟨82370284458043536445597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439308183776232194376517 82370284458043536445597)
                  ·
                    rfl

theorem cell22_721870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_721870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721870 prefixEnd_721870 := by exact prefixLift 721870
  have htrace : WordTrace (prefixWord ++ tailWord_721870) baseStart_721870 baseEnd_721870 := by
    simpa [prefixWord, tailWord_721870, baseEnd_721870] using wordTrace_append hprefix tailTrace_721870
  have hstable : (prefixWord ++ tailWord_721870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721870).length < 2 ^ (prefixWord ++ tailWord_721870).sum := by decide
  have hdescent : baseEnd_721870 < baseStart_721870 := by decide
  rcases family_descends (prefixWord ++ tailWord_721870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721881 : List Nat := [1, 2, 1, 2, 5, 1, 3, 7]
def baseStart_721881 : Nat := 118140960795 + 721881 * 2 ^ 59
def prefixEnd_721881 : Nat := 4983230072969 + 3 ^ 40 * 721881 * 2
def baseEnd_721881 : Nat := 27457179877658916367973

theorem tailTrace_721881 : CollatzResearch.WordTrace tailWord_721881 prefixEnd_721881 27457179877658916367973 := by
  unfold tailWord_721881
  simp only [CollatzResearch.WordTrace]
  refine ⟨26329163097755899304493497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17552775398503932869662331 26329163097755899304493497)
  ·
    refine ⟨19746872323316924478370123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26329163097755899304493497 19746872323316924478370123)
    ·
      refine ⟨29620308484975386717555185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19746872323316924478370123 29620308484975386717555185)
      ·
        refine ⟨22215231363731540038166389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29620308484975386717555185 22215231363731540038166389)
        ·
          refine ⟨2082677940349831878578099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22215231363731540038166389 2082677940349831878578099)
          ·
            refine ⟨3124016910524747817867149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082677940349831878578099 3124016910524747817867149)
            ·
              refine ⟨1171506341446780431700181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3124016910524747817867149 1171506341446780431700181)
              ·
                refine ⟨27457179877658916367973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1171506341446780431700181 27457179877658916367973)
                ·
                  rfl

theorem cell22_721881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 7].length) (baseStart_721881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721881 prefixEnd_721881 := by exact prefixLift 721881
  have htrace : WordTrace (prefixWord ++ tailWord_721881) baseStart_721881 baseEnd_721881 := by
    simpa [prefixWord, tailWord_721881, baseEnd_721881] using wordTrace_append hprefix tailTrace_721881
  have hstable : (prefixWord ++ tailWord_721881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721881).length < 2 ^ (prefixWord ++ tailWord_721881).sum := by decide
  have hdescent : baseEnd_721881 < baseStart_721881 := by decide
  rcases family_descends (prefixWord ++ tailWord_721881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721885 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_721885 : Nat := 118140960795 + 721885 * 2 ^ 59
def prefixEnd_721885 : Nat := 4983230072969 + 3 ^ 40 * 721885 * 2
def baseEnd_721885 : Nat := 247115988180675570211745

theorem tailTrace_721885 : CollatzResearch.WordTrace tailWord_721885 prefixEnd_721885 247115988180675570211745 := by
  unfold tailWord_721885
  simp only [CollatzResearch.WordTrace]
  refine ⟨26329308989741407987639109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17552872659827605325092739 26329308989741407987639109)
  ·
    refine ⟨4936745435576513997682333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26329308989741407987639109 4936745435576513997682333)
    ·
      refine ⟨1851279538341192749130875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4936745435576513997682333 1851279538341192749130875)
      ·
        refine ⟨2776919307511789123696313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1851279538341192749130875 2776919307511789123696313)
        ·
          refine ⟨2082689480633841842772235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2776919307511789123696313 2082689480633841842772235)
          ·
            refine ⟨3124034220950762764158353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082689480633841842772235 3124034220950762764158353)
            ·
              refine ⟨2343025665713072073118765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3124034220950762764158353 2343025665713072073118765)
              ·
                refine ⟨878634624642402027419537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2343025665713072073118765 878634624642402027419537)
                ·
                  refine ⟨658975968481801520564653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 878634624642402027419537 658975968481801520564653)
                  ·
                    refine ⟨247115988180675570211745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658975968481801520564653 247115988180675570211745)
                    ·
                      rfl

theorem cell22_721885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_721885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721885 prefixEnd_721885 := by exact prefixLift 721885
  have htrace : WordTrace (prefixWord ++ tailWord_721885) baseStart_721885 baseEnd_721885 := by
    simpa [prefixWord, tailWord_721885, baseEnd_721885] using wordTrace_append hprefix tailTrace_721885
  have hstable : (prefixWord ++ tailWord_721885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721885).length < 2 ^ (prefixWord ++ tailWord_721885).sum := by decide
  have hdescent : baseEnd_721885 < baseStart_721885 := by decide
  rcases family_descends (prefixWord ++ tailWord_721885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721898 : List Nat := [3, 1, 3, 1, 2, 3, 3, 6]
def baseStart_721898 : Nat := 118140960795 + 721898 * 2 ^ 59
def prefixEnd_721898 : Nat := 4983230072969 + 3 ^ 40 * 721898 * 2
def baseEnd_721898 : Nat := 27457826482927541070745

theorem tailTrace_721898 : CollatzResearch.WordTrace tailWord_721898 prefixEnd_721898 27457826482927541070745 := by
  unfold tailWord_721898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582445784673577801965587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17553188759129540805241565 6582445784673577801965587)
  ·
    refine ⟨9873668677010366702948381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6582445784673577801965587 9873668677010366702948381)
    ·
      refine ⟨3702625753878887513605643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9873668677010366702948381 3702625753878887513605643)
      ·
        refine ⟨5553938630818331270408465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3702625753878887513605643 5553938630818331270408465)
        ·
          refine ⟨4165453973113748452806349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5553938630818331270408465 4165453973113748452806349)
          ·
            refine ⟨1562045239917655669802381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4165453973113748452806349 1562045239917655669802381)
            ·
              refine ⟨585766964969120876175893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1562045239917655669802381 585766964969120876175893)
              ·
                refine ⟨27457826482927541070745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 585766964969120876175893 27457826482927541070745)
                ·
                  rfl

theorem cell22_721898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_721898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721898 prefixEnd_721898 := by exact prefixLift 721898
  have htrace : WordTrace (prefixWord ++ tailWord_721898) baseStart_721898 baseEnd_721898 := by
    simpa [prefixWord, tailWord_721898, baseEnd_721898] using wordTrace_append hprefix tailTrace_721898
  have hstable : (prefixWord ++ tailWord_721898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721898).length < 2 ^ (prefixWord ++ tailWord_721898).sum := by decide
  have hdescent : baseEnd_721898 < baseStart_721898 := by decide
  rcases family_descends (prefixWord ++ tailWord_721898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_721930 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_721930 : Nat := 118140960795 + 721930 * 2 ^ 59
def prefixEnd_721930 : Nat := 4983230072969 + 3 ^ 40 * 721930 * 2
def baseEnd_721930 : Nat := 247131392600310452836607

theorem tailTrace_721930 : CollatzResearch.WordTrace tailWord_721930 prefixEnd_721930 247131392600310452836607 := by
  unfold tailWord_721930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582737568644595168256811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17553966849718920448684829 6582737568644595168256811)
  ·
    refine ⟨9874106352966892752385217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6582737568644595168256811 9874106352966892752385217)
    ·
      refine ⟨7405579764725169564288913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9874106352966892752385217 7405579764725169564288913)
      ·
        refine ⟨5554184823543877173216685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7405579764725169564288913 5554184823543877173216685)
        ·
          refine ⟨2082819308828953939956257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5554184823543877173216685 2082819308828953939956257)
          ·
            refine ⟨1562114481621715454967193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082819308828953939956257 1562114481621715454967193)
            ·
              refine ⟨1171585861216286591225395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562114481621715454967193 1171585861216286591225395)
              ·
                refine ⟨1757378791824429886838093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171585861216286591225395 1757378791824429886838093)
                ·
                  refine ⟨659017046934161207564285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1757378791824429886838093 659017046934161207564285)
                  ·
                    refine ⟨247131392600310452836607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659017046934161207564285 247131392600310452836607)
                    ·
                      rfl

theorem cell22_721930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_721930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_721930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_721930 prefixEnd_721930 := by exact prefixLift 721930
  have htrace : WordTrace (prefixWord ++ tailWord_721930) baseStart_721930 baseEnd_721930 := by
    simpa [prefixWord, tailWord_721930, baseEnd_721930] using wordTrace_append hprefix tailTrace_721930
  have hstable : (prefixWord ++ tailWord_721930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_721930).length < 2 ^ (prefixWord ++ tailWord_721930).sum := by decide
  have hdescent : baseEnd_721930 < baseStart_721930 := by decide
  rcases family_descends (prefixWord ++ tailWord_721930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722001 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_722001 : Nat := 118140960795 + 722001 * 2 ^ 59
def prefixEnd_722001 : Nat := 4983230072969 + 3 ^ 40 * 722001 * 2
def baseEnd_722001 : Nat := 247155697351289934311389

theorem tailTrace_722001 : CollatzResearch.WordTrace tailWord_722001 prefixEnd_722001 247155697351289934311389 := by
  unfold tailWord_722001
  simp only [CollatzResearch.WordTrace]
  refine ⟨26333539857321159798861857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17555693238214106532574571 26333539857321159798861857)
  ·
    refine ⟨19750154892990869849146393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26333539857321159798861857 19750154892990869849146393)
    ·
      refine ⟨14812616169743152386859795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19750154892990869849146393 14812616169743152386859795)
      ·
        refine ⟨22218924254614728580289693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14812616169743152386859795 22218924254614728580289693)
        ·
          refine ⟨8332096595480523217608635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22218924254614728580289693 8332096595480523217608635)
          ·
            refine ⟨12498144893220784826412953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8332096595480523217608635 12498144893220784826412953)
            ·
              refine ⟨9373608669915588619809715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12498144893220784826412953 9373608669915588619809715)
              ·
                refine ⟨14060413004873382929714573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9373608669915588619809715 14060413004873382929714573)
                ·
                  refine ⟨5272654876827518598642965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14060413004873382929714573 5272654876827518598642965)
                  ·
                    refine ⟨247155697351289934311389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5272654876827518598642965 247155697351289934311389)
                    ·
                      rfl

theorem cell22_722001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_722001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722001 prefixEnd_722001 := by exact prefixLift 722001
  have htrace : WordTrace (prefixWord ++ tailWord_722001) baseStart_722001 baseEnd_722001 := by
    simpa [prefixWord, tailWord_722001, baseEnd_722001] using wordTrace_append hprefix tailTrace_722001
  have hstable : (prefixWord ++ tailWord_722001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722001).length < 2 ^ (prefixWord ++ tailWord_722001).sum := by decide
  have hdescent : baseEnd_722001 < baseStart_722001 := by decide
  rcases family_descends (prefixWord ++ tailWord_722001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722016 : List Nat := [2, 1, 1, 3, 2, 2, 1, 10]
def baseStart_722016 : Nat := 118140960795 + 722016 * 2 ^ 59
def prefixEnd_722016 : Nat := 4983230072969 + 3 ^ 40 * 722016 * 2
def baseEnd_722016 : Nat := 27462314684203877242927

theorem tailTrace_722016 : CollatzResearch.WordTrace tailWord_722016 prefixEnd_722016 27462314684203877242927 := by
  unfold tailWord_722016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167043476133408680328951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17556057968177878240438601 13167043476133408680328951)
  ·
    refine ⟨19750565214200113020493427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13167043476133408680328951 19750565214200113020493427)
    ·
      refine ⟨29625847821300169530740141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19750565214200113020493427 29625847821300169530740141)
      ·
        refine ⟨11109692932987563574027553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29625847821300169530740141 11109692932987563574027553)
        ·
          refine ⟨8332269699740672680520665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11109692932987563574027553 8332269699740672680520665)
          ·
            refine ⟨6249202274805504510390499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8332269699740672680520665 6249202274805504510390499)
            ·
              refine ⟨9373803412208256765585749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6249202274805504510390499 9373803412208256765585749)
              ·
                refine ⟨27462314684203877242927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9373803412208256765585749 27462314684203877242927)
                ·
                  rfl

theorem cell22_722016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 10].length) (baseStart_722016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722016 prefixEnd_722016 := by exact prefixLift 722016
  have htrace : WordTrace (prefixWord ++ tailWord_722016) baseStart_722016 baseEnd_722016 := by
    simpa [prefixWord, tailWord_722016, baseEnd_722016] using wordTrace_append hprefix tailTrace_722016
  have hstable : (prefixWord ++ tailWord_722016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722016).length < 2 ^ (prefixWord ++ tailWord_722016).sum := by decide
  have hdescent : baseEnd_722016 < baseStart_722016 := by decide
  rcases family_descends (prefixWord ++ tailWord_722016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722024 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 1, 4]
def baseStart_722024 : Nat := 118140960795 + 722024 * 2 ^ 59
def prefixEnd_722024 : Nat := 4983230072969 + 3 ^ 40 * 722024 * 2
def baseEnd_722024 : Nat := 247163570721325540986319

theorem tailTrace_722024 : CollatzResearch.WordTrace tailWord_722024 prefixEnd_722024 247163570721325540986319 := by
  unfold tailWord_722024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167189368118917363474563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17556252490825223151299417 13167189368118917363474563)
  ·
    refine ⟨19750784052178376045211845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13167189368118917363474563 19750784052178376045211845)
    ·
      refine ⟨3703272009783445508477221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19750784052178376045211845 3703272009783445508477221)
      ·
        refine ⟨694363501834396032839479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3703272009783445508477221 694363501834396032839479)
        ·
          refine ⟨1041545252751594049259219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694363501834396032839479 1041545252751594049259219)
          ·
            refine ⟨1562317879127391073888829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041545252751594049259219 1562317879127391073888829)
            ·
              refine ⟨585869204672771652708311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1562317879127391073888829 585869204672771652708311)
              ·
                refine ⟨878803807009157479062467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585869204672771652708311 878803807009157479062467)
                ·
                  refine ⟨1318205710513736218593701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 878803807009157479062467 1318205710513736218593701)
                  ·
                    refine ⟨247163570721325540986319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1318205710513736218593701 247163570721325540986319)
                    ·
                      rfl

theorem cell22_722024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_722024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722024 prefixEnd_722024 := by exact prefixLift 722024
  have htrace : WordTrace (prefixWord ++ tailWord_722024) baseStart_722024 baseEnd_722024 := by
    simpa [prefixWord, tailWord_722024, baseEnd_722024] using wordTrace_append hprefix tailTrace_722024
  have hstable : (prefixWord ++ tailWord_722024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722024).length < 2 ^ (prefixWord ++ tailWord_722024).sum := by decide
  have hdescent : baseEnd_722024 < baseStart_722024 := by decide
  rcases family_descends (prefixWord ++ tailWord_722024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722110 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_722110 : Nat := 118140960795 + 722110 * 2 ^ 59
def prefixEnd_722110 : Nat := 4983230072969 + 3 ^ 40 * 722110 * 2
def baseEnd_722110 : Nat := 247193010278849983336055

theorem tailTrace_722110 : CollatzResearch.WordTrace tailWord_722110 prefixEnd_722110 247193010278849983336055 := by
  unfold tailWord_722110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292189426740783926822473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17558343609284180943053189 3292189426740783926822473)
  ·
    refine ⟨2469142070055587945116855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3292189426740783926822473 2469142070055587945116855)
    ·
      refine ⟨3703713105083381917675283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469142070055587945116855 3703713105083381917675283)
      ·
        refine ⟨5555569657625072876512925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703713105083381917675283 5555569657625072876512925)
        ·
          refine ⟨2083338621609402328692347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5555569657625072876512925 2083338621609402328692347)
          ·
            refine ⟨3125007932414103493038521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083338621609402328692347 3125007932414103493038521)
            ·
              refine ⟨2343755949310577619778891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3125007932414103493038521 2343755949310577619778891)
              ·
                refine ⟨3515633923965866429668337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343755949310577619778891 3515633923965866429668337)
                ·
                  refine ⟨2636725442974399822251253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3515633923965866429668337 2636725442974399822251253)
                  ·
                    refine ⟨247193010278849983336055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2636725442974399822251253 247193010278849983336055)
                    ·
                      rfl

theorem cell22_722110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_722110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722110 prefixEnd_722110 := by exact prefixLift 722110
  have htrace : WordTrace (prefixWord ++ tailWord_722110) baseStart_722110 baseEnd_722110 := by
    simpa [prefixWord, tailWord_722110, baseEnd_722110] using wordTrace_append hprefix tailTrace_722110
  have hstable : (prefixWord ++ tailWord_722110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722110).length < 2 ^ (prefixWord ++ tailWord_722110).sum := by decide
  have hdescent : baseEnd_722110 < baseStart_722110 := by decide
  rcases family_descends (prefixWord ++ tailWord_722110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722112 : List Nat := [2, 1, 1, 2, 6, 1, 3, 1, 5]
def baseStart_722112 : Nat := 118140960795 + 722112 * 2 ^ 59
def prefixEnd_722112 : Nat := 4983230072969 + 3 ^ 40 * 722112 * 2
def baseEnd_722112 : Nat := 82397898306574214928683

theorem tailTrace_722112 : CollatzResearch.WordTrace tailWord_722112 prefixEnd_722112 82397898306574214928683 := by
  unfold tailWord_722112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13168794179959512878076295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17558392239946017170768393 13168794179959512878076295)
  ·
    refine ⟨19753191269939269317114443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13168794179959512878076295 19753191269939269317114443)
    ·
      refine ⟨29629786904908903975671665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19753191269939269317114443 29629786904908903975671665)
      ·
        refine ⟨22222340178681677981753749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29629786904908903975671665 22222340178681677981753749)
        ·
          refine ⟨1041672195875703655394707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22222340178681677981753749 1041672195875703655394707)
          ·
            refine ⟨1562508293813555483092061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041672195875703655394707 1562508293813555483092061)
            ·
              refine ⟨585940610180083306159523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1562508293813555483092061 585940610180083306159523)
              ·
                refine ⟨878910915270124959239285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585940610180083306159523 878910915270124959239285)
                ·
                  refine ⟨82397898306574214928683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 878910915270124959239285 82397898306574214928683)
                  ·
                    rfl

theorem cell22_722112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 5].length) (baseStart_722112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722112 prefixEnd_722112 := by exact prefixLift 722112
  have htrace : WordTrace (prefixWord ++ tailWord_722112) baseStart_722112 baseEnd_722112 := by
    simpa [prefixWord, tailWord_722112, baseEnd_722112] using wordTrace_append hprefix tailTrace_722112
  have hstable : (prefixWord ++ tailWord_722112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722112).length < 2 ^ (prefixWord ++ tailWord_722112).sum := by decide
  have hdescent : baseEnd_722112 < baseStart_722112 := by decide
  rcases family_descends (prefixWord ++ tailWord_722112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722118 : List Nat := [6, 1, 2, 2, 2, 1, 2, 6]
def baseStart_722118 : Nat := 118140960795 + 722118 * 2 ^ 59
def prefixEnd_722118 : Nat := 4983230072969 + 3 ^ 40 * 722118 * 2
def baseEnd_722118 : Nat := 27466194315815625459559

theorem tailTrace_722118 : CollatzResearch.WordTrace tailWord_722118 prefixEnd_722118 27466194315815625459559 := by
  unfold tailWord_722118
  simp only [CollatzResearch.WordTrace]
  refine ⟨823056474934290274402219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17558538131931525853914005 823056474934290274402219)
  ·
    refine ⟨1234584712401435411603329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 823056474934290274402219 1234584712401435411603329)
    ·
      refine ⟨925938534301076558702497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1234584712401435411603329 925938534301076558702497)
      ·
        refine ⟨694453900725807419026873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 925938534301076558702497 694453900725807419026873)
        ·
          refine ⟨520840425544355564270155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694453900725807419026873 520840425544355564270155)
          ·
            refine ⟨781260638316533346405233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520840425544355564270155 781260638316533346405233)
            ·
              refine ⟨585945478737400009803925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781260638316533346405233 585945478737400009803925)
              ·
                refine ⟨27466194315815625459559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 585945478737400009803925 27466194315815625459559)
                ·
                  rfl

theorem cell22_722118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_722118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722118 prefixEnd_722118 := by exact prefixLift 722118
  have htrace : WordTrace (prefixWord ++ tailWord_722118) baseStart_722118 baseEnd_722118 := by
    simpa [prefixWord, tailWord_722118, baseEnd_722118] using wordTrace_append hprefix tailTrace_722118
  have hstable : (prefixWord ++ tailWord_722118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722118).length < 2 ^ (prefixWord ++ tailWord_722118).sum := by decide
  have hdescent : baseEnd_722118 < baseStart_722118 := by decide
  rcases family_descends (prefixWord ++ tailWord_722118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722138 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_722138 : Nat := 118140960795 + 722138 * 2 ^ 59
def prefixEnd_722138 : Nat := 4983230072969 + 3 ^ 40 * 722138 * 2
def baseEnd_722138 : Nat := 247202595251067243635969

theorem tailTrace_722138 : CollatzResearch.WordTrace tailWord_722138 prefixEnd_722138 247202595251067243635969 := by
  unfold tailWord_722138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6584634164456208049149767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17559024438549888131066045 6584634164456208049149767)
  ·
    refine ⟨9876951246684312073724651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6584634164456208049149767 9876951246684312073724651)
    ·
      refine ⟨14815426870026468110586977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9876951246684312073724651 14815426870026468110586977)
      ·
        refine ⟨11111570152519851082940233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14815426870026468110586977 11111570152519851082940233)
        ·
          refine ⟨8333677614389888312205175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11111570152519851082940233 8333677614389888312205175)
          ·
            refine ⟨12500516421584832468307763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8333677614389888312205175 12500516421584832468307763)
            ·
              refine ⟨18750774632377248702461645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12500516421584832468307763 18750774632377248702461645)
              ·
                refine ⟨7031540487141468263423117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18750774632377248702461645 7031540487141468263423117)
                ·
                  refine ⟨2636827682678050598783669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7031540487141468263423117 2636827682678050598783669)
                  ·
                    refine ⟨247202595251067243635969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2636827682678050598783669 247202595251067243635969)
                    ·
                      rfl

theorem cell22_722138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_722138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722138 prefixEnd_722138 := by exact prefixLift 722138
  have htrace : WordTrace (prefixWord ++ tailWord_722138) baseStart_722138 baseEnd_722138 := by
    simpa [prefixWord, tailWord_722138, baseEnd_722138] using wordTrace_append hprefix tailTrace_722138
  have hstable : (prefixWord ++ tailWord_722138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722138).length < 2 ^ (prefixWord ++ tailWord_722138).sum := by decide
  have hdescent : baseEnd_722138 < baseStart_722138 := by decide
  rcases family_descends (prefixWord ++ tailWord_722138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722155 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 4, 3]
def baseStart_722155 : Nat := 118140960795 + 722155 * 2 ^ 59
def prefixEnd_722155 : Nat := 4983230072969 + 3 ^ 40 * 722155 * 2
def baseEnd_722155 : Nat := 247208414698484865960917

theorem tailTrace_722155 : CollatzResearch.WordTrace tailWord_722155 prefixEnd_722155 247208414698484865960917 := by
  unfold tailWord_722155
  simp only [CollatzResearch.WordTrace]
  refine ⟨26339156698763244099967919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17559437799175496066645279 26339156698763244099967919)
  ·
    refine ⟨39508735048144866149951879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26339156698763244099967919 39508735048144866149951879)
    ·
      refine ⟨59263102572217299224927819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39508735048144866149951879 59263102572217299224927819)
      ·
        refine ⟨88894653858325948837391729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59263102572217299224927819 88894653858325948837391729)
        ·
          refine ⟨66670990393744461628043797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88894653858325948837391729 66670990393744461628043797)
          ·
            refine ⟨3125202674706771638814553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66670990393744461628043797 3125202674706771638814553)
            ·
              refine ⟨2343902006030078729110915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3125202674706771638814553 2343902006030078729110915)
              ·
                refine ⟨3515853009045118093666373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343902006030078729110915 3515853009045118093666373)
                ·
                  refine ⟨659222439195959642562445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3515853009045118093666373 659222439195959642562445)
                  ·
                    refine ⟨247208414698484865960917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659222439195959642562445 247208414698484865960917)
                    ·
                      rfl

theorem cell22_722155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 3].length) (baseStart_722155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722155 prefixEnd_722155 := by exact prefixLift 722155
  have htrace : WordTrace (prefixWord ++ tailWord_722155) baseStart_722155 baseEnd_722155 := by
    simpa [prefixWord, tailWord_722155, baseEnd_722155] using wordTrace_append hprefix tailTrace_722155
  have hstable : (prefixWord ++ tailWord_722155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722155).length < 2 ^ (prefixWord ++ tailWord_722155).sum := by decide
  have hdescent : baseEnd_722155 < baseStart_722155 := by decide
  rcases family_descends (prefixWord ++ tailWord_722155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722157 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 6]
def baseStart_722157 : Nat := 118140960795 + 722157 * 2 ^ 59
def prefixEnd_722157 : Nat := 4983230072969 + 3 ^ 40 * 722157 * 2
def baseEnd_722157 : Nat := 82403033113119175803637

theorem tailTrace_722157 : CollatzResearch.WordTrace tailWord_722157 prefixEnd_722157 82403033113119175803637 := by
  unfold tailWord_722157
  simp only [CollatzResearch.WordTrace]
  refine ⟨26339229644755998441540725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17559486429837332294360483 26339229644755998441540725)
  ·
    refine ⟨2469302779195874853894443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26339229644755998441540725 2469302779195874853894443)
    ·
      refine ⟨3703954168793812280841665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469302779195874853894443 3703954168793812280841665)
      ·
        refine ⟨2777965626595359210631249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3703954168793812280841665 2777965626595359210631249)
        ·
          refine ⟨2083474219946519407973437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2777965626595359210631249 2083474219946519407973437)
          ·
            refine ⟨781302832479944777990039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2083474219946519407973437 781302832479944777990039)
            ·
              refine ⟨1171954248719917166985059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781302832479944777990039 1171954248719917166985059)
              ·
                refine ⟨1757931373079875750477589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171954248719917166985059 1757931373079875750477589)
                ·
                  refine ⟨82403033113119175803637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1757931373079875750477589 82403033113119175803637)
                  ·
                    rfl

theorem cell22_722157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_722157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722157 prefixEnd_722157 := by exact prefixLift 722157
  have htrace : WordTrace (prefixWord ++ tailWord_722157) baseStart_722157 baseEnd_722157 := by
    simpa [prefixWord, tailWord_722157, baseEnd_722157] using wordTrace_append hprefix tailTrace_722157
  have hstable : (prefixWord ++ tailWord_722157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722157).length < 2 ^ (prefixWord ++ tailWord_722157).sum := by decide
  have hdescent : baseEnd_722157 < baseStart_722157 := by decide
  rcases family_descends (prefixWord ++ tailWord_722157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722275 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 6]
def baseStart_722275 : Nat := 118140960795 + 722275 * 2 ^ 59
def prefixEnd_722275 : Nat := 4983230072969 + 3 ^ 40 * 722275 * 2
def baseEnd_722275 : Nat := 82416497716948184320183

theorem tailTrace_722275 : CollatzResearch.WordTrace tailWord_722275 prefixEnd_722275 82416497716948184320183 := by
  unfold tailWord_722275
  simp only [CollatzResearch.WordTrace]
  refine ⟨26343533458328504594336279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17562355638885669729557519 26343533458328504594336279)
  ·
    refine ⟨39515300187492756891504419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26343533458328504594336279 39515300187492756891504419)
    ·
      refine ⟨59272950281239135337256629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39515300187492756891504419 59272950281239135337256629)
      ·
        refine ⟨5556839088866168937867809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59272950281239135337256629 5556839088866168937867809)
        ·
          refine ⟨4167629316649626703400857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5556839088866168937867809 4167629316649626703400857)
          ·
            refine ⟨3125721987487220027550643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4167629316649626703400857 3125721987487220027550643)
            ·
              refine ⟨4688582981230830041325965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125721987487220027550643 4688582981230830041325965)
              ·
                refine ⟨1758218617961561265497237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4688582981230830041325965 1758218617961561265497237)
                ·
                  refine ⟨82416497716948184320183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1758218617961561265497237 82416497716948184320183)
                  ·
                    rfl

theorem cell22_722275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 6].length) (baseStart_722275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722275 prefixEnd_722275 := by exact prefixLift 722275
  have htrace : WordTrace (prefixWord ++ tailWord_722275) baseStart_722275 baseEnd_722275 := by
    simpa [prefixWord, tailWord_722275, baseEnd_722275] using wordTrace_append hprefix tailTrace_722275
  have hstable : (prefixWord ++ tailWord_722275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722275).length < 2 ^ (prefixWord ++ tailWord_722275).sum := by decide
  have hdescent : baseEnd_722275 < baseStart_722275 := by decide
  rcases family_descends (prefixWord ++ tailWord_722275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722302 : List Nat := [4, 2, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_722302 : Nat := 118140960795 + 722302 * 2 ^ 59
def prefixEnd_722302 : Nat := 4983230072969 + 3 ^ 40 * 722302 * 2
def baseEnd_722302 : Nat := 247258735802625482535467

theorem tailTrace_722302 : CollatzResearch.WordTrace tailWord_722302 prefixEnd_722302 247258735802625482535467 := by
  unfold tailWord_722302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293064778653836025696145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17563012152820458803712773 3293064778653836025696145)
  ·
    refine ⟨2469798583990377019272109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3293064778653836025696145 2469798583990377019272109)
    ·
      refine ⟨926174468996391382227041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2469798583990377019272109 926174468996391382227041)
      ·
        refine ⟨694630851747293536670281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 926174468996391382227041 694630851747293536670281)
        ·
          refine ⟨520973138810470152502711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694630851747293536670281 520973138810470152502711)
          ·
            refine ⟨781459708215705228754067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520973138810470152502711 781459708215705228754067)
            ·
              refine ⟨1172189562323557843131101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781459708215705228754067 1172189562323557843131101)
              ·
                refine ⟨439571085871334191174163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1172189562323557843131101 439571085871334191174163)
                ·
                  refine ⟨659356628807001286761245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439571085871334191174163 659356628807001286761245)
                  ·
                    refine ⟨247258735802625482535467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659356628807001286761245 247258735802625482535467)
                    ·
                      rfl

theorem cell22_722302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_722302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722302 prefixEnd_722302 := by exact prefixLift 722302
  have htrace : WordTrace (prefixWord ++ tailWord_722302) baseStart_722302 baseEnd_722302 := by
    simpa [prefixWord, tailWord_722302, baseEnd_722302] using wordTrace_append hprefix tailTrace_722302
  have hstable : (prefixWord ++ tailWord_722302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722302).length < 2 ^ (prefixWord ++ tailWord_722302).sum := by decide
  have hdescent : baseEnd_722302 < baseStart_722302 := by decide
  rcases family_descends (prefixWord ++ tailWord_722302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722307 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 4, 3]
def baseStart_722307 : Nat := 118140960795 + 722307 * 2 ^ 59
def prefixEnd_722307 : Nat := 4983230072969 + 3 ^ 40 * 722307 * 2
def baseEnd_722307 : Nat := 247260447404807136160451

theorem tailTrace_722307 : CollatzResearch.WordTrace tailWord_722307 prefixEnd_722307 247260447404807136160451 := by
  unfold tailWord_722307
  simp only [CollatzResearch.WordTrace]
  refine ⟨26344700594212574059501175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17563133729475049373000783 26344700594212574059501175)
  ·
    refine ⟨39517050891318861089251763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26344700594212574059501175 39517050891318861089251763)
    ·
      refine ⟨59275576336978291633877645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39517050891318861089251763 59275576336978291633877645)
      ·
        refine ⟨22228341126366859362704117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59275576336978291633877645 22228341126366859362704117)
        ·
          refine ⟨2083906980596893065253511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22228341126366859362704117 2083906980596893065253511)
          ·
            refine ⟨3125860470895339597880267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083906980596893065253511 3125860470895339597880267)
            ·
              refine ⟨4688790706343009396820401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125860470895339597880267 4688790706343009396820401)
              ·
                refine ⟨3516593029757257047615301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688790706343009396820401 3516593029757257047615301)
                ·
                  refine ⟨659361193079485696427869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3516593029757257047615301 659361193079485696427869)
                  ·
                    refine ⟨247260447404807136160451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659361193079485696427869 247260447404807136160451)
                    ·
                      rfl

theorem cell22_722307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 3].length) (baseStart_722307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722307 prefixEnd_722307 := by exact prefixLift 722307
  have htrace : WordTrace (prefixWord ++ tailWord_722307) baseStart_722307 baseEnd_722307 := by
    simpa [prefixWord, tailWord_722307, baseEnd_722307] using wordTrace_append hprefix tailTrace_722307
  have hstable : (prefixWord ++ tailWord_722307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722307).length < 2 ^ (prefixWord ++ tailWord_722307).sum := by decide
  have hdescent : baseEnd_722307 < baseStart_722307 := by decide
  rcases family_descends (prefixWord ++ tailWord_722307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722324 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_722324 : Nat := 118140960795 + 722324 * 2 ^ 59
def prefixEnd_722324 : Nat := 4983230072969 + 3 ^ 40 * 722324 * 2
def baseEnd_722324 : Nat := 247266266852224758485399

theorem tailTrace_722324 : CollatzResearch.WordTrace tailWord_722324 prefixEnd_722324 247266266852224758485399 := by
  unfold tailWord_722324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13172660317575492981435013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17563547090100657308580017 13172660317575492981435013)
  ·
    refine ⟨2469873809545404934019065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13172660317575492981435013 2469873809545404934019065)
    ·
      refine ⟨1852405357159053700514299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2469873809545404934019065 1852405357159053700514299)
      ·
        refine ⟨2778608035738580550771449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852405357159053700514299 2778608035738580550771449)
        ·
          refine ⟨2083956026803935413078587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778608035738580550771449 2083956026803935413078587)
          ·
            refine ⟨3125934040205903119617881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083956026803935413078587 3125934040205903119617881)
            ·
              refine ⟨2344450530154427339713411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3125934040205903119617881 2344450530154427339713411)
              ·
                refine ⟨3516675795231641009570117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344450530154427339713411 3516675795231641009570117)
                ·
                  refine ⟨659376711605932689294397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3516675795231641009570117 659376711605932689294397)
                  ·
                    refine ⟨247266266852224758485399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659376711605932689294397 247266266852224758485399)
                    ·
                      rfl

theorem cell22_722324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_722324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722324 prefixEnd_722324 := by exact prefixLift 722324
  have htrace : WordTrace (prefixWord ++ tailWord_722324) baseStart_722324 baseEnd_722324 := by
    simpa [prefixWord, tailWord_722324, baseEnd_722324] using wordTrace_append hprefix tailTrace_722324
  have hstable : (prefixWord ++ tailWord_722324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722324).length < 2 ^ (prefixWord ++ tailWord_722324).sum := by decide
  have hdescent : baseEnd_722324 < baseStart_722324 := by decide
  rcases family_descends (prefixWord ++ tailWord_722324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722382 : List Nat := [4, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_722382 : Nat := 118140960795 + 722382 * 2 ^ 59
def prefixEnd_722382 : Nat := 4983230072969 + 3 ^ 40 * 722382 * 2
def baseEnd_722382 : Nat := 82428707145843980178407

theorem tailTrace_722382 : CollatzResearch.WordTrace tailWord_722382 prefixEnd_722382 82428707145843980178407 := by
  unfold tailWord_722382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293429508617607733560175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17564957379293907912320933 3293429508617607733560175)
  ·
    refine ⟨4940144262926411600340263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3293429508617607733560175 4940144262926411600340263)
    ·
      refine ⟨7410216394389617400510395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4940144262926411600340263 7410216394389617400510395)
      ·
        refine ⟨11115324591584426100765593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7410216394389617400510395 11115324591584426100765593)
        ·
          refine ⟨8336493443688319575574195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11115324591584426100765593 8336493443688319575574195)
          ·
            refine ⟨12504740165532479363361293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8336493443688319575574195 12504740165532479363361293)
            ·
              refine ⟨4689277562074679761260485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12504740165532479363361293 4689277562074679761260485)
              ·
                refine ⟨879239542889002455236341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4689277562074679761260485 879239542889002455236341)
                ·
                  refine ⟨82428707145843980178407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 879239542889002455236341 82428707145843980178407)
                  ·
                    rfl

theorem cell22_722382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_722382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722382 prefixEnd_722382 := by exact prefixLift 722382
  have htrace : WordTrace (prefixWord ++ tailWord_722382) baseStart_722382 baseEnd_722382 := by
    simpa [prefixWord, tailWord_722382, baseEnd_722382] using wordTrace_append hprefix tailTrace_722382
  have hstable : (prefixWord ++ tailWord_722382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722382).length < 2 ^ (prefixWord ++ tailWord_722382).sum := by decide
  have hdescent : baseEnd_722382 < baseStart_722382 := by decide
  rcases family_descends (prefixWord ++ tailWord_722382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722397 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_722397 : Nat := 118140960795 + 722397 * 2 ^ 59
def prefixEnd_722397 : Nat := 4983230072969 + 3 ^ 40 * 722397 * 2
def baseEnd_722397 : Nat := 247291256244076901410175

theorem tailTrace_722397 : CollatzResearch.WordTrace tailWord_722397 prefixEnd_722397 247291256244076901410175 := by
  unfold tailWord_722397
  simp only [CollatzResearch.WordTrace]
  refine ⟨26347983163886519430277445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17565322109257679620184963 26347983163886519430277445)
  ·
    refine ⟨4940246843228722393177021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26347983163886519430277445 4940246843228722393177021)
    ·
      refine ⟨1852592566210770897441383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4940246843228722393177021 1852592566210770897441383)
      ·
        refine ⟨2778888849316156346162075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852592566210770897441383 2778888849316156346162075)
        ·
          refine ⟨4168333273974234519243113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778888849316156346162075 4168333273974234519243113)
          ·
            refine ⟨3126249955480675889432335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4168333273974234519243113 3126249955480675889432335)
            ·
              refine ⟨4689374933221013834148503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126249955480675889432335 4689374933221013834148503)
              ·
                refine ⟨7034062399831520751222755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4689374933221013834148503 7034062399831520751222755)
                ·
                  refine ⟨10551093599747281126834133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7034062399831520751222755 10551093599747281126834133)
                  ·
                    refine ⟨247291256244076901410175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10551093599747281126834133 247291256244076901410175)
                    ·
                      rfl

theorem cell22_722397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_722397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722397 prefixEnd_722397 := by exact prefixLift 722397
  have htrace : WordTrace (prefixWord ++ tailWord_722397) baseStart_722397 baseEnd_722397 := by
    simpa [prefixWord, tailWord_722397, baseEnd_722397] using wordTrace_append hprefix tailTrace_722397
  have hstable : (prefixWord ++ tailWord_722397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722397).length < 2 ^ (prefixWord ++ tailWord_722397).sum := by decide
  have hdescent : baseEnd_722397 < baseStart_722397 := by decide
  rcases family_descends (prefixWord ++ tailWord_722397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722429 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_722429 : Nat := 118140960795 + 722429 * 2 ^ 59
def prefixEnd_722429 : Nat := 4983230072969 + 3 ^ 40 * 722429 * 2
def baseEnd_722429 : Nat := 247302210498039484610077

theorem tailTrace_722429 : CollatzResearch.WordTrace tailWord_722429 prefixEnd_722429 247302210498039484610077 := by
  unfold tailWord_722429
  simp only [CollatzResearch.WordTrace]
  refine ⟨26349150299770588895442341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17566100199847059263628227 26349150299770588895442341)
  ·
    refine ⟨4940465681206985417895439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26349150299770588895442341 4940465681206985417895439)
    ·
      refine ⟨7410698521810478126843159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4940465681206985417895439 7410698521810478126843159)
      ·
        refine ⟨11116047782715717190264739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7410698521810478126843159 11116047782715717190264739)
        ·
          refine ⟨16674071674073575785397109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11116047782715717190264739 16674071674073575785397109)
          ·
            refine ⟨1563194219444397729880979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16674071674073575785397109 1563194219444397729880979)
            ·
              refine ⟨2344791329166596594821469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563194219444397729880979 2344791329166596594821469)
              ·
                refine ⟨879296748437473723058051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2344791329166596594821469 879296748437473723058051)
                ·
                  refine ⟨1318945122656210584587077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879296748437473723058051 1318945122656210584587077)
                  ·
                    refine ⟨247302210498039484610077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1318945122656210584587077 247302210498039484610077)
                    ·
                      rfl

theorem cell22_722429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_722429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722429 prefixEnd_722429 := by exact prefixLift 722429
  have htrace : WordTrace (prefixWord ++ tailWord_722429) baseStart_722429 baseEnd_722429 := by
    simpa [prefixWord, tailWord_722429, baseEnd_722429] using wordTrace_append hprefix tailTrace_722429
  have hstable : (prefixWord ++ tailWord_722429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722429).length < 2 ^ (prefixWord ++ tailWord_722429).sum := by decide
  have hdescent : baseEnd_722429 < baseStart_722429 := by decide
  rcases family_descends (prefixWord ++ tailWord_722429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722444 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 6]
def baseStart_722444 : Nat := 118140960795 + 722444 * 2 ^ 59
def prefixEnd_722444 : Nat := 4983230072969 + 3 ^ 40 * 722444 * 2
def baseEnd_722444 : Nat := 82435781768194815161677

theorem tailTrace_722444 : CollatzResearch.WordTrace tailWord_722444 prefixEnd_722444 82435781768194815161677 := by
  unfold tailWord_722444
  simp only [CollatzResearch.WordTrace]
  refine ⟨13174848697358123228619193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17566464929810830971492257 13174848697358123228619193)
  ·
    refine ⟨9881136523018592421464395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13174848697358123228619193 9881136523018592421464395)
    ·
      refine ⟨14821704784527888632196593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9881136523018592421464395 14821704784527888632196593)
      ·
        refine ⟨11116278588395916474147445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14821704784527888632196593 11116278588395916474147445)
        ·
          refine ⟨1042151117662117169451323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11116278588395916474147445 1042151117662117169451323)
          ·
            refine ⟨1563226676493175754176985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042151117662117169451323 1563226676493175754176985)
            ·
              refine ⟨1172420007369881815632739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563226676493175754176985 1172420007369881815632739)
              ·
                refine ⟨1758630011054822723449109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172420007369881815632739 1758630011054822723449109)
                ·
                  refine ⟨82435781768194815161677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1758630011054822723449109 82435781768194815161677)
                  ·
                    rfl

theorem cell22_722444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_722444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722444 prefixEnd_722444 := by exact prefixLift 722444
  have htrace : WordTrace (prefixWord ++ tailWord_722444) baseStart_722444 baseEnd_722444 := by
    simpa [prefixWord, tailWord_722444, baseEnd_722444] using wordTrace_append hprefix tailTrace_722444
  have hstable : (prefixWord ++ tailWord_722444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722444).length < 2 ^ (prefixWord ++ tailWord_722444).sum := by decide
  have hdescent : baseEnd_722444 < baseStart_722444 := by decide
  rcases family_descends (prefixWord ++ tailWord_722444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722474 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_722474 : Nat := 118140960795 + 722474 * 2 ^ 59
def prefixEnd_722474 : Nat := 4983230072969 + 3 ^ 40 * 722474 * 2
def baseEnd_722474 : Nat := 247317614917674367234939

theorem tailTrace_722474 : CollatzResearch.WordTrace tailWord_722474 prefixEnd_722474 247317614917674367234939 := by
  unfold tailWord_722474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587697896151890395207619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17567194389738374387220317 6587697896151890395207619)
  ·
    refine ⟨9881546844227835592811429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6587697896151890395207619 9881546844227835592811429)
    ·
      refine ⟨1852790033292719173652143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9881546844227835592811429 1852790033292719173652143)
      ·
        refine ⟨2779185049939078760478215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852790033292719173652143 2779185049939078760478215)
        ·
          refine ⟨4168777574908618140717323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779185049939078760478215 4168777574908618140717323)
          ·
            refine ⟨6253166362362927211075985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168777574908618140717323 6253166362362927211075985)
            ·
              refine ⟨4689874771772195408306989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6253166362362927211075985 4689874771772195408306989)
              ·
                refine ⟨1758703039414573278115121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4689874771772195408306989 1758703039414573278115121)
                ·
                  refine ⟨1319027279560929958586341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1758703039414573278115121 1319027279560929958586341)
                  ·
                    refine ⟨247317614917674367234939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1319027279560929958586341 247317614917674367234939)
                    ·
                      rfl

theorem cell22_722474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_722474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722474 prefixEnd_722474 := by exact prefixLift 722474
  have htrace : WordTrace (prefixWord ++ tailWord_722474) baseStart_722474 baseEnd_722474 := by
    simpa [prefixWord, tailWord_722474, baseEnd_722474] using wordTrace_append hprefix tailTrace_722474
  have hstable : (prefixWord ++ tailWord_722474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722474).length < 2 ^ (prefixWord ++ tailWord_722474).sum := by decide
  have hdescent : baseEnd_722474 < baseStart_722474 := by decide
  rcases family_descends (prefixWord ++ tailWord_722474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722478 : List Nat := [4, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_722478 : Nat := 118140960795 + 722478 * 2 ^ 59
def prefixEnd_722478 : Nat := 4983230072969 + 3 ^ 40 * 722478 * 2
def baseEnd_722478 : Nat := 82439661399806563378309

theorem tailTrace_722478 : CollatzResearch.WordTrace tailWord_722478 prefixEnd_722478 82439661399806563378309 := by
  unfold tailWord_722478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293867184574133782997011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17567291651062046842650725 3293867184574133782997011)
  ·
    refine ⟨4940800776861200674495517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3293867184574133782997011 4940800776861200674495517)
    ·
      refine ⟨1852800291322950252935819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4940800776861200674495517 1852800291322950252935819)
      ·
        refine ⟨2779200436984425379403729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852800291322950252935819 2779200436984425379403729)
        ·
          refine ⟨2084400327738319034552797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2779200436984425379403729 2084400327738319034552797)
          ·
            refine ⟨781650122901869637957299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2084400327738319034552797 781650122901869637957299)
            ·
              refine ⟨1172475184352804456935949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781650122901869637957299 1172475184352804456935949)
              ·
                refine ⟨439678194132301671350981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1172475184352804456935949 439678194132301671350981)
                ·
                  refine ⟨82439661399806563378309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439678194132301671350981 82439661399806563378309)
                  ·
                    rfl

theorem cell22_722478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_722478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722478 prefixEnd_722478 := by exact prefixLift 722478
  have htrace : WordTrace (prefixWord ++ tailWord_722478) baseStart_722478 baseEnd_722478 := by
    simpa [prefixWord, tailWord_722478, baseEnd_722478] using wordTrace_append hprefix tailTrace_722478
  have hstable : (prefixWord ++ tailWord_722478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722478).length < 2 ^ (prefixWord ++ tailWord_722478).sum := by decide
  have hdescent : baseEnd_722478 < baseStart_722478 := by decide
  rcases family_descends (prefixWord ++ tailWord_722478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722596 : List Nat := [2, 3, 1, 2, 2, 2, 1, 5, 4]
def baseStart_722596 : Nat := 118140960795 + 722596 * 2 ^ 59
def prefixEnd_722596 : Nat := 4983230072969 + 3 ^ 40 * 722596 * 2
def baseEnd_722596 : Nat := 82453126003635571894855

theorem tailTrace_722596 : CollatzResearch.WordTrace tailWord_722596 prefixEnd_722596 82453126003635571894855 := by
  unfold tailWord_722596
  simp only [CollatzResearch.WordTrace]
  refine ⟨13177620645082788208385821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17570160860110384277847761 13177620645082788208385821)
  ·
    refine ⟨4941607741906045578144683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13177620645082788208385821 4941607741906045578144683)
    ·
      refine ⟨7412411612859068367217025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4941607741906045578144683 7412411612859068367217025)
      ·
        refine ⟨5559308709644301275412769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7412411612859068367217025 5559308709644301275412769)
        ·
          refine ⟨4169481532233225956559577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5559308709644301275412769 4169481532233225956559577)
          ·
            refine ⟨3127111149174919467419683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4169481532233225956559577 3127111149174919467419683)
            ·
              refine ⟨4690666723762379201129525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127111149174919467419683 4690666723762379201129525)
              ·
                refine ⟨439750005352723050105893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4690666723762379201129525 439750005352723050105893)
                ·
                  refine ⟨82453126003635571894855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439750005352723050105893 82453126003635571894855)
                  ·
                    rfl

theorem cell22_722596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_722596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722596 prefixEnd_722596 := by exact prefixLift 722596
  have htrace : WordTrace (prefixWord ++ tailWord_722596) baseStart_722596 baseEnd_722596 := by
    simpa [prefixWord, tailWord_722596, baseEnd_722596] using wordTrace_append hprefix tailTrace_722596
  have hstable : (prefixWord ++ tailWord_722596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722596).length < 2 ^ (prefixWord ++ tailWord_722596).sum := by decide
  have hdescent : baseEnd_722596 < baseStart_722596 := by decide
  rcases family_descends (prefixWord ++ tailWord_722596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722607 : List Nat := [1, 1, 2, 1, 2, 4, 11]
def baseStart_722607 : Nat := 118140960795 + 722607 * 2 ^ 59
def prefixEnd_722607 : Nat := 4983230072969 + 3 ^ 40 * 722607 * 2
def baseEnd_722607 : Nat := 9161597908729864950353

theorem tailTrace_722607 : CollatzResearch.WordTrace tailWord_722607 prefixEnd_722607 9161597908729864950353 := by
  unfold tailWord_722607
  simp only [CollatzResearch.WordTrace]
  refine ⟨26355642493125725295422075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17570428328750483530281383 26355642493125725295422075)
  ·
    refine ⟨39533463739688587943133113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26355642493125725295422075 39533463739688587943133113)
    ·
      refine ⟨29650097804766440957349835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39533463739688587943133113 29650097804766440957349835)
      ·
        refine ⟨44475146707149661436024753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29650097804766440957349835 44475146707149661436024753)
        ·
          refine ⟨33356360030362246077018565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44475146707149661436024753 33356360030362246077018565)
          ·
            refine ⟨6254317505692921139440981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33356360030362246077018565 6254317505692921139440981)
            ·
              refine ⟨9161597908729864950353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6254317505692921139440981 9161597908729864950353)
              ·
                rfl

theorem cell22_722607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 11].length) (baseStart_722607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722607 prefixEnd_722607 := by exact prefixLift 722607
  have htrace : WordTrace (prefixWord ++ tailWord_722607) baseStart_722607 baseEnd_722607 := by
    simpa [prefixWord, tailWord_722607, baseEnd_722607] using wordTrace_append hprefix tailTrace_722607
  have hstable : (prefixWord ++ tailWord_722607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722607).length < 2 ^ (prefixWord ++ tailWord_722607).sum := by decide
  have hdescent : baseEnd_722607 < baseStart_722607 := by decide
  rcases family_descends (prefixWord ++ tailWord_722607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722641 : List Nat := [1, 2, 2, 1, 2, 6, 2, 6]
def baseStart_722641 : Nat := 118140960795 + 722641 * 2 ^ 59
def prefixEnd_722641 : Nat := 4983230072969 + 3 ^ 40 * 722641 * 2
def baseEnd_722641 : Nat := 27486086936726844256603

theorem tailTrace_722641 : CollatzResearch.WordTrace tailWord_722641 prefixEnd_722641 27486086936726844256603 := by
  unfold tailWord_722641
  simp only [CollatzResearch.WordTrace]
  refine ⟨26356882575002549102159777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17571255050001699401439851 26356882575002549102159777)
  ·
    refine ⟨19767661931251911826619833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26356882575002549102159777 19767661931251911826619833)
    ·
      refine ⟨14825746448438933869964875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19767661931251911826619833 14825746448438933869964875)
      ·
        refine ⟨22238619672658400804947313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14825746448438933869964875 22238619672658400804947313)
        ·
          refine ⟨16678964754493800603710485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22238619672658400804947313 16678964754493800603710485)
          ·
            refine ⟨781826472866896903298929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16678964754493800603710485 781826472866896903298929)
            ·
              refine ⟨586369854650172677474197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 781826472866896903298929 586369854650172677474197)
              ·
                refine ⟨27486086936726844256603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 586369854650172677474197 27486086936726844256603)
                ·
                  rfl

theorem cell22_722641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 6].length) (baseStart_722641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722641 prefixEnd_722641 := by exact prefixLift 722641
  have htrace : WordTrace (prefixWord ++ tailWord_722641) baseStart_722641 baseEnd_722641 := by
    simpa [prefixWord, tailWord_722641, baseEnd_722641] using wordTrace_append hprefix tailTrace_722641
  have hstable : (prefixWord ++ tailWord_722641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722641).length < 2 ^ (prefixWord ++ tailWord_722641).sum := by decide
  have hdescent : baseEnd_722641 < baseStart_722641 := by decide
  rcases family_descends (prefixWord ++ tailWord_722641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722673 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 3, 3]
def baseStart_722673 : Nat := 118140960795 + 722673 * 2 ^ 59
def prefixEnd_722673 : Nat := 4983230072969 + 3 ^ 40 * 722673 * 2
def baseEnd_722673 : Nat := 247385736684504181509329

theorem tailTrace_722673 : CollatzResearch.WordTrace tailWord_722673 prefixEnd_722673 247385736684504181509329 := by
  unfold tailWord_722673
  simp only [CollatzResearch.WordTrace]
  refine ⟨26358049710886618567324673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17572033140591079044883115 26358049710886618567324673)
  ·
    refine ⟨19768537283164963925493505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26358049710886618567324673 19768537283164963925493505)
    ·
      refine ⟨14826402962373722944120129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19768537283164963925493505 14826402962373722944120129)
      ·
        refine ⟨11119802221780292208090097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14826402962373722944120129 11119802221780292208090097)
        ·
          refine ⟨8339851666335219156067573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11119802221780292208090097 8339851666335219156067573)
          ·
            refine ⟨781861093718926795881335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8339851666335219156067573 781861093718926795881335)
            ·
              refine ⟨1172791640578390193822003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781861093718926795881335 1172791640578390193822003)
              ·
                refine ⟨1759187460867585290733005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172791640578390193822003 1759187460867585290733005)
                ·
                  refine ⟨659695297825344484024877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1759187460867585290733005 659695297825344484024877)
                  ·
                    refine ⟨247385736684504181509329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659695297825344484024877 247385736684504181509329)
                    ·
                      rfl

theorem cell22_722673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_722673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722673 prefixEnd_722673 := by exact prefixLift 722673
  have htrace : WordTrace (prefixWord ++ tailWord_722673) baseStart_722673 baseEnd_722673 := by
    simpa [prefixWord, tailWord_722673, baseEnd_722673] using wordTrace_append hprefix tailTrace_722673
  have hstable : (prefixWord ++ tailWord_722673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722673).length < 2 ^ (prefixWord ++ tailWord_722673).sum := by decide
  have hdescent : baseEnd_722673 < baseStart_722673 := by decide
  rcases family_descends (prefixWord ++ tailWord_722673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722684 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_722684 : Nat := 118140960795 + 722684 * 2 ^ 59
def prefixEnd_722684 : Nat := 4983230072969 + 3 ^ 40 * 722684 * 2
def baseEnd_722684 : Nat := 247389502209303819484295

theorem tailTrace_722684 : CollatzResearch.WordTrace tailWord_722684 prefixEnd_722684 247389502209303819484295 := by
  unfold tailWord_722684
  simp only [CollatzResearch.WordTrace]
  refine ⟨13179225456923383722987553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17572300609231178297316737 13179225456923383722987553)
  ·
    refine ⟨9884419092692537792240665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13179225456923383722987553 9884419092692537792240665)
    ·
      refine ⟨7413314319519403344180499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9884419092692537792240665 7413314319519403344180499)
      ·
        refine ⟨11119971479279105016270749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7413314319519403344180499 11119971479279105016270749)
        ·
          refine ⟨4169989304729664381101531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11119971479279105016270749 4169989304729664381101531)
          ·
            refine ⟨6254983957094496571652297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169989304729664381101531 6254983957094496571652297)
            ·
              refine ⟨4691237967820872428739223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6254983957094496571652297 4691237967820872428739223)
              ·
                refine ⟨7036856951731308643108835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691237967820872428739223 7036856951731308643108835)
                ·
                  refine ⟨10555285427596962964663253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7036856951731308643108835 10555285427596962964663253)
                  ·
                    refine ⟨247389502209303819484295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10555285427596962964663253 247389502209303819484295)
                    ·
                      rfl

theorem cell22_722684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_722684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722684 prefixEnd_722684 := by exact prefixLift 722684
  have htrace : WordTrace (prefixWord ++ tailWord_722684) baseStart_722684 baseEnd_722684 := by
    simpa [prefixWord, tailWord_722684, baseEnd_722684] using wordTrace_append hprefix tailTrace_722684
  have hstable : (prefixWord ++ tailWord_722684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722684).length < 2 ^ (prefixWord ++ tailWord_722684).sum := by decide
  have hdescent : baseEnd_722684 < baseStart_722684 := by decide
  rcases family_descends (prefixWord ++ tailWord_722684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722746 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_722746 : Nat := 118140960795 + 722746 * 2 ^ 59
def prefixEnd_722746 : Nat := 4983230072969 + 3 ^ 40 * 722746 * 2
def baseEnd_722746 : Nat := 247410726076356324434105

theorem tailTrace_722746 : CollatzResearch.WordTrace tailWord_722746 prefixEnd_722746 247410726076356324434105 := by
  unfold tailWord_722746
  simp only [CollatzResearch.WordTrace]
  refine ⟨6590178059905538008683023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17573808159748101356488061 6590178059905538008683023)
  ·
    refine ⟨9885267089858307013024535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6590178059905538008683023 9885267089858307013024535)
    ·
      refine ⟨14827900634787460519536803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9885267089858307013024535 14827900634787460519536803)
      ·
        refine ⟨22241850952181190779305205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14827900634787460519536803 22241850952181190779305205)
        ·
          refine ⟨2085173526766986635559863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22241850952181190779305205 2085173526766986635559863)
          ·
            refine ⟨3127760290150479953339795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085173526766986635559863 3127760290150479953339795)
            ·
              refine ⟨4691640435225719930009693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127760290150479953339795 4691640435225719930009693)
              ·
                refine ⟨1759365163209644973753635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4691640435225719930009693 1759365163209644973753635)
                ·
                  refine ⟨2639047744814467460630453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759365163209644973753635 2639047744814467460630453)
                  ·
                    refine ⟨247410726076356324434105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2639047744814467460630453 247410726076356324434105)
                    ·
                      rfl

theorem cell22_722746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_722746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722746 prefixEnd_722746 := by exact prefixLift 722746
  have htrace : WordTrace (prefixWord ++ tailWord_722746) baseStart_722746 baseEnd_722746 := by
    simpa [prefixWord, tailWord_722746, baseEnd_722746] using wordTrace_append hprefix tailTrace_722746
  have hstable : (prefixWord ++ tailWord_722746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722746).length < 2 ^ (prefixWord ++ tailWord_722746).sum := by decide
  have hdescent : baseEnd_722746 < baseStart_722746 := by decide
  rcases family_descends (prefixWord ++ tailWord_722746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722759 : List Nat := [1, 1, 4, 1, 2, 1, 2, 10]
def baseStart_722759 : Nat := 118140960795 + 722759 * 2 ^ 59
def prefixEnd_722759 : Nat := 4983230072969 + 3 ^ 40 * 722759 * 2
def baseEnd_722759 : Nat := 27490575138003180428785

theorem tailTrace_722759 : CollatzResearch.WordTrace tailWord_722759 prefixEnd_722759 27490575138003180428785 := by
  unfold tailWord_722759
  simp only [CollatzResearch.WordTrace]
  refine ⟨26361186388575055254955331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17574124259050036836636887 26361186388575055254955331)
  ·
    refine ⟨39541779582862582882432997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26361186388575055254955331 39541779582862582882432997)
    ·
      refine ⟨7414083671786734290456187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39541779582862582882432997 7414083671786734290456187)
      ·
        refine ⟨11121125507680101435684281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7414083671786734290456187 11121125507680101435684281)
        ·
          refine ⟨8340844130760076076763211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11121125507680101435684281 8340844130760076076763211)
          ·
            refine ⟨12511266196140114115144817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8340844130760076076763211 12511266196140114115144817)
            ·
              refine ⟨9383449647105085586358613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12511266196140114115144817 9383449647105085586358613)
              ·
                refine ⟨27490575138003180428785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 9383449647105085586358613 27490575138003180428785)
                ·
                  rfl

theorem cell22_722759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 10].length) (baseStart_722759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722759 prefixEnd_722759 := by exact prefixLift 722759
  have htrace : WordTrace (prefixWord ++ tailWord_722759) baseStart_722759 baseEnd_722759 := by
    simpa [prefixWord, tailWord_722759, baseEnd_722759] using wordTrace_append hprefix tailTrace_722759
  have hstable : (prefixWord ++ tailWord_722759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722759).length < 2 ^ (prefixWord ++ tailWord_722759).sum := by decide
  have hdescent : baseEnd_722759 < baseStart_722759 := by decide
  rcases family_descends (prefixWord ++ tailWord_722759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722765 : List Nat := [1, 6, 1, 2, 1, 1, 1, 5, 4]
def baseStart_722765 : Nat := 118140960795 + 722765 * 2 ^ 59
def prefixEnd_722765 : Nat := 4983230072969 + 3 ^ 40 * 722765 * 2
def baseEnd_722765 : Nat := 82472410054882202736349

theorem tailTrace_722765 : CollatzResearch.WordTrace tailWord_722765 prefixEnd_722765 82472410054882202736349 := by
  unfold tailWord_722765
  simp only [CollatzResearch.WordTrace]
  refine ⟨26361405226553318279673749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17574270151035545519782499 26361405226553318279673749)
  ·
    refine ⟨1235690869994686794359707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26361405226553318279673749 1235690869994686794359707)
    ·
      refine ⟨1853536304992030191539561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1235690869994686794359707 1853536304992030191539561)
      ·
        refine ⟨1390152228744022643654671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1853536304992030191539561 1390152228744022643654671)
        ·
          refine ⟨2085228343116033965482007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390152228744022643654671 2085228343116033965482007)
          ·
            refine ⟨3127842514674050948223011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085228343116033965482007 3127842514674050948223011)
            ·
              refine ⟨4691763772011076422334517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127842514674050948223011 4691763772011076422334517)
              ·
                refine ⟨439852853626038414593861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4691763772011076422334517 439852853626038414593861)
                ·
                  refine ⟨82472410054882202736349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439852853626038414593861 82472410054882202736349)
                  ·
                    rfl

theorem cell22_722765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_722765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722765 prefixEnd_722765 := by exact prefixLift 722765
  have htrace : WordTrace (prefixWord ++ tailWord_722765) baseStart_722765 baseEnd_722765 := by
    simpa [prefixWord, tailWord_722765, baseEnd_722765] using wordTrace_append hprefix tailTrace_722765
  have hstable : (prefixWord ++ tailWord_722765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722765).length < 2 ^ (prefixWord ++ tailWord_722765).sum := by decide
  have hdescent : baseEnd_722765 < baseStart_722765 := by decide
  rcases family_descends (prefixWord ++ tailWord_722765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722780 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_722780 : Nat := 118140960795 + 722780 * 2 ^ 59
def prefixEnd_722780 : Nat := 4983230072969 + 3 ^ 40 * 722780 * 2
def baseEnd_722780 : Nat := 247422364971191569084001

theorem tailTrace_722780 : CollatzResearch.WordTrace tailWord_722780 prefixEnd_722780 247422364971191569084001 := by
  unfold tailWord_722780
  simp only [CollatzResearch.WordTrace]
  refine ⟨13180976160749487920734897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17574634880999317227646529 13180976160749487920734897)
  ·
    refine ⟨9885732120562115940551173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13180976160749487920734897 9885732120562115940551173)
    ·
      refine ⟨1853574772605396738853345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9885732120562115940551173 1853574772605396738853345)
      ·
        refine ⟨1390181079454047554140009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1853574772605396738853345 1390181079454047554140009)
        ·
          refine ⟨1042635809590535665605007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390181079454047554140009 1042635809590535665605007)
          ·
            refine ⟨1563953714385803498407511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042635809590535665605007 1563953714385803498407511)
            ·
              refine ⟨2345930571578705247611267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563953714385803498407511 2345930571578705247611267)
              ·
                refine ⟨3518895857368057871416901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2345930571578705247611267 3518895857368057871416901)
                ·
                  refine ⟨659792973256510850890669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3518895857368057871416901 659792973256510850890669)
                  ·
                    refine ⟨247422364971191569084001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659792973256510850890669 247422364971191569084001)
                    ·
                      rfl

theorem cell22_722780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_722780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722780 prefixEnd_722780 := by exact prefixLift 722780
  have htrace : WordTrace (prefixWord ++ tailWord_722780) baseStart_722780 baseEnd_722780 := by
    simpa [prefixWord, tailWord_722780, baseEnd_722780] using wordTrace_append hprefix tailTrace_722780
  have hstable : (prefixWord ++ tailWord_722780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722780).length < 2 ^ (prefixWord ++ tailWord_722780).sum := by decide
  have hdescent : baseEnd_722780 < baseStart_722780 := by decide
  rcases family_descends (prefixWord ++ tailWord_722780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722851 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 3, 4]
def baseStart_722851 : Nat := 118140960795 + 722851 * 2 ^ 59
def prefixEnd_722851 : Nat := 4983230072969 + 3 ^ 40 * 722851 * 2
def baseEnd_722851 : Nat := 247446669722171050558783

theorem tailTrace_722851 : CollatzResearch.WordTrace tailWord_722851 prefixEnd_722851 247446669722171050558783 := by
  unfold tailWord_722851
  simp only [CollatzResearch.WordTrace]
  refine ⟨26364541904241754967304407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17576361269494503311536271 26364541904241754967304407)
  ·
    refine ⟨39546812856362632450956611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26364541904241754967304407 39546812856362632450956611)
    ·
      refine ⟨59320219284543948676434917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39546812856362632450956611 59320219284543948676434917)
      ·
        refine ⟨11122541115851990376831547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59320219284543948676434917 11122541115851990376831547)
        ·
          refine ⟨16683811673777985565247321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11122541115851990376831547 16683811673777985565247321)
          ·
            refine ⟨12512858755333489173935491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16683811673777985565247321 12512858755333489173935491)
            ·
              refine ⟨18769288133000233760903237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12512858755333489173935491 18769288133000233760903237)
              ·
                refine ⟨3519241524937543830169357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18769288133000233760903237 3519241524937543830169357)
                ·
                  refine ⟨1319715571851578936313509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3519241524937543830169357 1319715571851578936313509)
                  ·
                    refine ⟨247446669722171050558783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1319715571851578936313509 247446669722171050558783)
                    ·
                      rfl

theorem cell22_722851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 4].length) (baseStart_722851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722851 prefixEnd_722851 := by exact prefixLift 722851
  have htrace : WordTrace (prefixWord ++ tailWord_722851) baseStart_722851 baseEnd_722851 := by
    simpa [prefixWord, tailWord_722851, baseEnd_722851] using wordTrace_append hprefix tailTrace_722851
  have hstable : (prefixWord ++ tailWord_722851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722851).length < 2 ^ (prefixWord ++ tailWord_722851).sum := by decide
  have hdescent : baseEnd_722851 < baseStart_722851 := by decide
  rcases family_descends (prefixWord ++ tailWord_722851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722855 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 5]
def baseStart_722855 : Nat := 118140960795 + 722855 * 2 ^ 59
def prefixEnd_722855 : Nat := 4983230072969 + 3 ^ 40 * 722855 * 2
def baseEnd_722855 : Nat := 82482679667972124486257

theorem tailTrace_722855 : CollatzResearch.WordTrace tailWord_722855 prefixEnd_722855 82482679667972124486257 := by
  unfold tailWord_722855
  simp only [CollatzResearch.WordTrace]
  refine ⟨26364687796227263650450019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17576458530818175766966679 26364687796227263650450019)
  ·
    refine ⟨39547031694340895475675029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26364687796227263650450019 39547031694340895475675029)
    ·
      refine ⟨1853767110672229475422267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39547031694340895475675029 1853767110672229475422267)
      ·
        refine ⟨2780650666008344213133401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853767110672229475422267 2780650666008344213133401)
        ·
          refine ⟨2085487999506258159850051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2780650666008344213133401 2085487999506258159850051)
          ·
            refine ⟨3128231999259387239775077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085487999506258159850051 3128231999259387239775077)
            ·
              refine ⟨586543499861135107457827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3128231999259387239775077 586543499861135107457827)
              ·
                refine ⟨879815249791702661186741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586543499861135107457827 879815249791702661186741)
                ·
                  refine ⟨82482679667972124486257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 879815249791702661186741 82482679667972124486257)
                  ·
                    rfl

theorem cell22_722855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 5].length) (baseStart_722855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722855 prefixEnd_722855 := by exact prefixLift 722855
  have htrace : WordTrace (prefixWord ++ tailWord_722855) baseStart_722855 baseEnd_722855 := by
    simpa [prefixWord, tailWord_722855, baseEnd_722855] using wordTrace_append hprefix tailTrace_722855
  have hstable : (prefixWord ++ tailWord_722855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722855).length < 2 ^ (prefixWord ++ tailWord_722855).sum := by decide
  have hdescent : baseEnd_722855 < baseStart_722855 := by decide
  rcases family_descends (prefixWord ++ tailWord_722855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722866 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_722866 : Nat := 118140960795 + 722866 * 2 ^ 59
def prefixEnd_722866 : Nat := 4983230072969 + 3 ^ 40 * 722866 * 2
def baseEnd_722866 : Nat := 82483934842905337144579

theorem tailTrace_722866 : CollatzResearch.WordTrace tailWord_722866 prefixEnd_722866 82483934842905337144579 := by
  unfold tailWord_722866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6591272249796853132275113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17576725999458275019400301 6591272249796853132275113)
  ·
    refine ⟨4943454187347639849206335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6591272249796853132275113 4943454187347639849206335)
    ·
      refine ⟨7415181281021459773809503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4943454187347639849206335 7415181281021459773809503)
      ·
        refine ⟨11122771921532189660714255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415181281021459773809503 11122771921532189660714255)
        ·
          refine ⟨16684157882298284491071383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11122771921532189660714255 16684157882298284491071383)
          ·
            refine ⟨25026236823447426736607075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16684157882298284491071383 25026236823447426736607075)
            ·
              refine ⟨37539355235171140104910613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25026236823447426736607075 37539355235171140104910613)
              ·
                refine ⟨1759657276648647192417685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37539355235171140104910613 1759657276648647192417685)
                ·
                  refine ⟨82483934842905337144579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1759657276648647192417685 82483934842905337144579)
                  ·
                    rfl

theorem cell22_722866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_722866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722866 prefixEnd_722866 := by exact prefixLift 722866
  have htrace : WordTrace (prefixWord ++ tailWord_722866) baseStart_722866 baseEnd_722866 := by
    simpa [prefixWord, tailWord_722866, baseEnd_722866] using wordTrace_append hprefix tailTrace_722866
  have hstable : (prefixWord ++ tailWord_722866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722866).length < 2 ^ (prefixWord ++ tailWord_722866).sum := by decide
  have hdescent : baseEnd_722866 < baseStart_722866 := by decide
  rcases family_descends (prefixWord ++ tailWord_722866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722900 : List Nat := [2, 4, 1, 2, 1, 1, 3, 4, 4]
def baseStart_722900 : Nat := 118140960795 + 722900 * 2 ^ 59
def prefixEnd_722900 : Nat := 4983230072969 + 3 ^ 40 * 722900 * 2
def baseEnd_722900 : Nat := 82487814474517085361211

theorem tailTrace_722900 : CollatzResearch.WordTrace tailWord_722900 prefixEnd_722900 82487814474517085361211 := by
  unfold tailWord_722900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13183164540532118167919077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17577552720709490890558769 13183164540532118167919077)
  ·
    refine ⟨2471843351349772156484827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13183164540532118167919077 2471843351349772156484827)
    ·
      refine ⟨3707765027024658234727241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2471843351349772156484827 3707765027024658234727241)
      ·
        refine ⟨2780823770268493676045431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3707765027024658234727241 2780823770268493676045431)
        ·
          refine ⟨4171235655402740514068147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2780823770268493676045431 4171235655402740514068147)
          ·
            refine ⟨6256853483104110771102221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171235655402740514068147 6256853483104110771102221)
            ·
              refine ⟨2346320056164041539163333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6256853483104110771102221 2346320056164041539163333)
              ·
                refine ⟨439935010530757788593125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2346320056164041539163333 439935010530757788593125)
                ·
                  refine ⟨82487814474517085361211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 439935010530757788593125 82487814474517085361211)
                  ·
                    rfl

theorem cell22_722900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_722900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722900 prefixEnd_722900 := by exact prefixLift 722900
  have htrace : WordTrace (prefixWord ++ tailWord_722900) baseStart_722900 baseEnd_722900 := by
    simpa [prefixWord, tailWord_722900, baseEnd_722900] using wordTrace_append hprefix tailTrace_722900
  have hstable : (prefixWord ++ tailWord_722900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722900).length < 2 ^ (prefixWord ++ tailWord_722900).sum := by decide
  have hdescent : baseEnd_722900 < baseStart_722900 := by decide
  rcases family_descends (prefixWord ++ tailWord_722900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722915 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 2, 3]
def baseStart_722915 : Nat := 118140960795 + 722915 * 2 ^ 59
def prefixEnd_722915 : Nat := 4983230072969 + 3 ^ 40 * 722915 * 2
def baseEnd_722915 : Nat := 247468578230096216958587

theorem tailTrace_722915 : CollatzResearch.WordTrace tailWord_722915 prefixEnd_722915 247468578230096216958587 := by
  unfold tailWord_722915
  simp only [CollatzResearch.WordTrace]
  refine ⟨26366876176009893897634199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17577917450673262598422799 26366876176009893897634199)
  ·
    refine ⟨39550314264014840846451299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26366876176009893897634199 39550314264014840846451299)
    ·
      refine ⟨59325471396022261269676949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39550314264014840846451299 59325471396022261269676949)
      ·
        refine ⟨2780881471688543497016107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59325471396022261269676949 2780881471688543497016107)
        ·
          refine ⟨4171322207532815245524161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2780881471688543497016107 4171322207532815245524161)
          ·
            refine ⟨3128491655649611434143121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4171322207532815245524161 3128491655649611434143121)
            ·
              refine ⟨2346368741737208575607341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3128491655649611434143121 2346368741737208575607341)
              ·
                refine ⟨879888278151453215852753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2346368741737208575607341 879888278151453215852753)
                ·
                  refine ⟨659916208613589911889565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 879888278151453215852753 659916208613589911889565)
                  ·
                    refine ⟨247468578230096216958587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659916208613589911889565 247468578230096216958587)
                    ·
                      rfl

theorem cell22_722915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 3].length) (baseStart_722915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722915 prefixEnd_722915 := by exact prefixLift 722915
  have htrace : WordTrace (prefixWord ++ tailWord_722915) baseStart_722915 baseEnd_722915 := by
    simpa [prefixWord, tailWord_722915, baseEnd_722915] using wordTrace_append hprefix tailTrace_722915
  have hstable : (prefixWord ++ tailWord_722915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722915).length < 2 ^ (prefixWord ++ tailWord_722915).sum := by decide
  have hdescent : baseEnd_722915 < baseStart_722915 := by decide
  rcases family_descends (prefixWord ++ tailWord_722915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722971 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 1, 7]
def baseStart_722971 : Nat := 118140960795 + 722971 * 2 ^ 59
def prefixEnd_722971 : Nat := 4983230072969 + 3 ^ 40 * 722971 * 2
def baseEnd_722971 : Nat := 247487748174530737558415

theorem tailTrace_722971 : CollatzResearch.WordTrace tailWord_722971 prefixEnd_722971 247487748174530737558415 := by
  unfold tailWord_722971
  simp only [CollatzResearch.WordTrace]
  refine ⟨26368918663807015461672767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17579279109204676974448511 26368918663807015461672767)
  ·
    refine ⟨39553377995710523192509151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26368918663807015461672767 39553377995710523192509151)
    ·
      refine ⟨59330066993565784788763727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39553377995710523192509151 59330066993565784788763727)
      ·
        refine ⟨88995100490348677183145591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59330066993565784788763727 88995100490348677183145591)
        ·
          refine ⟨133492650735523015774718387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88995100490348677183145591 133492650735523015774718387)
          ·
            refine ⟨200238976103284523662077581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133492650735523015774718387 200238976103284523662077581)
            ·
              refine ⟨75089616038731696373279093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200238976103284523662077581 75089616038731696373279093)
              ·
                refine ⟨7039651503631096534994915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75089616038731696373279093 7039651503631096534994915)
                ·
                  refine ⟨10559477255446644802492373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7039651503631096534994915 10559477255446644802492373)
                  ·
                    refine ⟨247487748174530737558415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10559477255446644802492373 247487748174530737558415)
                    ·
                      rfl

theorem cell22_722971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_722971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722971 prefixEnd_722971 := by exact prefixLift 722971
  have htrace : WordTrace (prefixWord ++ tailWord_722971) baseStart_722971 baseEnd_722971 := by
    simpa [prefixWord, tailWord_722971, baseEnd_722971] using wordTrace_append hprefix tailTrace_722971
  have hstable : (prefixWord ++ tailWord_722971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722971).length < 2 ^ (prefixWord ++ tailWord_722971).sum := by decide
  have hdescent : baseEnd_722971 < baseStart_722971 := by decide
  rcases family_descends (prefixWord ++ tailWord_722971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_722994 : List Nat := [3, 2, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_722994 : Nat := 118140960795 + 722994 * 2 ^ 59
def prefixEnd_722994 : Nat := 4983230072969 + 3 ^ 40 * 722994 * 2
def baseEnd_722994 : Nat := 247495621544566344233345

theorem tailTrace_722994 : CollatzResearch.WordTrace tailWord_722994 prefixEnd_722994 247495621544566344233345 := by
  unfold tailWord_722994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592439385680922597440009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17579838361815793593173357 6592439385680922597440009)
  ·
    refine ⟨4944329539260691948080007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6592439385680922597440009 4944329539260691948080007)
    ·
      refine ⟨7416494308891037922120011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4944329539260691948080007 7416494308891037922120011)
      ·
        refine ⟨11124741463336556883180017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7416494308891037922120011 11124741463336556883180017)
        ·
          refine ⟨8343556097502417662385013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11124741463336556883180017 8343556097502417662385013)
          ·
            refine ⟨782208384140851655848595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8343556097502417662385013 782208384140851655848595)
            ·
              refine ⟨1173312576211277483772893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782208384140851655848595 1173312576211277483772893)
              ·
                refine ⟨439992216079229056414835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1173312576211277483772893 439992216079229056414835)
                ·
                  refine ⟨659988324118843584622253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439992216079229056414835 659988324118843584622253)
                  ·
                    refine ⟨247495621544566344233345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659988324118843584622253 247495621544566344233345)
                    ·
                      rfl

theorem cell22_722994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_722994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_722994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_722994 prefixEnd_722994 := by exact prefixLift 722994
  have htrace : WordTrace (prefixWord ++ tailWord_722994) baseStart_722994 baseEnd_722994 := by
    simpa [prefixWord, tailWord_722994, baseEnd_722994] using wordTrace_append hprefix tailTrace_722994
  have hstable : (prefixWord ++ tailWord_722994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_722994).length < 2 ^ (prefixWord ++ tailWord_722994).sum := by decide
  have hdescent : baseEnd_722994 < baseStart_722994 := by decide
  rcases family_descends (prefixWord ++ tailWord_722994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723033 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_723033 : Nat := 118140960795 + 723033 * 2 ^ 59
def prefixEnd_723033 : Nat := 4983230072969 + 3 ^ 40 * 723033 * 2
def baseEnd_723033 : Nat := 247508972041583242508225

theorem tailTrace_723033 : CollatzResearch.WordTrace tailWord_723033 prefixEnd_723033 247508972041583242508225 := by
  unfold tailWord_723033
  simp only [CollatzResearch.WordTrace]
  refine ⟨26371179989582400050429753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17580786659721600033619835 26371179989582400050429753)
  ·
    refine ⟨19778384992186800037822315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26371179989582400050429753 19778384992186800037822315)
    ·
      refine ⟨29667577488280200056733473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19778384992186800037822315 29667577488280200056733473)
      ·
        refine ⟨22250683116210150042550105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29667577488280200056733473 22250683116210150042550105)
        ·
          refine ⟨16688012337157612531912579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22250683116210150042550105 16688012337157612531912579)
          ·
            refine ⟨25032018505736418797868869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16688012337157612531912579 25032018505736418797868869)
            ·
              refine ⟨4693503469825578524600413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25032018505736418797868869 4693503469825578524600413)
              ·
                refine ⟨1760063801184591946725155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4693503469825578524600413 1760063801184591946725155)
                ·
                  refine ⟨2640095701776887920087733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1760063801184591946725155 2640095701776887920087733)
                  ·
                    refine ⟨247508972041583242508225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2640095701776887920087733 247508972041583242508225)
                    ·
                      rfl

theorem cell22_723033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_723033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723033 prefixEnd_723033 := by exact prefixLift 723033
  have htrace : WordTrace (prefixWord ++ tailWord_723033) baseStart_723033 baseEnd_723033 := by
    simpa [prefixWord, tailWord_723033, baseEnd_723033] using wordTrace_append hprefix tailTrace_723033
  have hstable : (prefixWord ++ tailWord_723033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723033).length < 2 ^ (prefixWord ++ tailWord_723033).sum := by decide
  have hdescent : baseEnd_723033 < baseStart_723033 := by decide
  rcases family_descends (prefixWord ++ tailWord_723033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723037 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_723037 : Nat := 118140960795 + 723037 * 2 ^ 59
def prefixEnd_723037 : Nat := 4983230072969 + 3 ^ 40 * 723037 * 2
def baseEnd_723037 : Nat := 247510341323328565408213

theorem tailTrace_723037 : CollatzResearch.WordTrace tailWord_723037 prefixEnd_723037 247510341323328565408213 := by
  unfold tailWord_723037
  simp only [CollatzResearch.WordTrace]
  refine ⟨26371325881567908733575365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17580883921045272489050243 26371325881567908733575365)
  ·
    refine ⟨4944623602793982887545381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26371325881567908733575365 4944623602793982887545381)
    ·
      refine ⟨927116925523871791414759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4944623602793982887545381 927116925523871791414759)
      ·
        refine ⟨1390675388285807687122139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927116925523871791414759 1390675388285807687122139)
        ·
          refine ⟨2086013082428711530683209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390675388285807687122139 2086013082428711530683209)
          ·
            refine ⟨1564509811821533648012407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2086013082428711530683209 1564509811821533648012407)
            ·
              refine ⟨2346764717732300472018611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1564509811821533648012407 2346764717732300472018611)
              ·
                refine ⟨3520147076598450708027917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2346764717732300472018611 3520147076598450708027917)
                ·
                  refine ⟨1320055153724419015510469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3520147076598450708027917 1320055153724419015510469)
                  ·
                    refine ⟨247510341323328565408213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1320055153724419015510469 247510341323328565408213)
                    ·
                      rfl

theorem cell22_723037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_723037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723037 prefixEnd_723037 := by exact prefixLift 723037
  have htrace : WordTrace (prefixWord ++ tailWord_723037) baseStart_723037 baseEnd_723037 := by
    simpa [prefixWord, tailWord_723037, baseEnd_723037] using wordTrace_append hprefix tailTrace_723037
  have hstable : (prefixWord ++ tailWord_723037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723037).length < 2 ^ (prefixWord ++ tailWord_723037).sum := by decide
  have hdescent : baseEnd_723037 < baseStart_723037 := by decide
  rcases family_descends (prefixWord ++ tailWord_723037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723065 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_723065 : Nat := 118140960795 + 723065 * 2 ^ 59
def prefixEnd_723065 : Nat := 4983230072969 + 3 ^ 40 * 723065 * 2
def baseEnd_723065 : Nat := 247519926295545825708127

theorem tailTrace_723065 : CollatzResearch.WordTrace tailWord_723065 prefixEnd_723065 247519926295545825708127 := by
  unfold tailWord_723065
  simp only [CollatzResearch.WordTrace]
  refine ⟨26372347125466469515594649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17581564750310979677063099 26372347125466469515594649)
  ·
    refine ⟨19779260344099852136695987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26372347125466469515594649 19779260344099852136695987)
    ·
      refine ⟨29668890516149778205043981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19779260344099852136695987 29668890516149778205043981)
      ·
        refine ⟨11125833943556166826891493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29668890516149778205043981 11125833943556166826891493)
        ·
          refine ⟨2086093864416781280042155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11125833943556166826891493 2086093864416781280042155)
          ·
            refine ⟨3129140796625171920063233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086093864416781280042155 3129140796625171920063233)
            ·
              refine ⟨2346855597468878940047425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3129140796625171920063233 2346855597468878940047425)
              ·
                refine ⟨1760141698101659205035569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2346855597468878940047425 1760141698101659205035569)
                ·
                  refine ⟨1320106273576244403776677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1760141698101659205035569 1320106273576244403776677)
                  ·
                    refine ⟨247519926295545825708127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1320106273576244403776677 247519926295545825708127)
                    ·
                      rfl

theorem cell22_723065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_723065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723065 prefixEnd_723065 := by exact prefixLift 723065
  have htrace : WordTrace (prefixWord ++ tailWord_723065) baseStart_723065 baseEnd_723065 := by
    simpa [prefixWord, tailWord_723065, baseEnd_723065] using wordTrace_append hprefix tailTrace_723065
  have hstable : (prefixWord ++ tailWord_723065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723065).length < 2 ^ (prefixWord ++ tailWord_723065).sum := by decide
  have hdescent : baseEnd_723065 < baseStart_723065 := by decide
  rcases family_descends (prefixWord ++ tailWord_723065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723069 : List Nat := [1, 4, 1, 1, 3, 4, 2, 2, 4]
def baseStart_723069 : Nat := 118140960795 + 723069 * 2 ^ 59
def prefixEnd_723069 : Nat := 4983230072969 + 3 ^ 40 * 723069 * 2
def baseEnd_723069 : Nat := 82507098525763716202705

theorem tailTrace_723069 : CollatzResearch.WordTrace tailWord_723069 prefixEnd_723069 82507098525763716202705 := by
  unfold tailWord_723069
  simp only [CollatzResearch.WordTrace]
  refine ⟨26372493017451978198740261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17581662011634652132493507 26372493017451978198740261)
  ·
    refine ⟨4944842440772245912263799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26372493017451978198740261 4944842440772245912263799)
    ·
      refine ⟨7417263661158368868395699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4944842440772245912263799 7417263661158368868395699)
      ·
        refine ⟨11125895491737553302593549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7417263661158368868395699 11125895491737553302593549)
        ·
          refine ⟨4172210809401582488472581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11125895491737553302593549 4172210809401582488472581)
          ·
            refine ⟨782289526762796716588609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4172210809401582488472581 782289526762796716588609)
            ·
              refine ⟨586717145072097537441457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782289526762796716588609 586717145072097537441457)
              ·
                refine ⟨440037858804073153081093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586717145072097537441457 440037858804073153081093)
                ·
                  refine ⟨82507098525763716202705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 440037858804073153081093 82507098525763716202705)
                  ·
                    rfl

theorem cell22_723069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_723069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723069 prefixEnd_723069 := by exact prefixLift 723069
  have htrace : WordTrace (prefixWord ++ tailWord_723069) baseStart_723069 baseEnd_723069 := by
    simpa [prefixWord, tailWord_723069, baseEnd_723069] using wordTrace_append hprefix tailTrace_723069
  have hstable : (prefixWord ++ tailWord_723069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723069).length < 2 ^ (prefixWord ++ tailWord_723069).sum := by decide
  have hdescent : baseEnd_723069 < baseStart_723069 := by decide
  rcases family_descends (prefixWord ++ tailWord_723069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723080 : List Nat := [2, 1, 3, 4, 1, 1, 3, 7]
def baseStart_723080 : Nat := 118140960795 + 723080 * 2 ^ 59
def prefixEnd_723080 : Nat := 4983230072969 + 3 ^ 40 * 723080 * 2
def baseEnd_723080 : Nat := 27502784566898976287009

theorem tailTrace_723080 : CollatzResearch.WordTrace tailWord_723080 prefixEnd_723080 27502784566898976287009 := by
  unfold tailWord_723080
  simp only [CollatzResearch.WordTrace]
  refine ⟨13186447110206063538695347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17581929480274751384927129 13186447110206063538695347)
  ·
    refine ⟨19779670665309095308043021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13186447110206063538695347 19779670665309095308043021)
    ·
      refine ⟨7417376499490910740516133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19779670665309095308043021 7417376499490910740516133)
      ·
        refine ⟨1390758093654545763846775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7417376499490910740516133 1390758093654545763846775)
        ·
          refine ⟨2086137140481818645770163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390758093654545763846775 2086137140481818645770163)
          ·
            refine ⟨3129205710722727968655245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2086137140481818645770163 3129205710722727968655245)
            ·
              refine ⟨1173452141521022988245717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3129205710722727968655245 1173452141521022988245717)
              ·
                refine ⟨27502784566898976287009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1173452141521022988245717 27502784566898976287009)
                ·
                  rfl

theorem cell22_723080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 7].length) (baseStart_723080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723080 prefixEnd_723080 := by exact prefixLift 723080
  have htrace : WordTrace (prefixWord ++ tailWord_723080) baseStart_723080 baseEnd_723080 := by
    simpa [prefixWord, tailWord_723080, baseEnd_723080] using wordTrace_append hprefix tailTrace_723080
  have hstable : (prefixWord ++ tailWord_723080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723080).length < 2 ^ (prefixWord ++ tailWord_723080).sum := by decide
  have hdescent : baseEnd_723080 < baseStart_723080 := by decide
  rcases family_descends (prefixWord ++ tailWord_723080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723093 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_723093 : Nat := 118140960795 + 723093 * 2 ^ 59
def prefixEnd_723093 : Nat := 4983230072969 + 3 ^ 40 * 723093 * 2
def baseEnd_723093 : Nat := 247529511267763086008041

theorem tailTrace_723093 : CollatzResearch.WordTrace tailWord_723093 prefixEnd_723093 247529511267763086008041 := by
  unfold tailWord_723093
  simp only [CollatzResearch.WordTrace]
  refine ⟨26373368369365030297613933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17582245579576686865075955 26373368369365030297613933)
  ·
    refine ⟨9890013138511886361605225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26373368369365030297613933 9890013138511886361605225)
    ·
      refine ⟨7417509853883914771203919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9890013138511886361605225 7417509853883914771203919)
      ·
        refine ⟨11126264780825872156805879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7417509853883914771203919 11126264780825872156805879)
        ·
          refine ⟨16689397171238808235208819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11126264780825872156805879 16689397171238808235208819)
          ·
            refine ⟨25034095756858212352813229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16689397171238808235208819 25034095756858212352813229)
            ·
              refine ⟨9387785908821829632304961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25034095756858212352813229 9387785908821829632304961)
              ·
                refine ⟨7040839431616372224228721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9387785908821829632304961 7040839431616372224228721)
                ·
                  refine ⟨5280629573712279168171541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7040839431616372224228721 5280629573712279168171541)
                  ·
                    refine ⟨247529511267763086008041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5280629573712279168171541 247529511267763086008041)
                    ·
                      rfl

theorem cell22_723093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_723093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723093 prefixEnd_723093 := by exact prefixLift 723093
  have htrace : WordTrace (prefixWord ++ tailWord_723093) baseStart_723093 baseEnd_723093 := by
    simpa [prefixWord, tailWord_723093, baseEnd_723093] using wordTrace_append hprefix tailTrace_723093
  have hstable : (prefixWord ++ tailWord_723093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723093).length < 2 ^ (prefixWord ++ tailWord_723093).sum := by decide
  have hdescent : baseEnd_723093 < baseStart_723093 := by decide
  rcases family_descends (prefixWord ++ tailWord_723093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723118 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_723118 : Nat := 118140960795 + 723118 * 2 ^ 59
def prefixEnd_723118 : Nat := 4983230072969 + 3 ^ 40 * 723118 * 2
def baseEnd_723118 : Nat := 247538069278671354132965

theorem tailTrace_723118 : CollatzResearch.WordTrace tailWord_723118 prefixEnd_723118 247538069278671354132965 := by
  unfold tailWord_723118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296785024284307445909251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17582853462849639711516005 3296785024284307445909251)
  ·
    refine ⟨4945177536426461168863877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3296785024284307445909251 4945177536426461168863877)
    ·
      refine ⟨927220788079961469161977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4945177536426461168863877 927220788079961469161977)
      ·
        refine ⟨695415591059971101871483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 927220788079961469161977 695415591059971101871483)
        ·
          refine ⟨1043123386589956652807225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695415591059971101871483 1043123386589956652807225)
          ·
            refine ⟨782342539942467489605419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1043123386589956652807225 782342539942467489605419)
            ·
              refine ⟨1173513809913701234408129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782342539942467489605419 1173513809913701234408129)
              ·
                refine ⟨880135357435275925806097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173513809913701234408129 880135357435275925806097)
                ·
                  refine ⟨660101518076456944354573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 880135357435275925806097 660101518076456944354573)
                  ·
                    refine ⟨247538069278671354132965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 660101518076456944354573 247538069278671354132965)
                    ·
                      rfl

theorem cell22_723118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_723118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723118 prefixEnd_723118 := by exact prefixLift 723118
  have htrace : WordTrace (prefixWord ++ tailWord_723118) baseStart_723118 baseEnd_723118 := by
    simpa [prefixWord, tailWord_723118, baseEnd_723118] using wordTrace_append hprefix tailTrace_723118
  have hstable : (prefixWord ++ tailWord_723118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723118).length < 2 ^ (prefixWord ++ tailWord_723118).sum := by decide
  have hdescent : baseEnd_723118 < baseStart_723118 := by decide
  rcases family_descends (prefixWord ++ tailWord_723118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723217 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_723217 : Nat := 118140960795 + 723217 * 2 ^ 59
def prefixEnd_723217 : Nat := 4983230072969 + 3 ^ 40 * 723217 * 2
def baseEnd_723217 : Nat := 247571959001868095907661

theorem tailTrace_723217 : CollatzResearch.WordTrace tailWord_723217 prefixEnd_723217 247571959001868095907661 := by
  unfold tailWord_723217
  simp only [CollatzResearch.WordTrace]
  refine ⟨26377891020915799475127905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17585260680610532983418603 26377891020915799475127905)
  ·
    refine ⟨19783418265686849606345929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26377891020915799475127905 19783418265686849606345929)
    ·
      refine ⟨14837563699265137204759447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19783418265686849606345929 14837563699265137204759447)
      ·
        refine ⟨22256345548897705807139171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14837563699265137204759447 22256345548897705807139171)
        ·
          refine ⟨33384518323346558710708757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22256345548897705807139171 33384518323346558710708757)
          ·
            refine ⟨1564899296406869939564473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33384518323346558710708757 1564899296406869939564473)
            ·
              refine ⟨1173674472305152454673355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1564899296406869939564473 1173674472305152454673355)
              ·
                refine ⟨1760511708457728682010033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173674472305152454673355 1760511708457728682010033)
                ·
                  refine ⟨1320383781343296511507525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1760511708457728682010033 1320383781343296511507525)
                  ·
                    refine ⟨247571959001868095907661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1320383781343296511507525 247571959001868095907661)
                    ·
                      rfl

theorem cell22_723217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_723217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723217 prefixEnd_723217 := by exact prefixLift 723217
  have htrace : WordTrace (prefixWord ++ tailWord_723217) baseStart_723217 baseEnd_723217 := by
    simpa [prefixWord, tailWord_723217, baseEnd_723217] using wordTrace_append hprefix tailTrace_723217
  have hstable : (prefixWord ++ tailWord_723217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723217).length < 2 ^ (prefixWord ++ tailWord_723217).sum := by decide
  have hdescent : baseEnd_723217 < baseStart_723217 := by decide
  rcases family_descends (prefixWord ++ tailWord_723217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723249 : List Nat := [1, 2, 2, 3, 5, 1, 1, 7]
def baseStart_723249 : Nat := 118140960795 + 723249 * 2 ^ 59
def prefixEnd_723249 : Nat := 4983230072969 + 3 ^ 40 * 723249 * 2
def baseEnd_723249 : Nat := 27509212583981186567507

theorem tailTrace_723249 : CollatzResearch.WordTrace tailWord_723249 prefixEnd_723249 27509212583981186567507 := by
  unfold tailWord_723249
  simp only [CollatzResearch.WordTrace]
  refine ⟨26379058156799868940292801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17586038771199912626861867 26379058156799868940292801)
  ·
    refine ⟨19784293617599901705219601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26379058156799868940292801 19784293617599901705219601)
    ·
      refine ⟨14838220213199926278914701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19784293617599901705219601 14838220213199926278914701)
      ·
        refine ⟨5564332579949972354593013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14838220213199926278914701 5564332579949972354593013)
        ·
          refine ⟨521656179370309908243095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5564332579949972354593013 521656179370309908243095)
          ·
            refine ⟨782484269055464862364643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521656179370309908243095 782484269055464862364643)
            ·
              refine ⟨1173726403583197293546965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782484269055464862364643 1173726403583197293546965)
              ·
                refine ⟨27509212583981186567507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1173726403583197293546965 27509212583981186567507)
                ·
                  rfl

theorem cell22_723249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 7].length) (baseStart_723249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723249 prefixEnd_723249 := by exact prefixLift 723249
  have htrace : WordTrace (prefixWord ++ tailWord_723249) baseStart_723249 baseEnd_723249 := by
    simpa [prefixWord, tailWord_723249, baseEnd_723249] using wordTrace_append hprefix tailTrace_723249
  have hstable : (prefixWord ++ tailWord_723249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723249).length < 2 ^ (prefixWord ++ tailWord_723249).sum := by decide
  have hdescent : baseEnd_723249 < baseStart_723249 := by decide
  rcases family_descends (prefixWord ++ tailWord_723249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723268 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_723268 : Nat := 118140960795 + 723268 * 2 ^ 59
def prefixEnd_723268 : Nat := 4983230072969 + 3 ^ 40 * 723268 * 2
def baseEnd_723268 : Nat := 247589417344120962882505

theorem tailTrace_723268 : CollatzResearch.WordTrace tailWord_723268 prefixEnd_723268 247589417344120962882505 := by
  unfold tailWord_723268
  simp only [CollatzResearch.WordTrace]
  refine ⟨13189875571865517592617229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17586500762487356790156305 13189875571865517592617229)
  ·
    refine ⟨4946203339449569097231461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13189875571865517592617229 4946203339449569097231461)
    ·
      refine ⟨927413126146794205730899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4946203339449569097231461 927413126146794205730899)
      ·
        refine ⟨1391119689220191308596349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927413126146794205730899 1391119689220191308596349)
        ·
          refine ⟨521669883457571740723631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1391119689220191308596349 521669883457571740723631)
          ·
            refine ⟨782504825186357611085447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521669883457571740723631 782504825186357611085447)
            ·
              refine ⟨1173757237779536416628171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782504825186357611085447 1173757237779536416628171)
              ·
                refine ⟨1760635856669304624942257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173757237779536416628171 1760635856669304624942257)
                ·
                  refine ⟨1320476892501978468706693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1760635856669304624942257 1320476892501978468706693)
                  ·
                    refine ⟨247589417344120962882505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1320476892501978468706693 247589417344120962882505)
                    ·
                      rfl

theorem cell22_723268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_723268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723268 prefixEnd_723268 := by exact prefixLift 723268
  have htrace : WordTrace (prefixWord ++ tailWord_723268) baseStart_723268 baseEnd_723268 := by
    simpa [prefixWord, tailWord_723268, baseEnd_723268] using wordTrace_append hprefix tailTrace_723268
  have hstable : (prefixWord ++ tailWord_723268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723268).length < 2 ^ (prefixWord ++ tailWord_723268).sum := by decide
  have hdescent : baseEnd_723268 < baseStart_723268 := by decide
  rcases family_descends (prefixWord ++ tailWord_723268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723281 : List Nat := [1, 2, 2, 1, 4, 3, 2, 3, 1, 3]
def baseStart_723281 : Nat := 118140960795 + 723281 * 2 ^ 59
def prefixEnd_723281 : Nat := 4983230072969 + 3 ^ 40 * 723281 * 2
def baseEnd_723281 : Nat := 247593867509793262307465

theorem tailTrace_723281 : CollatzResearch.WordTrace tailWord_723281 prefixEnd_723281 247593867509793262307465 := by
  unfold tailWord_723281
  simp only [CollatzResearch.WordTrace]
  refine ⟨26380225292683938405457697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17586816861789292270305131 26380225292683938405457697)
  ·
    refine ⟨19785168969512953804093273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26380225292683938405457697 19785168969512953804093273)
    ·
      refine ⟨14838876727134715353069955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19785168969512953804093273 14838876727134715353069955)
      ·
        refine ⟨22258315090702073029604933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14838876727134715353069955 22258315090702073029604933)
        ·
          refine ⟨4173434079506638693050925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22258315090702073029604933 4173434079506638693050925)
          ·
            refine ⟨1565037779814989509894097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4173434079506638693050925 1565037779814989509894097)
            ·
              refine ⟨1173778334861242132420573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1565037779814989509894097 1173778334861242132420573)
              ·
                refine ⟨440166875572965799657715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1173778334861242132420573 440166875572965799657715)
                ·
                  refine ⟨660250313359448699486573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440166875572965799657715 660250313359448699486573)
                  ·
                    refine ⟨247593867509793262307465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 660250313359448699486573 247593867509793262307465)
                    ·
                      rfl

theorem cell22_723281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_723281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723281 prefixEnd_723281 := by exact prefixLift 723281
  have htrace : WordTrace (prefixWord ++ tailWord_723281) baseStart_723281 baseEnd_723281 := by
    simpa [prefixWord, tailWord_723281, baseEnd_723281] using wordTrace_append hprefix tailTrace_723281
  have hstable : (prefixWord ++ tailWord_723281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723281).length < 2 ^ (prefixWord ++ tailWord_723281).sum := by decide
  have hdescent : baseEnd_723281 < baseStart_723281 := by decide
  rcases family_descends (prefixWord ++ tailWord_723281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723339 : List Nat := [1, 1, 1, 1, 4, 4, 3, 3, 4]
def baseStart_723339 : Nat := 118140960795 + 723339 * 2 ^ 59
def prefixEnd_723339 : Nat := 4983230072969 + 3 ^ 40 * 723339 * 2
def baseEnd_723339 : Nat := 82537907365033481452429

theorem tailTrace_723339 : CollatzResearch.WordTrace tailWord_723339 prefixEnd_723339 82537907365033481452429 := by
  unfold tailWord_723339
  simp only [CollatzResearch.WordTrace]
  refine ⟨26382340726473814311069071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17588227150982542874046047 26382340726473814311069071)
  ·
    refine ⟨39573511089710721466603607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26382340726473814311069071 39573511089710721466603607)
    ·
      refine ⟨59360266634566082199905411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39573511089710721466603607 59360266634566082199905411)
      ·
        refine ⟨89040399951849123299858117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59360266634566082199905411 89040399951849123299858117)
        ·
          refine ⟨16695074990971710618723397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89040399951849123299858117 16695074990971710618723397)
          ·
            refine ⟨3130326560807195741010637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16695074990971710618723397 3130326560807195741010637)
            ·
              refine ⟨1173872460302698402878989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3130326560807195741010637 1173872460302698402878989)
              ·
                refine ⟨440202172613511901079621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1173872460302698402878989 440202172613511901079621)
                ·
                  refine ⟨82537907365033481452429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 440202172613511901079621 82537907365033481452429)
                  ·
                    rfl

theorem cell22_723339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 3, 4].length) (baseStart_723339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723339 prefixEnd_723339 := by exact prefixLift 723339
  have htrace : WordTrace (prefixWord ++ tailWord_723339) baseStart_723339 baseEnd_723339 := by
    simpa [prefixWord, tailWord_723339, baseEnd_723339] using wordTrace_append hprefix tailTrace_723339
  have hstable : (prefixWord ++ tailWord_723339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723339).length < 2 ^ (prefixWord ++ tailWord_723339).sum := by decide
  have hdescent : baseEnd_723339 < baseStart_723339 := by decide
  rcases family_descends (prefixWord ++ tailWord_723339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723354 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_723354 : Nat := 118140960795 + 723354 * 2 ^ 59
def prefixEnd_723354 : Nat := 4983230072969 + 3 ^ 40 * 723354 * 2
def baseEnd_723354 : Nat := 247618856901645405232241

theorem tailTrace_723354 : CollatzResearch.WordTrace tailWord_723354 prefixEnd_723354 247618856901645405232241 := by
  unfold tailWord_723354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6595721955354867968216279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17588591880946314581910077 6595721955354867968216279)
  ·
    refine ⟨9893582933032301952324419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6595721955354867968216279 9893582933032301952324419)
    ·
      refine ⟨14840374399548452928486629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9893582933032301952324419 14840374399548452928486629)
      ·
        refine ⟨2782570199915334924091243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14840374399548452928486629 2782570199915334924091243)
        ·
          refine ⟨4173855299873002386136865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782570199915334924091243 4173855299873002386136865)
          ·
            refine ⟨3130391474904751789602649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4173855299873002386136865 3130391474904751789602649)
            ·
              refine ⟨2347793606178563842201987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3130391474904751789602649 2347793606178563842201987)
              ·
                refine ⟨3521690409267845763302981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2347793606178563842201987 3521690409267845763302981)
                ·
                  refine ⟨660316951737721080619309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3521690409267845763302981 660316951737721080619309)
                  ·
                    refine ⟨247618856901645405232241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 660316951737721080619309 247618856901645405232241)
                    ·
                      rfl

theorem cell22_723354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_723354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723354 prefixEnd_723354 := by exact prefixLift 723354
  have htrace : WordTrace (prefixWord ++ tailWord_723354) baseStart_723354 baseEnd_723354 := by
    simpa [prefixWord, tailWord_723354, baseEnd_723354] using wordTrace_append hprefix tailTrace_723354
  have hstable : (prefixWord ++ tailWord_723354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723354).length < 2 ^ (prefixWord ++ tailWord_723354).sum := by decide
  have hdescent : baseEnd_723354 < baseStart_723354 := by decide
  rcases family_descends (prefixWord ++ tailWord_723354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723367 : List Nat := [1, 1, 6, 1, 1, 2, 1, 9]
def baseStart_723367 : Nat := 118140960795 + 723367 * 2 ^ 59
def prefixEnd_723367 : Nat := 4983230072969 + 3 ^ 40 * 723367 * 2
def baseEnd_723367 : Nat := 27513700785257522739689

theorem tailTrace_723367 : CollatzResearch.WordTrace tailWord_723367 prefixEnd_723367 27513700785257522739689 := by
  unfold tailWord_723367
  simp only [CollatzResearch.WordTrace]
  refine ⟨26383361970372375093088355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17588907980248250062058903 26383361970372375093088355)
  ·
    refine ⟨39575042955558562639632533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26383361970372375093088355 39575042955558562639632533)
    ·
      refine ⟨1855080138541807623732775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39575042955558562639632533 1855080138541807623732775)
      ·
        refine ⟨2782620207812711435599163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855080138541807623732775 2782620207812711435599163)
        ·
          refine ⟨4173930311719067153398745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782620207812711435599163 4173930311719067153398745)
          ·
            refine ⟨3130447733789300365049059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4173930311719067153398745 3130447733789300365049059)
            ·
              refine ⟨4695671600683950547573589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130447733789300365049059 4695671600683950547573589)
              ·
                refine ⟨27513700785257522739689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4695671600683950547573589 27513700785257522739689)
                ·
                  rfl

theorem cell22_723367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 9].length) (baseStart_723367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723367 prefixEnd_723367 := by exact prefixLift 723367
  have htrace : WordTrace (prefixWord ++ tailWord_723367) baseStart_723367 baseEnd_723367 := by
    simpa [prefixWord, tailWord_723367, baseEnd_723367] using wordTrace_append hprefix tailTrace_723367
  have hstable : (prefixWord ++ tailWord_723367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723367).length < 2 ^ (prefixWord ++ tailWord_723367).sum := by decide
  have hdescent : baseEnd_723367 < baseStart_723367 := by decide
  rcases family_descends (prefixWord ++ tailWord_723367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723414 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_723414 : Nat := 118140960795 + 723414 * 2 ^ 59
def prefixEnd_723414 : Nat := 4983230072969 + 3 ^ 40 * 723414 * 2
def baseEnd_723414 : Nat := 247639396127825248732057

theorem tailTrace_723414 : CollatzResearch.WordTrace tailWord_723414 prefixEnd_723414 247639396127825248732057 := by
  unfold tailWord_723414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649067262575131382503081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17590050800801401413366197 1649067262575131382503081)
  ·
    refine ⟨1236800446931348536877311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1649067262575131382503081 1236800446931348536877311)
    ·
      refine ⟨1855200670397022805315967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236800446931348536877311 1855200670397022805315967)
      ·
        refine ⟨2782801005595534207973951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855200670397022805315967 2782801005595534207973951)
        ·
          refine ⟨4174201508393301311960927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2782801005595534207973951 4174201508393301311960927)
          ·
            refine ⟨6261302262589951967941391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174201508393301311960927 6261302262589951967941391)
            ·
              refine ⟨9391953393884927951912087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6261302262589951967941391 9391953393884927951912087)
              ·
                refine ⟨14087930090827391927868131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9391953393884927951912087 14087930090827391927868131)
                ·
                  refine ⟨21131895136241087891802197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14087930090827391927868131 21131895136241087891802197)
                  ·
                    refine ⟨247639396127825248732057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21131895136241087891802197 247639396127825248732057)
                    ·
                      rfl

theorem cell22_723414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_723414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723414 prefixEnd_723414 := by exact prefixLift 723414
  have htrace : WordTrace (prefixWord ++ tailWord_723414) baseStart_723414 baseEnd_723414 := by
    simpa [prefixWord, tailWord_723414, baseEnd_723414] using wordTrace_append hprefix tailTrace_723414
  have hstable : (prefixWord ++ tailWord_723414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723414).length < 2 ^ (prefixWord ++ tailWord_723414).sum := by decide
  have hdescent : baseEnd_723414 < baseStart_723414 := by decide
  rcases family_descends (prefixWord ++ tailWord_723414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723459 : List Nat := [1, 1, 1, 3, 2, 1, 5, 3, 1, 4]
def baseStart_723459 : Nat := 118140960795 + 723459 * 2 ^ 59
def prefixEnd_723459 : Nat := 4983230072969 + 3 ^ 40 * 723459 * 2
def baseEnd_723459 : Nat := 247654800547460131356919

theorem tailTrace_723459 : CollatzResearch.WordTrace tailWord_723459 prefixEnd_723459 247654800547460131356919 := by
  unfold tailWord_723459
  simp only [CollatzResearch.WordTrace]
  refine ⟨26386717486039074805437431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17591144990692716536958287 26386717486039074805437431)
  ·
    refine ⟨39580076229058612208156147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26386717486039074805437431 39580076229058612208156147)
    ·
      refine ⟨59370114343587918312234221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39580076229058612208156147 59370114343587918312234221)
      ·
        refine ⟨22263792878845469367087833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59370114343587918312234221 22263792878845469367087833)
        ·
          refine ⟨16697844659134102025315875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22263792878845469367087833 16697844659134102025315875)
          ·
            refine ⟨25046766988701153037973813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16697844659134102025315875 25046766988701153037973813)
            ·
              refine ⟨2348134405190733097310045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25046766988701153037973813 2348134405190733097310045)
              ·
                refine ⟨880550401946524911491267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2348134405190733097310045 880550401946524911491267)
                ·
                  refine ⟨1320825602919787367236901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880550401946524911491267 1320825602919787367236901)
                  ·
                    refine ⟨247654800547460131356919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1320825602919787367236901 247654800547460131356919)
                    ·
                      rfl

theorem cell22_723459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 4].length) (baseStart_723459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723459 prefixEnd_723459 := by exact prefixLift 723459
  have htrace : WordTrace (prefixWord ++ tailWord_723459) baseStart_723459 baseEnd_723459 := by
    simpa [prefixWord, tailWord_723459, baseEnd_723459] using wordTrace_append hprefix tailTrace_723459
  have hstable : (prefixWord ++ tailWord_723459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723459).length < 2 ^ (prefixWord ++ tailWord_723459).sum := by decide
  have hdescent : baseEnd_723459 < baseStart_723459 := by decide
  rcases family_descends (prefixWord ++ tailWord_723459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723463 : List Nat := [1, 1, 4, 3, 4, 1, 1, 2, 5]
def baseStart_723463 : Nat := 118140960795 + 723463 * 2 ^ 59
def prefixEnd_723463 : Nat := 4983230072969 + 3 ^ 40 * 723463 * 2
def baseEnd_723463 : Nat := 82552056609735151418969

theorem tailTrace_723463 : CollatzResearch.WordTrace tailWord_723463 prefixEnd_723463 82552056609735151418969 := by
  unfold tailWord_723463
  simp only [CollatzResearch.WordTrace]
  refine ⟨26386863378024583488583043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17591242252016388992388695 26386863378024583488583043)
  ·
    refine ⟨39580295067036875232874565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26386863378024583488583043 39580295067036875232874565)
    ·
      refine ⟨7421305325069414106163981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39580295067036875232874565 7421305325069414106163981)
      ·
        refine ⟨2782989496901030289811493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7421305325069414106163981 2782989496901030289811493)
        ·
          refine ⟨521810530668943179339655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2782989496901030289811493 521810530668943179339655)
          ·
            refine ⟨782715796003414769009483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521810530668943179339655 782715796003414769009483)
            ·
              refine ⟨1174073694005122153514225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782715796003414769009483 1174073694005122153514225)
              ·
                refine ⟨880555270503841615135669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174073694005122153514225 880555270503841615135669)
                ·
                  refine ⟨82552056609735151418969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 880555270503841615135669 82552056609735151418969)
                  ·
                    rfl

theorem cell22_723463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 5].length) (baseStart_723463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723463 prefixEnd_723463 := by exact prefixLift 723463
  have htrace : WordTrace (prefixWord ++ tailWord_723463) baseStart_723463 baseEnd_723463 := by
    simpa [prefixWord, tailWord_723463, baseEnd_723463] using wordTrace_append hprefix tailTrace_723463
  have hstable : (prefixWord ++ tailWord_723463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723463).length < 2 ^ (prefixWord ++ tailWord_723463).sum := by decide
  have hdescent : baseEnd_723463 < baseStart_723463 := by decide
  rcases family_descends (prefixWord ++ tailWord_723463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723501 : List Nat := [1, 5, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_723501 : Nat := 118140960795 + 723501 * 2 ^ 59
def prefixEnd_723501 : Nat := 4983230072969 + 3 ^ 40 * 723501 * 2
def baseEnd_723501 : Nat := 247669178005786021806791

theorem tailTrace_723501 : CollatzResearch.WordTrace tailWord_723501 prefixEnd_723501 247669178005786021806791 := by
  unfold tailWord_723501
  simp only [CollatzResearch.WordTrace]
  refine ⟨26388249351886915978466357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17592166234591277318977571 26388249351886915978466357)
  ·
    refine ⟨2473898376739398372981221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26388249351886915978466357 2473898376739398372981221)
    ·
      refine ⟨463855945638637194933979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2473898376739398372981221 463855945638637194933979)
      ·
        refine ⟨695783918457955792400969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463855945638637194933979 695783918457955792400969)
        ·
          refine ⟨521837938843466844300727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 695783918457955792400969 521837938843466844300727)
          ·
            refine ⟨782756908265200266451091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521837938843466844300727 782756908265200266451091)
            ·
              refine ⟨1174135362397800399676637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782756908265200266451091 1174135362397800399676637)
              ·
                refine ⟨440300760899175149878739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1174135362397800399676637 440300760899175149878739)
                ·
                  refine ⟨660451141348762724818109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440300760899175149878739 660451141348762724818109)
                  ·
                    refine ⟨247669178005786021806791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 660451141348762724818109 247669178005786021806791)
                    ·
                      rfl

theorem cell22_723501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_723501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723501 prefixEnd_723501 := by exact prefixLift 723501
  have htrace : WordTrace (prefixWord ++ tailWord_723501) baseStart_723501 baseEnd_723501 := by
    simpa [prefixWord, tailWord_723501, baseEnd_723501] using wordTrace_append hprefix tailTrace_723501
  have hstable : (prefixWord ++ tailWord_723501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723501).length < 2 ^ (prefixWord ++ tailWord_723501).sum := by decide
  have hdescent : baseEnd_723501 < baseStart_723501 := by decide
  rcases family_descends (prefixWord ++ tailWord_723501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723521 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_723521 : Nat := 118140960795 + 723521 * 2 ^ 59
def prefixEnd_723521 : Nat := 4983230072969 + 3 ^ 40 * 723521 * 2
def baseEnd_723521 : Nat := 247676024414512636306729

theorem tailTrace_723521 : CollatzResearch.WordTrace tailWord_723521 prefixEnd_723521 247676024414512636306729 := by
  unfold tailWord_723521
  simp only [CollatzResearch.WordTrace]
  refine ⟨26388978811814459394194417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17592652541209639596129611 26388978811814459394194417)
  ·
    refine ⟨19791734108860844545645813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26388978811814459394194417 19791734108860844545645813)
    ·
      refine ⟨1855475072705704176154295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19791734108860844545645813 1855475072705704176154295)
      ·
        refine ⟨2783212609058556264231443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855475072705704176154295 2783212609058556264231443)
        ·
          refine ⟨4174818913587834396347165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783212609058556264231443 4174818913587834396347165)
          ·
            refine ⟨1565557092595437898630187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4174818913587834396347165 1565557092595437898630187)
            ·
              refine ⟨2348335638893156847945281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565557092595437898630187 2348335638893156847945281)
              ·
                refine ⟨1761251729169867635958961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348335638893156847945281 1761251729169867635958961)
                ·
                  refine ⟨1320938796877400726969221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1761251729169867635958961 1320938796877400726969221)
                  ·
                    refine ⟨247676024414512636306729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1320938796877400726969221 247676024414512636306729)
                    ·
                      rfl

theorem cell22_723521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_723521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723521 prefixEnd_723521 := by exact prefixLift 723521
  have htrace : WordTrace (prefixWord ++ tailWord_723521) baseStart_723521 baseEnd_723521 := by
    simpa [prefixWord, tailWord_723521, baseEnd_723521] using wordTrace_append hprefix tailTrace_723521
  have hstable : (prefixWord ++ tailWord_723521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723521).length < 2 ^ (prefixWord ++ tailWord_723521).sum := by decide
  have hdescent : baseEnd_723521 < baseStart_723521 := by decide
  rcases family_descends (prefixWord ++ tailWord_723521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723540 : List Nat := [2, 4, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_723540 : Nat := 118140960795 + 723540 * 2 ^ 59
def prefixEnd_723540 : Nat := 4983230072969 + 3 ^ 40 * 723540 * 2
def baseEnd_723540 : Nat := 247682528502802920081671

theorem tailTrace_723540 : CollatzResearch.WordTrace tailWord_723540 prefixEnd_723540 247682528502802920081671 := by
  unfold tailWord_723540
  simp only [CollatzResearch.WordTrace]
  refine ⟨13194835899372812819568037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17593114532497083759424049 13194835899372812819568037)
  ·
    refine ⟨2474031731132402403669007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13194835899372812819568037 2474031731132402403669007)
    ·
      refine ⟨3711047596698603605503511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2474031731132402403669007 3711047596698603605503511)
      ·
        refine ⟨5566571395047905408255267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711047596698603605503511 5566571395047905408255267)
        ·
          refine ⟨8349857092571858112382901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5566571395047905408255267 8349857092571858112382901)
          ·
            refine ⟨782799102428611698035897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8349857092571858112382901 782799102428611698035897)
            ·
              refine ⟨587099326821458773526923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782799102428611698035897 587099326821458773526923)
              ·
                refine ⟨880648990232188160290385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587099326821458773526923 880648990232188160290385)
                ·
                  refine ⟨660486742674141120217789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 880648990232188160290385 660486742674141120217789)
                  ·
                    refine ⟨247682528502802920081671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 660486742674141120217789 247682528502802920081671)
                    ·
                      rfl

theorem cell22_723540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_723540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723540 prefixEnd_723540 := by exact prefixLift 723540
  have htrace : WordTrace (prefixWord ++ tailWord_723540) baseStart_723540 baseEnd_723540 := by
    simpa [prefixWord, tailWord_723540, baseEnd_723540] using wordTrace_append hprefix tailTrace_723540
  have hstable : (prefixWord ++ tailWord_723540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723540).length < 2 ^ (prefixWord ++ tailWord_723540).sum := by decide
  have hdescent : baseEnd_723540 < baseStart_723540 := by decide
  rcases family_descends (prefixWord ++ tailWord_723540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723609 : List Nat := [1, 2, 1, 2, 1, 2, 5, 2, 6]
def baseStart_723609 : Nat := 118140960795 + 723609 * 2 ^ 59
def prefixEnd_723609 : Nat := 4983230072969 + 3 ^ 40 * 723609 * 2
def baseEnd_723609 : Nat := 82568716204303246702153

theorem tailTrace_723609 : CollatzResearch.WordTrace tailWord_723609 prefixEnd_723609 82568716204303246702153 := by
  unfold tailWord_723609
  simp only [CollatzResearch.WordTrace]
  refine ⟨26392188435495650423397881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17594792290330433615598587 26392188435495650423397881)
  ·
    refine ⟨19794141326621737817548411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26392188435495650423397881 19794141326621737817548411)
    ·
      refine ⟨29691211989932606726322617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19794141326621737817548411 29691211989932606726322617)
      ·
        refine ⟨22268408992449455044741963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29691211989932606726322617 22268408992449455044741963)
        ·
          refine ⟨33402613488674182567112945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22268408992449455044741963 33402613488674182567112945)
          ·
            refine ⟨25051960116505636925334709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33402613488674182567112945 25051960116505636925334709)
            ·
              refine ⟨2348621260922403461750129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25051960116505636925334709 2348621260922403461750129)
              ·
                refine ⟨1761465945691802596312597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348621260922403461750129 1761465945691802596312597)
                ·
                  refine ⟨82568716204303246702153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1761465945691802596312597 82568716204303246702153)
                  ·
                    rfl

theorem cell22_723609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_723609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723609 prefixEnd_723609 := by exact prefixLift 723609
  have htrace : WordTrace (prefixWord ++ tailWord_723609) baseStart_723609 baseEnd_723609 := by
    simpa [prefixWord, tailWord_723609, baseEnd_723609] using wordTrace_append hprefix tailTrace_723609
  have hstable : (prefixWord ++ tailWord_723609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723609).length < 2 ^ (prefixWord ++ tailWord_723609).sum := by decide
  have hdescent : baseEnd_723609 < baseStart_723609 := by decide
  rcases family_descends (prefixWord ++ tailWord_723609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723658 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 1, 5]
def baseStart_723658 : Nat := 118140960795 + 723658 * 2 ^ 59
def prefixEnd_723658 : Nat := 4983230072969 + 3 ^ 40 * 723658 * 2
def baseEnd_723658 : Nat := 247722922314289945631309

theorem tailTrace_723658 : CollatzResearch.WordTrace tailWord_723658 prefixEnd_723658 247722922314289945631309 := by
  unfold tailWord_723658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6598493903079532947982907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17595983741545421194621085 6598493903079532947982907)
  ·
    refine ⟨9897740854619299421974361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6598493903079532947982907 9897740854619299421974361)
    ·
      refine ⟨7423305640964474566480771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9897740854619299421974361 7423305640964474566480771)
      ·
        refine ⟨11134958461446711849721157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7423305640964474566480771 11134958461446711849721157)
        ·
          refine ⟨2087804711521258471822717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11134958461446711849721157 2087804711521258471822717)
          ·
            refine ⟨782926766820471926933519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2087804711521258471822717 782926766820471926933519)
            ·
              refine ⟨1174390150230707890400279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782926766820471926933519 1174390150230707890400279)
              ·
                refine ⟨1761585225346061835600419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174390150230707890400279 1761585225346061835600419)
                ·
                  refine ⟨2642377838019092753400629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1761585225346061835600419 2642377838019092753400629)
                  ·
                    refine ⟨247722922314289945631309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2642377838019092753400629 247722922314289945631309)
                    ·
                      rfl

theorem cell22_723658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_723658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723658 prefixEnd_723658 := by exact prefixLift 723658
  have htrace : WordTrace (prefixWord ++ tailWord_723658) baseStart_723658 baseEnd_723658 := by
    simpa [prefixWord, tailWord_723658, baseEnd_723658] using wordTrace_append hprefix tailTrace_723658
  have hstable : (prefixWord ++ tailWord_723658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723658).length < 2 ^ (prefixWord ++ tailWord_723658).sum := by decide
  have hdescent : baseEnd_723658 < baseStart_723658 := by decide
  rcases family_descends (prefixWord ++ tailWord_723658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723671 : List Nat := [1, 1, 3, 2, 1, 4, 4, 6]
def baseStart_723671 : Nat := 118140960795 + 723671 * 2 ^ 59
def prefixEnd_723671 : Nat := 4983230072969 + 3 ^ 40 * 723671 * 2
def baseEnd_723671 : Nat := 27525263608884693895141

theorem tailTrace_723671 : CollatzResearch.WordTrace tailWord_723671 prefixEnd_723671 27525263608884693895141 := by
  unfold tailWord_723671
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394449761271035012154867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17596299840847356674769911 26394449761271035012154867)
  ·
    refine ⟨39591674641906552518232301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26394449761271035012154867 39591674641906552518232301)
    ·
      refine ⟨14846877990714957194337113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39591674641906552518232301 14846877990714957194337113)
      ·
        refine ⟨11135158493036217895752835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14846877990714957194337113 11135158493036217895752835)
        ·
          refine ⟨16702737739554326843629253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11135158493036217895752835 16702737739554326843629253)
          ·
            refine ⟨3131763326166436283180485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16702737739554326843629253 3131763326166436283180485)
            ·
              refine ⟨587205623656206803096341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3131763326166436283180485 587205623656206803096341)
              ·
                refine ⟨27525263608884693895141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 587205623656206803096341 27525263608884693895141)
                ·
                  rfl

theorem cell22_723671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 6].length) (baseStart_723671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723671 prefixEnd_723671 := by exact prefixLift 723671
  have htrace : WordTrace (prefixWord ++ tailWord_723671) baseStart_723671 baseEnd_723671 := by
    simpa [prefixWord, tailWord_723671, baseEnd_723671] using wordTrace_append hprefix tailTrace_723671
  have hstable : (prefixWord ++ tailWord_723671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723671).length < 2 ^ (prefixWord ++ tailWord_723671).sum := by decide
  have hdescent : baseEnd_723671 < baseStart_723671 := by decide
  rcases family_descends (prefixWord ++ tailWord_723671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723688 : List Nat := [2, 1, 4, 1, 5, 1, 8]
def baseStart_723688 : Nat := 118140960795 + 723688 * 2 ^ 59
def prefixEnd_723688 : Nat := 4983230072969 + 3 ^ 40 * 723688 * 2
def baseEnd_723688 : Nat := 9175303404717772865971

theorem tailTrace_723688 : CollatzResearch.WordTrace tailWord_723688 prefixEnd_723688 9175303404717772865971 := by
  unfold tailWord_723688
  simp only [CollatzResearch.WordTrace]
  refine ⟨13197534901104723457761859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17596713201472964610349145 13197534901104723457761859)
  ·
    refine ⟨19796302351657085186642789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13197534901104723457761859 19796302351657085186642789)
    ·
      refine ⟨3711806690935703472495523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19796302351657085186642789 3711806690935703472495523)
      ·
        refine ⟨5567710036403555208743285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711806690935703472495523 5567710036403555208743285)
        ·
          refine ⟨521972815912833300819683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5567710036403555208743285 521972815912833300819683)
          ·
            refine ⟨782959223869249951229525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521972815912833300819683 782959223869249951229525)
            ·
              refine ⟨9175303404717772865971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 782959223869249951229525 9175303404717772865971)
              ·
                rfl

theorem cell22_723688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 8].length) (baseStart_723688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723688 prefixEnd_723688 := by exact prefixLift 723688
  have htrace : WordTrace (prefixWord ++ tailWord_723688) baseStart_723688 baseEnd_723688 := by
    simpa [prefixWord, tailWord_723688, baseEnd_723688] using wordTrace_append hprefix tailTrace_723688
  have hstable : (prefixWord ++ tailWord_723688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723688).length < 2 ^ (prefixWord ++ tailWord_723688).sum := by decide
  have hdescent : baseEnd_723688 < baseStart_723688 := by decide
  rcases family_descends (prefixWord ++ tailWord_723688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723754 : List Nat := [3, 1, 4, 3, 1, 1, 1, 4, 1, 3]
def baseStart_723754 : Nat := 118140960795 + 723754 * 2 ^ 59
def prefixEnd_723754 : Nat := 4983230072969 + 3 ^ 40 * 723754 * 2
def baseEnd_723754 : Nat := 247755785076177695231015

theorem tailTrace_723754 : CollatzResearch.WordTrace tailWord_723754 prefixEnd_723754 247755785076177695231015 := by
  unfold tailWord_723754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6599369254992585046856579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17598318013313560124950877 6599369254992585046856579)
  ·
    refine ⟨9899053882488877570284869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6599369254992585046856579 9899053882488877570284869)
    ·
      refine ⟨1856072602966664544428413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9899053882488877570284869 1856072602966664544428413)
      ·
        refine ⟨696027226112499204160655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1856072602966664544428413 696027226112499204160655)
        ·
          refine ⟨1044040839168748806240983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696027226112499204160655 1044040839168748806240983)
          ·
            refine ⟨1566061258753123209361475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044040839168748806240983 1566061258753123209361475)
            ·
              refine ⟨2349091888129684814042213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566061258753123209361475 2349091888129684814042213)
              ·
                refine ⟨440454729024315902632915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2349091888129684814042213 440454729024315902632915)
                ·
                  refine ⟨660682093536473853949373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440454729024315902632915 660682093536473853949373)
                  ·
                    refine ⟨247755785076177695231015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 660682093536473853949373 247755785076177695231015)
                    ·
                      rfl

theorem cell22_723754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_723754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723754 prefixEnd_723754 := by exact prefixLift 723754
  have htrace : WordTrace (prefixWord ++ tailWord_723754) baseStart_723754 baseEnd_723754 := by
    simpa [prefixWord, tailWord_723754, baseEnd_723754] using wordTrace_append hprefix tailTrace_723754
  have hstable : (prefixWord ++ tailWord_723754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723754).length < 2 ^ (prefixWord ++ tailWord_723754).sum := by decide
  have hdescent : baseEnd_723754 < baseStart_723754 := by decide
  rcases family_descends (prefixWord ++ tailWord_723754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723761 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 6]
def baseStart_723761 : Nat := 118140960795 + 723761 * 2 ^ 59
def prefixEnd_723761 : Nat := 4983230072969 + 3 ^ 40 * 723761 * 2
def baseEnd_723761 : Nat := 82586060439744003435331

theorem tailTrace_723761 : CollatzResearch.WordTrace tailWord_723761 prefixEnd_723761 82586060439744003435331 := by
  unfold tailWord_723761
  simp only [CollatzResearch.WordTrace]
  refine ⟨26397732330944980382931137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17598488220629986921954091 26397732330944980382931137)
  ·
    refine ⟨19798299248208735287198353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26397732330944980382931137 19798299248208735287198353)
    ·
      refine ⟨14848724436156551465398765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19798299248208735287198353 14848724436156551465398765)
      ·
        refine ⟨5568271663558706799524537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14848724436156551465398765 5568271663558706799524537)
        ·
          refine ⟨4176203747669030099643403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5568271663558706799524537 4176203747669030099643403)
          ·
            refine ⟨6264305621503545149465105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4176203747669030099643403 6264305621503545149465105)
            ·
              refine ⟨4698229216127658862098829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6264305621503545149465105 4698229216127658862098829)
              ·
                refine ⟨1761835956047872073287061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4698229216127658862098829 1761835956047872073287061)
                ·
                  refine ⟨82586060439744003435331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1761835956047872073287061 82586060439744003435331)
                  ·
                    rfl

theorem cell22_723761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_723761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723761 prefixEnd_723761 := by exact prefixLift 723761
  have htrace : WordTrace (prefixWord ++ tailWord_723761) baseStart_723761 baseEnd_723761 := by
    simpa [prefixWord, tailWord_723761, baseEnd_723761] using wordTrace_append hprefix tailTrace_723761
  have hstable : (prefixWord ++ tailWord_723761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723761).length < 2 ^ (prefixWord ++ tailWord_723761).sum := by decide
  have hdescent : baseEnd_723761 < baseStart_723761 := by decide
  rcases family_descends (prefixWord ++ tailWord_723761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723836 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_723836 : Nat := 118140960795 + 723836 * 2 ^ 59
def prefixEnd_723836 : Nat := 4983230072969 + 3 ^ 40 * 723836 * 2
def baseEnd_723836 : Nat := 247783855351956814680763

theorem tailTrace_723836 : CollatzResearch.WordTrace tailWord_723836 prefixEnd_723836 247783855351956814680763 := by
  unfold tailWord_723836
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200233902836634095955681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17600311870448845461274241 13200233902836634095955681)
  ·
    refine ⟨9900175427127475571966761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13200233902836634095955681 9900175427127475571966761)
    ·
      refine ⟨7425131570345606678975071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9900175427127475571966761 7425131570345606678975071)
      ·
        refine ⟨11137697355518410018462607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7425131570345606678975071 11137697355518410018462607)
        ·
          refine ⟨16706546033277615027693911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11137697355518410018462607 16706546033277615027693911)
          ·
            refine ⟨25059819049916422541540867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16706546033277615027693911 25059819049916422541540867)
            ·
              refine ⟨37589728574874633812311301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25059819049916422541540867 37589728574874633812311301)
              ·
                refine ⟨7048074107788993839808369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37589728574874633812311301 7048074107788993839808369)
                ·
                  refine ⟨5286055580841745379856277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7048074107788993839808369 5286055580841745379856277)
                  ·
                    refine ⟨247783855351956814680763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5286055580841745379856277 247783855351956814680763)
                    ·
                      rfl

theorem cell22_723836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_723836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723836 prefixEnd_723836 := by exact prefixLift 723836
  have htrace : WordTrace (prefixWord ++ tailWord_723836) baseStart_723836 baseEnd_723836 := by
    simpa [prefixWord, tailWord_723836, baseEnd_723836] using wordTrace_append hprefix tailTrace_723836
  have hstable : (prefixWord ++ tailWord_723836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723836).length < 2 ^ (prefixWord ++ tailWord_723836).sum := by decide
  have hdescent : baseEnd_723836 < baseStart_723836 := by decide
  rcases family_descends (prefixWord ++ tailWord_723836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723851 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 7]
def baseStart_723851 : Nat := 118140960795 + 723851 * 2 ^ 59
def prefixEnd_723851 : Nat := 4983230072969 + 3 ^ 40 * 723851 * 2
def baseEnd_723851 : Nat := 82596330052833925185239

theorem tailTrace_723851 : CollatzResearch.WordTrace tailWord_723851 prefixEnd_723851 82596330052833925185239 := by
  unfold tailWord_723851
  simp only [CollatzResearch.WordTrace]
  refine ⟨26401014900618925753707407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17600676600412617169138271 26401014900618925753707407)
  ·
    refine ⟨39601522350928388630561111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26401014900618925753707407 39601522350928388630561111)
    ·
      refine ⟨59402283526392582945841667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39601522350928388630561111 59402283526392582945841667)
      ·
        refine ⟨89103425289588874418762501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59402283526392582945841667 89103425289588874418762501)
        ·
          refine ⟨16706892241797913953517969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89103425289588874418762501 16706892241797913953517969)
          ·
            refine ⟨12530169181348435465138477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16706892241797913953517969 12530169181348435465138477)
            ·
              refine ⟨4698813443005663299426929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12530169181348435465138477 4698813443005663299426929)
              ·
                refine ⟨3524110082254247474570197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4698813443005663299426929 3524110082254247474570197)
                ·
                  refine ⟨82596330052833925185239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3524110082254247474570197 82596330052833925185239)
                  ·
                    rfl

theorem cell22_723851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 7].length) (baseStart_723851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723851 prefixEnd_723851 := by exact prefixLift 723851
  have htrace : WordTrace (prefixWord ++ tailWord_723851) baseStart_723851 baseEnd_723851 := by
    simpa [prefixWord, tailWord_723851, baseEnd_723851] using wordTrace_append hprefix tailTrace_723851
  have hstable : (prefixWord ++ tailWord_723851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723851).length < 2 ^ (prefixWord ++ tailWord_723851).sum := by decide
  have hdescent : baseEnd_723851 < baseStart_723851 := by decide
  rcases family_descends (prefixWord ++ tailWord_723851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723898 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_723898 : Nat := 118140960795 + 723898 * 2 ^ 59
def prefixEnd_723898 : Nat := 4983230072969 + 3 ^ 40 * 723898 * 2
def baseEnd_723898 : Nat := 247805079219009319630573

theorem tailTrace_723898 : CollatzResearch.WordTrace tailWord_723898 prefixEnd_723898 247805079219009319630573 := by
  unfold tailWord_723898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6600682282862163195167087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17601819420965768520445565 6600682282862163195167087)
  ·
    refine ⟨9901023424293244792750631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6600682282862163195167087 9901023424293244792750631)
    ·
      refine ⟨14851535136439867189125947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9901023424293244792750631 14851535136439867189125947)
      ·
        refine ⟨22277302704659800783688921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14851535136439867189125947 22277302704659800783688921)
        ·
          refine ⟨16707977028494850587766691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22277302704659800783688921 16707977028494850587766691)
          ·
            refine ⟨25061965542742275881650037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16707977028494850587766691 25061965542742275881650037)
            ·
              refine ⟨2349559269632088363904691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25061965542742275881650037 2349559269632088363904691)
              ·
                refine ⟨3524338904448132545857037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2349559269632088363904691 3524338904448132545857037)
                ·
                  refine ⟨1321627089168049704696389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3524338904448132545857037 1321627089168049704696389)
                  ·
                    refine ⟨247805079219009319630573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321627089168049704696389 247805079219009319630573)
                    ·
                      rfl

theorem cell22_723898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_723898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723898 prefixEnd_723898 := by exact prefixLift 723898
  have htrace : WordTrace (prefixWord ++ tailWord_723898) baseStart_723898 baseEnd_723898 := by
    simpa [prefixWord, tailWord_723898, baseEnd_723898] using wordTrace_append hprefix tailTrace_723898
  have hstable : (prefixWord ++ tailWord_723898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723898).length < 2 ^ (prefixWord ++ tailWord_723898).sum := by decide
  have hdescent : baseEnd_723898 < baseStart_723898 := by decide
  rcases family_descends (prefixWord ++ tailWord_723898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_723966 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_723966 : Nat := 118140960795 + 723966 * 2 ^ 59
def prefixEnd_723966 : Nat := 4983230072969 + 3 ^ 40 * 723966 * 2
def baseEnd_723966 : Nat := 247828357008679808930365

theorem tailTrace_723966 : CollatzResearch.WordTrace tailWord_723966 prefixEnd_723966 247828357008679808930365 := by
  unfold tailWord_723966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300651161900287549267969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17603472863468200262762501 3300651161900287549267969)
  ·
    refine ⟨2475488371425215661950977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3300651161900287549267969 2475488371425215661950977)
    ·
      refine ⟨1856616278568911746463233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2475488371425215661950977 1856616278568911746463233)
      ·
        refine ⟨1392462208926683809847425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1856616278568911746463233 1392462208926683809847425)
        ·
          refine ⟨1044346656695012857385569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1392462208926683809847425 1044346656695012857385569)
          ·
            refine ⟨783259992521259643039177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044346656695012857385569 783259992521259643039177)
            ·
              refine ⟨587444994390944732279383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783259992521259643039177 587444994390944732279383)
              ·
                refine ⟨881167491586417098419075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587444994390944732279383 881167491586417098419075)
                ·
                  refine ⟨1321751237379625647628613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 881167491586417098419075 1321751237379625647628613)
                  ·
                    refine ⟨247828357008679808930365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321751237379625647628613 247828357008679808930365)
                    ·
                      rfl

theorem cell22_723966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_723966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_723966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_723966 prefixEnd_723966 := by exact prefixLift 723966
  have htrace : WordTrace (prefixWord ++ tailWord_723966) baseStart_723966 baseEnd_723966 := by
    simpa [prefixWord, tailWord_723966, baseEnd_723966] using wordTrace_append hprefix tailTrace_723966
  have hstable : (prefixWord ++ tailWord_723966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_723966).length < 2 ^ (prefixWord ++ tailWord_723966).sum := by decide
  have hdescent : baseEnd_723966 < baseStart_723966 := by decide
  rcases family_descends (prefixWord ++ tailWord_723966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724024 : List Nat := [2, 1, 2, 1, 5, 1, 3, 3, 1, 3]
def baseStart_724024 : Nat := 118140960795 + 724024 * 2 ^ 59
def prefixEnd_724024 : Nat := 4983230072969 + 3 ^ 40 * 724024 * 2
def baseEnd_724024 : Nat := 247848211593986990980187

theorem tailTrace_724024 : CollatzResearch.WordTrace tailWord_724024 prefixEnd_724024 247848211593986990980187 := by
  unfold tailWord_724024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13203662364496088149877563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17604883152661450866503417 13203662364496088149877563)
  ·
    refine ⟨19805493546744132224816345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13203662364496088149877563 19805493546744132224816345)
    ·
      refine ⟨14854120160058099168612259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19805493546744132224816345 14854120160058099168612259)
      ·
        refine ⟨22281180240087148752918389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14854120160058099168612259 22281180240087148752918389)
        ·
          refine ⟨2088860647508170195586099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22281180240087148752918389 2088860647508170195586099)
          ·
            refine ⟨3133290971262255293379149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088860647508170195586099 3133290971262255293379149)
            ·
              refine ⟨1174984114223345735017181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3133290971262255293379149 1174984114223345735017181)
              ·
                refine ⟨440619042833754650631443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1174984114223345735017181 440619042833754650631443)
                ·
                  refine ⟨660928564250631975947165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440619042833754650631443 660928564250631975947165)
                  ·
                    refine ⟨247848211593986990980187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 660928564250631975947165 247848211593986990980187)
                    ·
                      rfl

theorem cell22_724024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_724024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724024 prefixEnd_724024 := by exact prefixLift 724024
  have htrace : WordTrace (prefixWord ++ tailWord_724024) baseStart_724024 baseEnd_724024 := by
    simpa [prefixWord, tailWord_724024, baseEnd_724024] using wordTrace_append hprefix tailTrace_724024
  have hstable : (prefixWord ++ tailWord_724024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724024).length < 2 ^ (prefixWord ++ tailWord_724024).sum := by decide
  have hdescent : baseEnd_724024 < baseStart_724024 := by decide
  rcases family_descends (prefixWord ++ tailWord_724024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724080 : List Nat := [2, 1, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_724080 : Nat := 118140960795 + 724080 * 2 ^ 59
def prefixEnd_724080 : Nat := 4983230072969 + 3 ^ 40 * 724080 * 2
def baseEnd_724080 : Nat := 247867381538421511580015

theorem tailTrace_724080 : CollatzResearch.WordTrace tailWord_724080 prefixEnd_724080 247867381538421511580015 := by
  unfold tailWord_724080
  simp only [CollatzResearch.WordTrace]
  refine ⟨13204683608394648931896847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17606244811192865242529129 13204683608394648931896847)
  ·
    refine ⟨19807025412591973397845271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13204683608394648931896847 19807025412591973397845271)
    ·
      refine ⟨29710538118887960096767907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19807025412591973397845271 29710538118887960096767907)
      ·
        refine ⟨44565807178331940145151861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29710538118887960096767907 44565807178331940145151861)
        ·
          refine ⟨4178044422968619388607987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44565807178331940145151861 4178044422968619388607987)
          ·
            refine ⟨6267066634452929082911981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178044422968619388607987 6267066634452929082911981)
            ·
              refine ⟨2350149987919848406091993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6267066634452929082911981 2350149987919848406091993)
              ·
                refine ⟨1762612490939886304568995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350149987919848406091993 1762612490939886304568995)
                ·
                  refine ⟨2643918736409829456853493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762612490939886304568995 2643918736409829456853493)
                  ·
                    refine ⟨247867381538421511580015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2643918736409829456853493 247867381538421511580015)
                    ·
                      rfl

theorem cell22_724080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_724080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724080 prefixEnd_724080 := by exact prefixLift 724080
  have htrace : WordTrace (prefixWord ++ tailWord_724080) baseStart_724080 baseEnd_724080 := by
    simpa [prefixWord, tailWord_724080, baseEnd_724080] using wordTrace_append hprefix tailTrace_724080
  have hstable : (prefixWord ++ tailWord_724080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724080).length < 2 ^ (prefixWord ++ tailWord_724080).sum := by decide
  have hdescent : baseEnd_724080 < baseStart_724080 := by decide
  rcases family_descends (prefixWord ++ tailWord_724080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724082 : List Nat := [3, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_724082 : Nat := 118140960795 + 724082 * 2 ^ 59
def prefixEnd_724082 : Nat := 4983230072969 + 3 ^ 40 * 724082 * 2
def baseEnd_724082 : Nat := 82622688726431391010003

theorem tailTrace_724082 : CollatzResearch.WordTrace tailWord_724082 prefixEnd_724082 82622688726431391010003 := by
  unfold tailWord_724082
  simp only [CollatzResearch.WordTrace]
  refine ⟨6602360040695513051341625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17606293441854701470244333 6602360040695513051341625)
  ·
    refine ⟨4951770030521634788506219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6602360040695513051341625 4951770030521634788506219)
    ·
      refine ⟨7427655045782452182759329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4951770030521634788506219 7427655045782452182759329)
      ·
        refine ⟨5570741284336839137069497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7427655045782452182759329 5570741284336839137069497)
        ·
          refine ⟨4178055963252629352802123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5570741284336839137069497 4178055963252629352802123)
          ·
            refine ⟨6267083944878944029203185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178055963252629352802123 6267083944878944029203185)
            ·
              refine ⟨4700312958659208021902389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6267083944878944029203185 4700312958659208021902389)
              ·
                refine ⟨440654339874300752053349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4700312958659208021902389 440654339874300752053349)
                ·
                  refine ⟨82622688726431391010003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 440654339874300752053349 82622688726431391010003)
                  ·
                    rfl

theorem cell22_724082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_724082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724082 prefixEnd_724082 := by exact prefixLift 724082
  have htrace : WordTrace (prefixWord ++ tailWord_724082) baseStart_724082 baseEnd_724082 := by
    simpa [prefixWord, tailWord_724082, baseEnd_724082] using wordTrace_append hprefix tailTrace_724082
  have hstable : (prefixWord ++ tailWord_724082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724082).length < 2 ^ (prefixWord ++ tailWord_724082).sum := by decide
  have hdescent : baseEnd_724082 < baseStart_724082 := by decide
  rcases family_descends (prefixWord ++ tailWord_724082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724114 : List Nat := [3, 2, 3, 1, 1, 2, 2, 3, 2, 3]
def baseStart_724114 : Nat := 118140960795 + 724114 * 2 ^ 59
def prefixEnd_724114 : Nat := 4983230072969 + 3 ^ 40 * 724114 * 2
def baseEnd_724114 : Nat := 247879020433256756229911

theorem tailTrace_724114 : CollatzResearch.WordTrace tailWord_724114 prefixEnd_724114 247879020433256756229911 := by
  unfold tailWord_724114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6602651824666530417632849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17607071532444081113687597 6602651824666530417632849)
  ·
    refine ⟨4951988868499897813224637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6602651824666530417632849 4951988868499897813224637)
    ·
      refine ⟨1856995825687461679959239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4951988868499897813224637 1856995825687461679959239)
      ·
        refine ⟨2785493738531192519938859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1856995825687461679959239 2785493738531192519938859)
        ·
          refine ⟨4178240607796788779908289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785493738531192519938859 4178240607796788779908289)
          ·
            refine ⟨3133680455847591584931217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4178240607796788779908289 3133680455847591584931217)
            ·
              refine ⟨2350260341885693688698413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3133680455847591584931217 2350260341885693688698413)
              ·
                refine ⟨881347628207135133261905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2350260341885693688698413 881347628207135133261905)
                ·
                  refine ⟨661010721155351349946429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 881347628207135133261905 661010721155351349946429)
                  ·
                    refine ⟨247879020433256756229911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661010721155351349946429 247879020433256756229911)
                    ·
                      rfl

theorem cell22_724114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_724114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724114 prefixEnd_724114 := by exact prefixLift 724114
  have htrace : WordTrace (prefixWord ++ tailWord_724114) baseStart_724114 baseEnd_724114 := by
    simpa [prefixWord, tailWord_724114, baseEnd_724114] using wordTrace_append hprefix tailTrace_724114
  have hstable : (prefixWord ++ tailWord_724114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724114).length < 2 ^ (prefixWord ++ tailWord_724114).sum := by decide
  have hdescent : baseEnd_724114 < baseStart_724114 := by decide
  rcases family_descends (prefixWord ++ tailWord_724114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724155 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 5]
def baseStart_724155 : Nat := 118140960795 + 724155 * 2 ^ 59
def prefixEnd_724155 : Nat := 4983230072969 + 3 ^ 40 * 724155 * 2
def baseEnd_724155 : Nat := 82631018523715438651595

theorem tailTrace_724155 : CollatzResearch.WordTrace tailWord_724155 prefixEnd_724155 82631018523715438651595 := by
  unfold tailWord_724155
  simp only [CollatzResearch.WordTrace]
  refine ⟨26412102691517585672773919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17608068461011723781849279 26412102691517585672773919)
  ·
    refine ⟨39618154037276378509160879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26412102691517585672773919 39618154037276378509160879)
    ·
      refine ⟨59427231055914567763741319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39618154037276378509160879 59427231055914567763741319)
      ·
        refine ⟨89140846583871851645611979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59427231055914567763741319 89140846583871851645611979)
        ·
          refine ⟨133711269875807777468417969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89140846583871851645611979 133711269875807777468417969)
          ·
            refine ⟨100283452406855833101313477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133711269875807777468417969 100283452406855833101313477)
            ·
              refine ⟨18803147326285468706496277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100283452406855833101313477 18803147326285468706496277)
              ·
                refine ⟨881397530919631345617013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18803147326285468706496277 881397530919631345617013)
                ·
                  refine ⟨82631018523715438651595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 881397530919631345617013 82631018523715438651595)
                  ·
                    rfl

theorem cell22_724155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 5].length) (baseStart_724155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724155 prefixEnd_724155 := by exact prefixLift 724155
  have htrace : WordTrace (prefixWord ++ tailWord_724155) baseStart_724155 baseEnd_724155 := by
    simpa [prefixWord, tailWord_724155, baseEnd_724155] using wordTrace_append hprefix tailTrace_724155
  have hstable : (prefixWord ++ tailWord_724155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724155).length < 2 ^ (prefixWord ++ tailWord_724155).sum := by decide
  have hdescent : baseEnd_724155 < baseStart_724155 := by decide
  rcases family_descends (prefixWord ++ tailWord_724155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724159 : List Nat := [1, 1, 2, 2, 2, 2, 4, 4, 1, 3]
def baseStart_724159 : Nat := 118140960795 + 724159 * 2 ^ 59
def prefixEnd_724159 : Nat := 4983230072969 + 3 ^ 40 * 724159 * 2
def baseEnd_724159 : Nat := 247894424852891638854773

theorem tailTrace_724159 : CollatzResearch.WordTrace tailWord_724159 prefixEnd_724159 247894424852891638854773 := by
  unfold tailWord_724159
  simp only [CollatzResearch.WordTrace]
  refine ⟨26412248583503094355919531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17608165722335396237279687 26412248583503094355919531)
  ·
    refine ⟨39618372875254641533879297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26412248583503094355919531 39618372875254641533879297)
    ·
      refine ⟨29713779656440981150409473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39618372875254641533879297 29713779656440981150409473)
      ·
        refine ⟨22285334742330735862807105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29713779656440981150409473 22285334742330735862807105)
        ·
          refine ⟨16714001056748051897105329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22285334742330735862807105 16714001056748051897105329)
          ·
            refine ⟨12535500792561038922828997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16714001056748051897105329 12535500792561038922828997)
            ·
              refine ⟨2350406398605194798030437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12535500792561038922828997 2350406398605194798030437)
              ·
                refine ⟨440701199738474024630707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2350406398605194798030437 440701199738474024630707)
                ·
                  refine ⟨661051799607711036946061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440701199738474024630707 661051799607711036946061)
                  ·
                    refine ⟨247894424852891638854773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661051799607711036946061 247894424852891638854773)
                    ·
                      rfl

theorem cell22_724159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 3].length) (baseStart_724159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724159 prefixEnd_724159 := by exact prefixLift 724159
  have htrace : WordTrace (prefixWord ++ tailWord_724159) baseStart_724159 baseEnd_724159 := by
    simpa [prefixWord, tailWord_724159, baseEnd_724159] using wordTrace_append hprefix tailTrace_724159
  have hstable : (prefixWord ++ tailWord_724159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724159).length < 2 ^ (prefixWord ++ tailWord_724159).sum := by decide
  have hdescent : baseEnd_724159 < baseStart_724159 := by decide
  rcases family_descends (prefixWord ++ tailWord_724159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724215 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 3, 5]
def baseStart_724215 : Nat := 118140960795 + 724215 * 2 ^ 59
def prefixEnd_724215 : Nat := 4983230072969 + 3 ^ 40 * 724215 * 2
def baseEnd_724215 : Nat := 247913594797326159454601

theorem tailTrace_724215 : CollatzResearch.WordTrace tailWord_724215 prefixEnd_724215 247913594797326159454601 := by
  unfold tailWord_724215
  simp only [CollatzResearch.WordTrace]
  refine ⟨26414291071300215919958099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17609527380866810613305399 26414291071300215919958099)
  ·
    refine ⟨39621436606950323879937149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26414291071300215919958099 39621436606950323879937149)
    ·
      refine ⟨14858038727606371454976431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39621436606950323879937149 14858038727606371454976431)
      ·
        refine ⟨22287058091409557182464647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14858038727606371454976431 22287058091409557182464647)
        ·
          refine ⟨33430587137114335773696971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22287058091409557182464647 33430587137114335773696971)
          ·
            refine ⟨50145880705671503660545457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33430587137114335773696971 50145880705671503660545457)
            ·
              refine ⟨37609410529253627745409093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50145880705671503660545457 37609410529253627745409093)
              ·
                refine ⟨7051764474235055202264205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37609410529253627745409093 7051764474235055202264205)
                ·
                  refine ⟨2644411677838145700849077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7051764474235055202264205 2644411677838145700849077)
                  ·
                    refine ⟨247913594797326159454601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2644411677838145700849077 247913594797326159454601)
                    ·
                      rfl

theorem cell22_724215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_724215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724215 prefixEnd_724215 := by exact prefixLift 724215
  have htrace : WordTrace (prefixWord ++ tailWord_724215) baseStart_724215 baseEnd_724215 := by
    simpa [prefixWord, tailWord_724215, baseEnd_724215] using wordTrace_append hprefix tailTrace_724215
  have hstable : (prefixWord ++ tailWord_724215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724215).length < 2 ^ (prefixWord ++ tailWord_724215).sum := by decide
  have hdescent : baseEnd_724215 < baseStart_724215 := by decide
  rcases family_descends (prefixWord ++ tailWord_724215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724264 : List Nat := [2, 1, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_724264 : Nat := 118140960795 + 724264 * 2 ^ 59
def prefixEnd_724264 : Nat := 4983230072969 + 3 ^ 40 * 724264 * 2
def baseEnd_724264 : Nat := 247930368498706364979451

theorem tailTrace_724264 : CollatzResearch.WordTrace tailWord_724264 prefixEnd_724264 247930368498706364979451 := by
  unfold tailWord_724264
  simp only [CollatzResearch.WordTrace]
  refine ⟨13208039124061348644245923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17610718832081798192327897 13208039124061348644245923)
  ·
    refine ⟨19812058686092022966368885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13208039124061348644245923 19812058686092022966368885)
    ·
      refine ⟨1857380501821127153097083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19812058686092022966368885 1857380501821127153097083)
      ·
        refine ⟨2786070752731690729645625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857380501821127153097083 2786070752731690729645625)
        ·
          refine ⟨2089553064548768047234219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2786070752731690729645625 2089553064548768047234219)
          ·
            refine ⟨3134329596823152070851329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089553064548768047234219 3134329596823152070851329)
            ·
              refine ⟨2350747197617364053138497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134329596823152070851329 2350747197617364053138497)
              ·
                refine ⟨1763060398213023039853873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350747197617364053138497 1763060398213023039853873)
                ·
                  refine ⟨1322295298659767279890405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1763060398213023039853873 1322295298659767279890405)
                  ·
                    refine ⟨247930368498706364979451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1322295298659767279890405 247930368498706364979451)
                    ·
                      rfl

theorem cell22_724264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_724264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724264 prefixEnd_724264 := by exact prefixLift 724264
  have htrace : WordTrace (prefixWord ++ tailWord_724264) baseStart_724264 baseEnd_724264 := by
    simpa [prefixWord, tailWord_724264, baseEnd_724264] using wordTrace_append hprefix tailTrace_724264
  have hstable : (prefixWord ++ tailWord_724264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724264).length < 2 ^ (prefixWord ++ tailWord_724264).sum := by decide
  have hdescent : baseEnd_724264 < baseStart_724264 := by decide
  rcases family_descends (prefixWord ++ tailWord_724264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724266 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_724266 : Nat := 118140960795 + 724266 * 2 ^ 59
def prefixEnd_724266 : Nat := 4983230072969 + 3 ^ 40 * 724266 * 2
def baseEnd_724266 : Nat := 247931053139579026429445

theorem tailTrace_724266 : CollatzResearch.WordTrace tailWord_724266 prefixEnd_724266 247931053139579026429445 := by
  unfold tailWord_724266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6604037798528862907516163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17610767462743634420043101 6604037798528862907516163)
  ·
    refine ⟨9906056697793294361274245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6604037798528862907516163 9906056697793294361274245)
    ·
      refine ⟨1857385630836242692738921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9906056697793294361274245 1857385630836242692738921)
      ·
        refine ⟨1393039223127182019554191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1857385630836242692738921 1393039223127182019554191)
        ·
          refine ⟨2089558834690773029331287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393039223127182019554191 2089558834690773029331287)
          ·
            refine ⟨3134338252036159543996931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089558834690773029331287 3134338252036159543996931)
            ·
              refine ⟨4701507378054239315995397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134338252036159543996931 4701507378054239315995397)
              ·
                refine ⟨881532633385169871749137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4701507378054239315995397 881532633385169871749137)
                ·
                  refine ⟨661149475038877403811853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 881532633385169871749137 661149475038877403811853)
                  ·
                    refine ⟨247931053139579026429445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661149475038877403811853 247931053139579026429445)
                    ·
                      rfl

theorem cell22_724266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_724266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724266 prefixEnd_724266 := by exact prefixLift 724266
  have htrace : WordTrace (prefixWord ++ tailWord_724266) baseStart_724266 baseEnd_724266 := by
    simpa [prefixWord, tailWord_724266, baseEnd_724266] using wordTrace_append hprefix tailTrace_724266
  have hstable : (prefixWord ++ tailWord_724266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724266).length < 2 ^ (prefixWord ++ tailWord_724266).sum := by decide
  have hdescent : baseEnd_724266 < baseStart_724266 := by decide
  rcases family_descends (prefixWord ++ tailWord_724266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724311 : List Nat := [1, 1, 3, 2, 3, 2, 1, 5, 1, 3]
def baseStart_724311 : Nat := 118140960795 + 724311 * 2 ^ 59
def prefixEnd_724311 : Nat := 4983230072969 + 3 ^ 40 * 724311 * 2
def baseEnd_724311 : Nat := 247946457559213909054307

theorem tailTrace_724311 : CollatzResearch.WordTrace tailWord_724311 prefixEnd_724311 247946457559213909054307 := by
  unfold tailWord_724311
  simp only [CollatzResearch.WordTrace]
  refine ⟨26417792478952424315452787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17611861652634949543635191 26417792478952424315452787)
  ·
    refine ⟨39626688718428636473179181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26417792478952424315452787 39626688718428636473179181)
    ·
      refine ⟨14860008269410738677442193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39626688718428636473179181 14860008269410738677442193)
      ·
        refine ⟨11145006202058054008081645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14860008269410738677442193 11145006202058054008081645)
        ·
          refine ⟨4179377325771770253030617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11145006202058054008081645 4179377325771770253030617)
          ·
            refine ⟨3134532994328827689772963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4179377325771770253030617 3134532994328827689772963)
            ·
              refine ⟨4701799491493241534659445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134532994328827689772963 4701799491493241534659445)
              ·
                refine ⟨440793702327491393874323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4701799491493241534659445 440793702327491393874323)
                ·
                  refine ⟨661190553491237090811485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440793702327491393874323 661190553491237090811485)
                  ·
                    refine ⟨247946457559213909054307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661190553491237090811485 247946457559213909054307)
                    ·
                      rfl

theorem cell22_724311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_724311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724311 prefixEnd_724311 := by exact prefixLift 724311
  have htrace : WordTrace (prefixWord ++ tailWord_724311) baseStart_724311 baseEnd_724311 := by
    simpa [prefixWord, tailWord_724311, baseEnd_724311] using wordTrace_append hprefix tailTrace_724311
  have hstable : (prefixWord ++ tailWord_724311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724311).length < 2 ^ (prefixWord ++ tailWord_724311).sum := by decide
  have hdescent : baseEnd_724311 < baseStart_724311 := by decide
  rcases family_descends (prefixWord ++ tailWord_724311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724317 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_724317 : Nat := 118140960795 + 724317 * 2 ^ 59
def prefixEnd_724317 : Nat := 4983230072969 + 3 ^ 40 * 724317 * 2
def baseEnd_724317 : Nat := 247948511481831893404289

theorem tailTrace_724317 : CollatzResearch.WordTrace tailWord_724317 prefixEnd_724317 247948511481831893404289 := by
  unfold tailWord_724317
  simp only [CollatzResearch.WordTrace]
  refine ⟨26418011316930687340171205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17612007544620458226780803 26418011316930687340171205)
  ·
    refine ⟨4953377121924503876282101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26418011316930687340171205 4953377121924503876282101)
    ·
      refine ⟨464379105180422238401447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4953377121924503876282101 464379105180422238401447)
      ·
        refine ⟨696568657770633357602171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464379105180422238401447 696568657770633357602171)
        ·
          refine ⟨1044852986655950036403257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696568657770633357602171 1044852986655950036403257)
          ·
            refine ⟨783639739991962527302443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044852986655950036403257 783639739991962527302443)
            ·
              refine ⟨1175459609987943790953665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783639739991962527302443 1175459609987943790953665)
              ·
                refine ⟨881594707490957843215249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175459609987943790953665 881594707490957843215249)
                ·
                  refine ⟨661196030618218382411437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 881594707490957843215249 661196030618218382411437)
                  ·
                    refine ⟨247948511481831893404289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661196030618218382411437 247948511481831893404289)
                    ·
                      rfl

theorem cell22_724317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_724317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724317 prefixEnd_724317 := by exact prefixLift 724317
  have htrace : WordTrace (prefixWord ++ tailWord_724317) baseStart_724317 baseEnd_724317 := by
    simpa [prefixWord, tailWord_724317, baseEnd_724317] using wordTrace_append hprefix tailTrace_724317
  have hstable : (prefixWord ++ tailWord_724317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724317).length < 2 ^ (prefixWord ++ tailWord_724317).sum := by decide
  have hdescent : baseEnd_724317 < baseStart_724317 := by decide
  rcases family_descends (prefixWord ++ tailWord_724317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724324 : List Nat := [2, 3, 1, 1, 3, 2, 3, 2, 5]
def baseStart_724324 : Nat := 118140960795 + 724324 * 2 ^ 59
def prefixEnd_724324 : Nat := 4983230072969 + 3 ^ 40 * 724324 * 2
def baseEnd_724324 : Nat := 82650302574962069493089

theorem tailTrace_724324 : CollatzResearch.WordTrace tailWord_724324 prefixEnd_724324 82650302574962069493089 := by
  unfold tailWord_724324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13209133313952663767838013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17612177751936885023784017 13209133313952663767838013)
  ·
    refine ⟨4953424992732248912939255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13209133313952663767838013 4953424992732248912939255)
    ·
      refine ⟨7430137489098373369408883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953424992732248912939255 7430137489098373369408883)
      ·
        refine ⟨11145206233647560054113325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7430137489098373369408883 11145206233647560054113325)
        ·
          refine ⟨4179452337617835020292497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11145206233647560054113325 4179452337617835020292497)
          ·
            refine ⟨3134589253213376265219373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4179452337617835020292497 3134589253213376265219373)
            ·
              refine ⟨1175470969955016099457265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3134589253213376265219373 1175470969955016099457265)
              ·
                refine ⟨881603227466262074592949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175470969955016099457265 881603227466262074592949)
                ·
                  refine ⟨82650302574962069493089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 881603227466262074592949 82650302574962069493089)
                  ·
                    rfl

theorem cell22_724324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_724324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724324 prefixEnd_724324 := by exact prefixLift 724324
  have htrace : WordTrace (prefixWord ++ tailWord_724324) baseStart_724324 baseEnd_724324 := by
    simpa [prefixWord, tailWord_724324, baseEnd_724324] using wordTrace_append hprefix tailTrace_724324
  have hstable : (prefixWord ++ tailWord_724324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724324).length < 2 ^ (prefixWord ++ tailWord_724324).sum := by decide
  have hdescent : baseEnd_724324 < baseStart_724324 := by decide
  rcases family_descends (prefixWord ++ tailWord_724324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724337 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_724337 : Nat := 118140960795 + 724337 * 2 ^ 59
def prefixEnd_724337 : Nat := 4983230072969 + 3 ^ 40 * 724337 * 2
def baseEnd_724337 : Nat := 247955357890558507904227

theorem tailTrace_724337 : CollatzResearch.WordTrace tailWord_724337 prefixEnd_724337 247955357890558507904227 := by
  unfold tailWord_724337
  simp only [CollatzResearch.WordTrace]
  refine ⟨26418740776858230755899265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17612493851238820503932843 26418740776858230755899265)
  ·
    refine ⟨19814055582643673066924449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26418740776858230755899265 19814055582643673066924449)
    ·
      refine ⟨14860541686982754800193337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19814055582643673066924449 14860541686982754800193337)
      ·
        refine ⟨11145406265237066100145003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14860541686982754800193337 11145406265237066100145003)
        ·
          refine ⟨16718109397855599150217505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11145406265237066100145003 16718109397855599150217505)
          ·
            refine ⟨12538582048391699362663129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16718109397855599150217505 12538582048391699362663129)
            ·
              refine ⟨9403936536293774521997347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12538582048391699362663129 9403936536293774521997347)
              ·
                refine ⟨14105904804440661782996021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9403936536293774521997347 14105904804440661782996021)
                ·
                  refine ⟨1322428575416312042155877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14105904804440661782996021 1322428575416312042155877)
                  ·
                    refine ⟨247955357890558507904227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1322428575416312042155877 247955357890558507904227)
                    ·
                      rfl

theorem cell22_724337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_724337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724337 prefixEnd_724337 := by exact prefixLift 724337
  have htrace : WordTrace (prefixWord ++ tailWord_724337) baseStart_724337 baseEnd_724337 := by
    simpa [prefixWord, tailWord_724337, baseEnd_724337] using wordTrace_append hprefix tailTrace_724337
  have hstable : (prefixWord ++ tailWord_724337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724337).length < 2 ^ (prefixWord ++ tailWord_724337).sum := by decide
  have hdescent : baseEnd_724337 < baseStart_724337 := by decide
  rcases family_descends (prefixWord ++ tailWord_724337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724384 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 4, 3]
def baseStart_724384 : Nat := 118140960795 + 724384 * 2 ^ 59
def prefixEnd_724384 : Nat := 4983230072969 + 3 ^ 40 * 724384 * 2
def baseEnd_724384 : Nat := 247971446951066051979083

theorem tailTrace_724384 : CollatzResearch.WordTrace tailWord_724384 prefixEnd_724384 247971446951066051979083 := by
  unfold tailWord_724384
  simp only [CollatzResearch.WordTrace]
  refine ⟨13210227503843978891430103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17613636671791971855240137 13210227503843978891430103)
  ·
    refine ⟨19815341255765968337145155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13210227503843978891430103 19815341255765968337145155)
    ·
      refine ⟨29723011883648952505717733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19815341255765968337145155 29723011883648952505717733)
      ·
        refine ⟨5573064728184178594822075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29723011883648952505717733 5573064728184178594822075)
        ·
          refine ⟨8359597092276267892233113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5573064728184178594822075 8359597092276267892233113)
          ·
            refine ⟨6269697819207200919174835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8359597092276267892233113 6269697819207200919174835)
            ·
              refine ⟨9404546728810801378762253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6269697819207200919174835 9404546728810801378762253)
              ·
                refine ⟨3526705023304050517035845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9404546728810801378762253 3526705023304050517035845)
                ·
                  refine ⟨661257191869509471944221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3526705023304050517035845 661257191869509471944221)
                  ·
                    refine ⟨247971446951066051979083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661257191869509471944221 247971446951066051979083)
                    ·
                      rfl

theorem cell22_724384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_724384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724384 prefixEnd_724384 := by exact prefixLift 724384
  have htrace : WordTrace (prefixWord ++ tailWord_724384) baseStart_724384 baseEnd_724384 := by
    simpa [prefixWord, tailWord_724384, baseEnd_724384] using wordTrace_append hprefix tailTrace_724384
  have hstable : (prefixWord ++ tailWord_724384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724384).length < 2 ^ (prefixWord ++ tailWord_724384).sum := by decide
  have hdescent : baseEnd_724384 < baseStart_724384 := by decide
  rcases family_descends (prefixWord ++ tailWord_724384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724386 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_724386 : Nat := 118140960795 + 724386 * 2 ^ 59
def prefixEnd_724386 : Nat := 4983230072969 + 3 ^ 40 * 724386 * 2
def baseEnd_724386 : Nat := 82657377197312904476359

theorem tailTrace_724386 : CollatzResearch.WordTrace tailWord_724386 prefixEnd_724386 82657377197312904476359 := by
  unfold tailWord_724386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6605131988420178031108253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17613685302453808082955341 6605131988420178031108253)
  ·
    refine ⟨2476924495657566761665595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6605131988420178031108253 2476924495657566761665595)
    ·
      refine ⟨3715386743486350142498393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2476924495657566761665595 3715386743486350142498393)
      ·
        refine ⟨2786540057614762606873795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3715386743486350142498393 2786540057614762606873795)
        ·
          refine ⟨4179810086422143910310693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786540057614762606873795 4179810086422143910310693)
          ·
            refine ⟨783714391204151983183255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4179810086422143910310693 783714391204151983183255)
            ·
              refine ⟨1175571586806227974774883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783714391204151983183255 1175571586806227974774883)
              ·
                refine ⟨1763357380209341962162325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175571586806227974774883 1763357380209341962162325)
                ·
                  refine ⟨82657377197312904476359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1763357380209341962162325 82657377197312904476359)
                  ·
                    rfl

theorem cell22_724386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_724386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724386 prefixEnd_724386 := by exact prefixLift 724386
  have htrace : WordTrace (prefixWord ++ tailWord_724386) baseStart_724386 baseEnd_724386 := by
    simpa [prefixWord, tailWord_724386, baseEnd_724386] using wordTrace_append hprefix tailTrace_724386
  have hstable : (prefixWord ++ tailWord_724386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724386).length < 2 ^ (prefixWord ++ tailWord_724386).sum := by decide
  have hdescent : baseEnd_724386 < baseStart_724386 := by decide
  rcases family_descends (prefixWord ++ tailWord_724386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724401 : List Nat := [1, 2, 2, 4, 1, 1, 3, 3, 2, 3]
def baseStart_724401 : Nat := 118140960795 + 724401 * 2 ^ 59
def prefixEnd_724401 : Nat := 4983230072969 + 3 ^ 40 * 724401 * 2
def baseEnd_724401 : Nat := 247977266398483674304031

theorem tailTrace_724401 : CollatzResearch.WordTrace tailWord_724401 prefixEnd_724401 247977266398483674304031 := by
  unfold tailWord_724401
  simp only [CollatzResearch.WordTrace]
  refine ⟨26421075048626369686229057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17614050032417579790819371 26421075048626369686229057)
  ·
    refine ⟨19815806286469777264671793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26421075048626369686229057 19815806286469777264671793)
    ·
      refine ⟨14861854714852332948503845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19815806286469777264671793 14861854714852332948503845)
      ·
        refine ⟨2786597759034812427844471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14861854714852332948503845 2786597759034812427844471)
        ·
          refine ⟨4179896638552218641766707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786597759034812427844471 4179896638552218641766707)
          ·
            refine ⟨6269844957828327962650061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4179896638552218641766707 6269844957828327962650061)
            ·
              refine ⟨2351191859185622985993773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6269844957828327962650061 2351191859185622985993773)
              ·
                refine ⟨881696947194608619747665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2351191859185622985993773 881696947194608619747665)
                ·
                  refine ⟨661272710395956464810749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 881696947194608619747665 661272710395956464810749)
                  ·
                    refine ⟨247977266398483674304031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661272710395956464810749 247977266398483674304031)
                    ·
                      rfl

theorem cell22_724401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_724401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724401 prefixEnd_724401 := by exact prefixLift 724401
  have htrace : WordTrace (prefixWord ++ tailWord_724401) baseStart_724401 baseEnd_724401 := by
    simpa [prefixWord, tailWord_724401, baseEnd_724401] using wordTrace_append hprefix tailTrace_724401
  have hstable : (prefixWord ++ tailWord_724401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724401).length < 2 ^ (prefixWord ++ tailWord_724401).sum := by decide
  have hdescent : baseEnd_724401 < baseStart_724401 := by decide
  rcases family_descends (prefixWord ++ tailWord_724401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724486 : List Nat := [6, 2, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_724486 : Nat := 118140960795 + 724486 * 2 ^ 59
def prefixEnd_724486 : Nat := 4983230072969 + 3 ^ 40 * 724486 * 2
def baseEnd_724486 : Nat := 248006363635571785928771

theorem tailTrace_724486 : CollatzResearch.WordTrace tailWord_724486 prefixEnd_724486 248006363635571785928771 := by
  unfold tailWord_724486
  simp only [CollatzResearch.WordTrace]
  refine ⟨825755476666200912596041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17616116835545619468715541 825755476666200912596041)
  ·
    refine ⟨619316607499650684447031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 825755476666200912596041 619316607499650684447031)
    ·
      refine ⟨928974911249476026670547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 619316607499650684447031 928974911249476026670547)
      ·
        refine ⟨1393462366874214040005821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928974911249476026670547 1393462366874214040005821)
        ·
          refine ⟨522548387577830265002183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1393462366874214040005821 522548387577830265002183)
          ·
            refine ⟨783822581366745397503275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522548387577830265002183 783822581366745397503275)
            ·
              refine ⟨1175733872050118096254913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783822581366745397503275 1175733872050118096254913)
              ·
                refine ⟨881800404037588572191185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175733872050118096254913 881800404037588572191185)
                ·
                  refine ⟨661350303028191429143389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 881800404037588572191185 661350303028191429143389)
                  ·
                    refine ⟨248006363635571785928771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661350303028191429143389 248006363635571785928771)
                    ·
                      rfl

theorem cell22_724486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_724486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724486 prefixEnd_724486 := by exact prefixLift 724486
  have htrace : WordTrace (prefixWord ++ tailWord_724486) baseStart_724486 baseEnd_724486 := by
    simpa [prefixWord, tailWord_724486, baseEnd_724486] using wordTrace_append hprefix tailTrace_724486
  have hstable : (prefixWord ++ tailWord_724486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724486).length < 2 ^ (prefixWord ++ tailWord_724486).sum := by decide
  have hdescent : baseEnd_724486 < baseStart_724486 := by decide
  rcases family_descends (prefixWord ++ tailWord_724486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724536 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 4, 3]
def baseStart_724536 : Nat := 118140960795 + 724536 * 2 ^ 59
def prefixEnd_724536 : Nat := 4983230072969 + 3 ^ 40 * 724536 * 2
def baseEnd_724536 : Nat := 248023479657388322178617

theorem tailTrace_724536 : CollatzResearch.WordTrace tailWord_724536 prefixEnd_724536 248023479657388322178617 := by
  unfold tailWord_724536
  simp only [CollatzResearch.WordTrace]
  refine ⟨13212999451568643871196731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17617332602091525161595641 13212999451568643871196731)
  ·
    refine ⟨19819499177352965806795097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13212999451568643871196731 19819499177352965806795097)
    ·
      refine ⟨14864624383014724355096323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19819499177352965806795097 14864624383014724355096323)
      ·
        refine ⟨22296936574522086532644485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14864624383014724355096323 22296936574522086532644485)
        ·
          refine ⟨4180675607722891224870841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22296936574522086532644485 4180675607722891224870841)
          ·
            refine ⟨3135506705792168418653131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4180675607722891224870841 3135506705792168418653131)
            ·
              refine ⟨4703260058688252627979697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3135506705792168418653131 4703260058688252627979697)
              ·
                refine ⟨3527445044016189470984773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4703260058688252627979697 3527445044016189470984773)
                ·
                  refine ⟨661395945753035525809645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3527445044016189470984773 661395945753035525809645)
                  ·
                    refine ⟨248023479657388322178617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661395945753035525809645 248023479657388322178617)
                    ·
                      rfl

theorem cell22_724536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_724536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724536 prefixEnd_724536 := by exact prefixLift 724536
  have htrace : WordTrace (prefixWord ++ tailWord_724536) baseStart_724536 baseEnd_724536 := by
    simpa [prefixWord, tailWord_724536, baseEnd_724536] using wordTrace_append hprefix tailTrace_724536
  have hstable : (prefixWord ++ tailWord_724536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724536).length < 2 ^ (prefixWord ++ tailWord_724536).sum := by decide
  have hdescent : baseEnd_724536 < baseStart_724536 := by decide
  rcases family_descends (prefixWord ++ tailWord_724536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724615 : List Nat := [1, 1, 4, 2, 1, 4, 1, 4, 1, 3]
def baseStart_724615 : Nat := 118140960795 + 724615 * 2 ^ 59
def prefixEnd_724615 : Nat := 4983230072969 + 3 ^ 40 * 724615 * 2
def baseEnd_724615 : Nat := 248050522971858449453375

theorem tailTrace_724615 : CollatzResearch.WordTrace tailWord_724615 prefixEnd_724615 248050522971858449453375 := by
  unfold tailWord_724615
  simp only [CollatzResearch.WordTrace]
  refine ⟨26428880269851084234519299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17619253513234056156346199 26428880269851084234519299)
  ·
    refine ⟨39643320404776626351778949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26428880269851084234519299 39643320404776626351778949)
    ·
      refine ⟨7433122575895617440958553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39643320404776626351778949 7433122575895617440958553)
      ·
        refine ⟨5574841931921713080718915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7433122575895617440958553 5574841931921713080718915)
        ·
          refine ⟨8362262897882569621078373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5574841931921713080718915 8362262897882569621078373)
          ·
            refine ⟨1567924293352981803952195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8362262897882569621078373 1567924293352981803952195)
            ·
              refine ⟨2351886440029472705928293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567924293352981803952195 2351886440029472705928293)
              ·
                refine ⟨440978707505526132361555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2351886440029472705928293 440978707505526132361555)
                ·
                  refine ⟨661468061258289198542333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440978707505526132361555 661468061258289198542333)
                  ·
                    refine ⟨248050522971858449453375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661468061258289198542333 248050522971858449453375)
                    ·
                      rfl

theorem cell22_724615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_724615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724615 prefixEnd_724615 := by exact prefixLift 724615
  have htrace : WordTrace (prefixWord ++ tailWord_724615) baseStart_724615 baseEnd_724615 := by
    simpa [prefixWord, tailWord_724615, baseEnd_724615] using wordTrace_append hprefix tailTrace_724615
  have hstable : (prefixWord ++ tailWord_724615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724615).length < 2 ^ (prefixWord ++ tailWord_724615).sum := by decide
  have hdescent : baseEnd_724615 < baseStart_724615 := by decide
  rcases family_descends (prefixWord ++ tailWord_724615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724662 : List Nat := [5, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_724662 : Nat := 118140960795 + 724662 * 2 ^ 59
def prefixEnd_724662 : Nat := 4983230072969 + 3 ^ 40 * 724662 * 2
def baseEnd_724662 : Nat := 82688870677455331176077

theorem tailTrace_724662 : CollatzResearch.WordTrace tailWord_724662 prefixEnd_724662 82688870677455331176077 := by
  unfold tailWord_724662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1651912156292550703842515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17620396333787207507653493 1651912156292550703842515)
  ·
    refine ⟨2477868234438826055763773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1651912156292550703842515 2477868234438826055763773)
    ·
      refine ⟨929200587914559770911415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2477868234438826055763773 929200587914559770911415)
      ·
        refine ⟨1393800881871839656367123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929200587914559770911415 1393800881871839656367123)
        ·
          refine ⟨2090701322807759484550685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393800881871839656367123 2090701322807759484550685)
          ·
            refine ⟨784012996052909806706507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2090701322807759484550685 784012996052909806706507)
            ·
              refine ⟨1176019494079364710059761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784012996052909806706507 1176019494079364710059761)
              ·
                refine ⟨882014620559523532544821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1176019494079364710059761 882014620559523532544821)
                ·
                  refine ⟨82688870677455331176077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 882014620559523532544821 82688870677455331176077)
                  ·
                    rfl

theorem cell22_724662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_724662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724662 prefixEnd_724662 := by exact prefixLift 724662
  have htrace : WordTrace (prefixWord ++ tailWord_724662) baseStart_724662 baseEnd_724662 := by
    simpa [prefixWord, tailWord_724662, baseEnd_724662] using wordTrace_append hprefix tailTrace_724662
  have hstable : (prefixWord ++ tailWord_724662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724662).length < 2 ^ (prefixWord ++ tailWord_724662).sum := by decide
  have hdescent : baseEnd_724662 < baseStart_724662 := by decide
  rcases family_descends (prefixWord ++ tailWord_724662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724686 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_724686 : Nat := 118140960795 + 724686 * 2 ^ 59
def prefixEnd_724686 : Nat := 4983230072969 + 3 ^ 40 * 724686 * 2
def baseEnd_724686 : Nat := 248074827722837930928157

theorem tailTrace_724686 : CollatzResearch.WordTrace tailWord_724686 prefixEnd_724686 248074827722837930928157 := by
  unfold tailWord_724686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3303933731574232920044239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17620979901729242240235941 3303933731574232920044239)
  ·
    refine ⟨4955900597361349380066359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3303933731574232920044239 4955900597361349380066359)
    ·
      refine ⟨7433850896042024070099539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4955900597361349380066359 7433850896042024070099539)
      ·
        refine ⟨11150776344063036105149309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7433850896042024070099539 11150776344063036105149309)
        ·
          refine ⟨4181541129023638539430991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11150776344063036105149309 4181541129023638539430991)
          ·
            refine ⟨6272311693535457809146487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4181541129023638539430991 6272311693535457809146487)
            ·
              refine ⟨9408467540303186713719731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272311693535457809146487 9408467540303186713719731)
              ·
                refine ⟨14112701310454780070579597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9408467540303186713719731 14112701310454780070579597)
                ·
                  refine ⟨5292262991420542526467349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14112701310454780070579597 5292262991420542526467349)
                  ·
                    refine ⟨248074827722837930928157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5292262991420542526467349 248074827722837930928157)
                    ·
                      rfl

theorem cell22_724686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_724686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724686 prefixEnd_724686 := by exact prefixLift 724686
  have htrace : WordTrace (prefixWord ++ tailWord_724686) baseStart_724686 baseEnd_724686 := by
    simpa [prefixWord, tailWord_724686, baseEnd_724686] using wordTrace_append hprefix tailTrace_724686
  have hstable : (prefixWord ++ tailWord_724686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724686).length < 2 ^ (prefixWord ++ tailWord_724686).sum := by decide
  have hdescent : baseEnd_724686 < baseStart_724686 := by decide
  rcases family_descends (prefixWord ++ tailWord_724686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724707 : List Nat := [1, 1, 1, 7, 2, 2, 1, 3, 4]
def baseStart_724707 : Nat := 118140960795 + 724707 * 2 ^ 59
def prefixEnd_724707 : Nat := 4983230072969 + 3 ^ 40 * 724707 * 2
def baseEnd_724707 : Nat := 82694005484000292051031

theorem tailTrace_724707 : CollatzResearch.WordTrace tailWord_724707 prefixEnd_724707 82694005484000292051031 := by
  unfold tailWord_724707
  simp only [CollatzResearch.WordTrace]
  refine ⟨26432235785517783946868375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17621490523678522631245583 26432235785517783946868375)
  ·
    refine ⟨39648353678276675920302563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26432235785517783946868375 39648353678276675920302563)
    ·
      refine ⟨59472530517415013880453845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39648353678276675920302563 59472530517415013880453845)
      ·
        refine ⟨1393887434001914387823137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 59472530517415013880453845 1393887434001914387823137)
        ·
          refine ⟨1045415575501435790867353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1393887434001914387823137 1045415575501435790867353)
          ·
            refine ⟨784061681626076843150515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1045415575501435790867353 784061681626076843150515)
            ·
              refine ⟨1176092522439115264725773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784061681626076843150515 1176092522439115264725773)
              ·
                refine ⟨441034695914668224272165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1176092522439115264725773 441034695914668224272165)
                ·
                  refine ⟨82694005484000292051031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441034695914668224272165 82694005484000292051031)
                  ·
                    rfl

theorem cell22_724707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 4].length) (baseStart_724707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724707 prefixEnd_724707 := by exact prefixLift 724707
  have htrace : WordTrace (prefixWord ++ tailWord_724707) baseStart_724707 baseEnd_724707 := by
    simpa [prefixWord, tailWord_724707, baseEnd_724707] using wordTrace_append hprefix tailTrace_724707
  have hstable : (prefixWord ++ tailWord_724707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724707).length < 2 ^ (prefixWord ++ tailWord_724707).sum := by decide
  have hdescent : baseEnd_724707 < baseStart_724707 := by decide
  rcases family_descends (prefixWord ++ tailWord_724707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724733 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_724733 : Nat := 118140960795 + 724733 * 2 ^ 59
def prefixEnd_724733 : Nat := 4983230072969 + 3 ^ 40 * 724733 * 2
def baseEnd_724733 : Nat := 248090916783345475003013

theorem tailTrace_724733 : CollatzResearch.WordTrace tailWord_724733 prefixEnd_724733 248090916783345475003013 := by
  unfold tailWord_724733
  simp only [CollatzResearch.WordTrace]
  refine ⟨26433184083423590387314853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17622122722282393591543235 26433184083423590387314853)
  ·
    refine ⟨4956222015641923197621535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26433184083423590387314853 4956222015641923197621535)
    ·
      refine ⟨7434333023462884796432303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4956222015641923197621535 7434333023462884796432303)
      ·
        refine ⟨11151499535194327194648455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434333023462884796432303 11151499535194327194648455)
        ·
          refine ⟨16727249302791490791972683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11151499535194327194648455 16727249302791490791972683)
          ·
            refine ⟨25090873954187236187959025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16727249302791490791972683 25090873954187236187959025)
            ·
              refine ⟨18818155465640427140969269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25090873954187236187959025 18818155465640427140969269)
              ·
                refine ⟨1764202074903790044465869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18818155465640427140969269 1764202074903790044465869)
                ·
                  refine ⟨661575778088921266674701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1764202074903790044465869 661575778088921266674701)
                  ·
                    refine ⟨248090916783345475003013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661575778088921266674701 248090916783345475003013)
                    ·
                      rfl

theorem cell22_724733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_724733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724733 prefixEnd_724733 := by exact prefixLift 724733
  have htrace : WordTrace (prefixWord ++ tailWord_724733) baseStart_724733 baseEnd_724733 := by
    simpa [prefixWord, tailWord_724733, baseEnd_724733] using wordTrace_append hprefix tailTrace_724733
  have hstable : (prefixWord ++ tailWord_724733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724733).length < 2 ^ (prefixWord ++ tailWord_724733).sum := by decide
  have hdescent : baseEnd_724733 < baseStart_724733 := by decide
  rcases family_descends (prefixWord ++ tailWord_724733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724808 : List Nat := [2, 1, 3, 1, 1, 5, 1, 2, 6]
def baseStart_724808 : Nat := 118140960795 + 724808 * 2 ^ 59
def prefixEnd_724808 : Nat := 4983230072969 + 3 ^ 40 * 724808 * 2
def baseEnd_724808 : Nat := 82705530272023426459261

theorem tailTrace_724808 : CollatzResearch.WordTrace tailWord_724808 prefixEnd_724808 82705530272023426459261 := by
  unfold tailWord_724808
  simp only [CollatzResearch.WordTrace]
  refine ⟨13217959779075939098147539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17623946372101252130863385 13217959779075939098147539)
  ·
    refine ⟨19826939668613908647221309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13217959779075939098147539 19826939668613908647221309)
    ·
      refine ⟨7435102375730215742707991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19826939668613908647221309 7435102375730215742707991)
      ·
        refine ⟨11152653563595323614061987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7435102375730215742707991 11152653563595323614061987)
        ·
          refine ⟨16728980345392985421092981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11152653563595323614061987 16728980345392985421092981)
          ·
            refine ⟨1568341907380592383227467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16728980345392985421092981 1568341907380592383227467)
            ·
              refine ⟨2352512861070888574841201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568341907380592383227467 2352512861070888574841201)
              ·
                refine ⟨1764384645803166431130901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2352512861070888574841201 1764384645803166431130901)
                ·
                  refine ⟨82705530272023426459261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1764384645803166431130901 82705530272023426459261)
                  ·
                    rfl

theorem cell22_724808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_724808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724808 prefixEnd_724808 := by exact prefixLift 724808
  have htrace : WordTrace (prefixWord ++ tailWord_724808) baseStart_724808 baseEnd_724808 := by
    simpa [prefixWord, tailWord_724808, baseEnd_724808] using wordTrace_append hprefix tailTrace_724808
  have hstable : (prefixWord ++ tailWord_724808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724808).length < 2 ^ (prefixWord ++ tailWord_724808).sum := by decide
  have hdescent : baseEnd_724808 < baseStart_724808 := by decide
  rcases family_descends (prefixWord ++ tailWord_724808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724825 : List Nat := [1, 2, 1, 2, 2, 3, 4, 3, 4]
def baseStart_724825 : Nat := 118140960795 + 724825 * 2 ^ 59
def prefixEnd_724825 : Nat := 4983230072969 + 3 ^ 40 * 724825 * 2
def baseEnd_724825 : Nat := 82707470087829300567577

theorem tailTrace_724825 : CollatzResearch.WordTrace tailWord_724825 prefixEnd_724825 82707470087829300567577 := by
  unfold tailWord_724825
  simp only [CollatzResearch.WordTrace]
  refine ⟨26436539599090290099663929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17624359732726860066442619 26436539599090290099663929)
  ·
    refine ⟨19827404699317717574747947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26436539599090290099663929 19827404699317717574747947)
    ·
      refine ⟨29741107048976576362121921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19827404699317717574747947 29741107048976576362121921)
      ·
        refine ⟨22305830286732432271591441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29741107048976576362121921 22305830286732432271591441)
        ·
          refine ⟨16729372715049324203693581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22305830286732432271591441 16729372715049324203693581)
          ·
            refine ⟨6273514768143496576385093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16729372715049324203693581 6273514768143496576385093)
            ·
              refine ⟨1176284019026905608072205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6273514768143496576385093 1176284019026905608072205)
              ·
                refine ⟨441106507135089603027077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1176284019026905608072205 441106507135089603027077)
                ·
                  refine ⟨82707470087829300567577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441106507135089603027077 82707470087829300567577)
                  ·
                    rfl

theorem cell22_724825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 3, 4].length) (baseStart_724825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724825 prefixEnd_724825 := by exact prefixLift 724825
  have htrace : WordTrace (prefixWord ++ tailWord_724825) baseStart_724825 baseEnd_724825 := by
    simpa [prefixWord, tailWord_724825, baseEnd_724825] using wordTrace_append hprefix tailTrace_724825
  have hstable : (prefixWord ++ tailWord_724825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724825).length < 2 ^ (prefixWord ++ tailWord_724825).sum := by decide
  have hdescent : baseEnd_724825 < baseStart_724825 := by decide
  rcases family_descends (prefixWord ++ tailWord_724825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724840 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 4, 3]
def baseStart_724840 : Nat := 118140960795 + 724840 * 2 ^ 59
def prefixEnd_724840 : Nat := 4983230072969 + 3 ^ 40 * 724840 * 2
def baseEnd_724840 : Nat := 248127545070032862577685

theorem tailTrace_724840 : CollatzResearch.WordTrace tailWord_724840 prefixEnd_724840 248127545070032862577685 := by
  unfold tailWord_724840
  simp only [CollatzResearch.WordTrace]
  refine ⟨13218543347017973830729987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17624724462690631774306649 13218543347017973830729987)
  ·
    refine ⟨19827815020526960746094981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13218543347017973830729987 19827815020526960746094981)
    ·
      refine ⟨3717715316348805139892809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19827815020526960746094981 3717715316348805139892809)
      ·
        refine ⟨2788286487261603854919607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3717715316348805139892809 2788286487261603854919607)
        ·
          refine ⟨4182429730892405782379411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788286487261603854919607 4182429730892405782379411)
          ·
            refine ⟨6273644596338608673569117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4182429730892405782379411 6273644596338608673569117)
            ·
              refine ⟨2352616723626978252588419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6273644596338608673569117 2352616723626978252588419)
              ·
                refine ⟨3528925085440467378882629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352616723626978252588419 3528925085440467378882629)
                ·
                  refine ⟨661673453520087633540493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3528925085440467378882629 661673453520087633540493)
                  ·
                    refine ⟨248127545070032862577685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661673453520087633540493 248127545070032862577685)
                    ·
                      rfl

theorem cell22_724840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_724840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724840 prefixEnd_724840 := by exact prefixLift 724840
  have htrace : WordTrace (prefixWord ++ tailWord_724840) baseStart_724840 baseEnd_724840 := by
    simpa [prefixWord, tailWord_724840, baseEnd_724840] using wordTrace_append hprefix tailTrace_724840
  have hstable : (prefixWord ++ tailWord_724840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724840).length < 2 ^ (prefixWord ++ tailWord_724840).sum := by decide
  have hdescent : baseEnd_724840 < baseStart_724840 := by decide
  rcases family_descends (prefixWord ++ tailWord_724840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724842 : List Nat := [3, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_724842 : Nat := 118140960795 + 724842 * 2 ^ 59
def prefixEnd_724842 : Nat := 4983230072969 + 3 ^ 40 * 724842 * 2
def baseEnd_724842 : Nat := 82709409903635174675893

theorem tailTrace_724842 : CollatzResearch.WordTrace tailWord_724842 prefixEnd_724842 82709409903635174675893 := by
  unfold tailWord_724842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609289910007175500758195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17624773093352468002021853 6609289910007175500758195)
  ·
    refine ⟨9913934865010763251137293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6609289910007175500758195 9913934865010763251137293)
    ·
      refine ⟨3717725574379036219176485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9913934865010763251137293 3717725574379036219176485)
      ·
        refine ⟨697073545196069291095591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3717725574379036219176485 697073545196069291095591)
        ·
          refine ⟨1045610317794103936643387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697073545196069291095591 1045610317794103936643387)
          ·
            refine ⟨1568415476691155904965081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045610317794103936643387 1568415476691155904965081)
            ·
              refine ⟨1176311607518366928723811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568415476691155904965081 1176311607518366928723811)
              ·
                refine ⟨1764467411277550393085717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176311607518366928723811 1764467411277550393085717)
                ·
                  refine ⟨82709409903635174675893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1764467411277550393085717 82709409903635174675893)
                  ·
                    rfl

theorem cell22_724842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_724842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724842 prefixEnd_724842 := by exact prefixLift 724842
  have htrace : WordTrace (prefixWord ++ tailWord_724842) baseStart_724842 baseEnd_724842 := by
    simpa [prefixWord, tailWord_724842, baseEnd_724842] using wordTrace_append hprefix tailTrace_724842
  have hstable : (prefixWord ++ tailWord_724842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724842).length < 2 ^ (prefixWord ++ tailWord_724842).sum := by decide
  have hdescent : baseEnd_724842 < baseStart_724842 := by decide
  rcases family_descends (prefixWord ++ tailWord_724842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724853 : List Nat := [1, 3, 4, 1, 1, 1, 2, 9]
def baseStart_724853 : Nat := 118140960795 + 724853 * 2 ^ 59
def prefixEnd_724853 : Nat := 4983230072969 + 3 ^ 40 * 724853 * 2
def baseEnd_724853 : Nat := 27570221692856129111405

theorem tailTrace_724853 : CollatzResearch.WordTrace tailWord_724853 prefixEnd_724853 27570221692856129111405 := by
  unfold tailWord_724853
  simp only [CollatzResearch.WordTrace]
  refine ⟨26437560842988850881683213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17625040561992567254455475 26437560842988850881683213)
  ·
    refine ⟨9914085316120819080631205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26437560842988850881683213 9914085316120819080631205)
    ·
      refine ⟨1858890996772653577618351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9914085316120819080631205 1858890996772653577618351)
      ·
        refine ⟨2788336495158980366427527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1858890996772653577618351 2788336495158980366427527)
        ·
          refine ⟨4182504742738470549641291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788336495158980366427527 4182504742738470549641291)
          ·
            refine ⟨6273757114107705824461937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4182504742738470549641291 6273757114107705824461937)
            ·
              refine ⟨4705317835580779368346453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6273757114107705824461937 4705317835580779368346453)
              ·
                refine ⟨27570221692856129111405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4705317835580779368346453 27570221692856129111405)
                ·
                  rfl

theorem cell22_724853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 9].length) (baseStart_724853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724853 prefixEnd_724853 := by exact prefixLift 724853
  have htrace : WordTrace (prefixWord ++ tailWord_724853) baseStart_724853 baseEnd_724853 := by
    simpa [prefixWord, tailWord_724853, baseEnd_724853] using wordTrace_append hprefix tailTrace_724853
  have hstable : (prefixWord ++ tailWord_724853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724853).length < 2 ^ (prefixWord ++ tailWord_724853).sum := by decide
  have hdescent : baseEnd_724853 < baseStart_724853 := by decide
  rcases family_descends (prefixWord ++ tailWord_724853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724857 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 2, 3]
def baseStart_724857 : Nat := 118140960795 + 724857 * 2 ^ 59
def prefixEnd_724857 : Nat := 4983230072969 + 3 ^ 40 * 724857 * 2
def baseEnd_724857 : Nat := 248133364517450484902633

theorem tailTrace_724857 : CollatzResearch.WordTrace tailWord_724857 prefixEnd_724857 248133364517450484902633 := by
  unfold tailWord_724857
  simp only [CollatzResearch.WordTrace]
  refine ⟨26437706734974359564828825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17625137823316239709885883 26437706734974359564828825)
  ·
    refine ⟨19828280051230769673621619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26437706734974359564828825 19828280051230769673621619)
    ·
      refine ⟨29742420076846154510432429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19828280051230769673621619 29742420076846154510432429)
      ·
        refine ⟨11153407528817307941412161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29742420076846154510432429 11153407528817307941412161)
        ·
          refine ⟨8365055646612980956059121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11153407528817307941412161 8365055646612980956059121)
          ·
            refine ⟨6273791734959735717044341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8365055646612980956059121 6273791734959735717044341)
            ·
              refine ⟨588167975152475223472907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6273791734959735717044341 588167975152475223472907)
              ·
                refine ⟨882251962728712835209361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588167975152475223472907 882251962728712835209361)
                ·
                  refine ⟨661688972046534626407021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 882251962728712835209361 661688972046534626407021)
                  ·
                    refine ⟨248133364517450484902633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661688972046534626407021 248133364517450484902633)
                    ·
                      rfl

theorem cell22_724857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 3].length) (baseStart_724857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724857 prefixEnd_724857 := by exact prefixLift 724857
  have htrace : WordTrace (prefixWord ++ tailWord_724857) baseStart_724857 baseEnd_724857 := by
    simpa [prefixWord, tailWord_724857, baseEnd_724857] using wordTrace_append hprefix tailTrace_724857
  have hstable : (prefixWord ++ tailWord_724857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724857).length < 2 ^ (prefixWord ++ tailWord_724857).sum := by decide
  have hdescent : baseEnd_724857 < baseStart_724857 := by decide
  rcases family_descends (prefixWord ++ tailWord_724857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724953 : List Nat := [1, 2, 1, 2, 7, 1, 2, 2, 1, 3]
def baseStart_724953 : Nat := 118140960795 + 724953 * 2 ^ 59
def prefixEnd_724953 : Nat := 4983230072969 + 3 ^ 40 * 724953 * 2
def baseEnd_724953 : Nat := 248166227279338234502339

theorem tailTrace_724953 : CollatzResearch.WordTrace tailWord_724953 prefixEnd_724953 248166227279338234502339 := by
  unfold tailWord_724953
  simp only [CollatzResearch.WordTrace]
  refine ⟨26441208142626567960323513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17627472095084378640215675 26441208142626567960323513)
  ·
    refine ⟨19830906106969925970242635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26441208142626567960323513 19830906106969925970242635)
    ·
      refine ⟨29746359160454888955363953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19830906106969925970242635 29746359160454888955363953)
      ·
        refine ⟨22309769370341166716522965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29746359160454888955363953 22309769370341166716522965)
        ·
          refine ⟨522885219617371094918507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 22309769370341166716522965 522885219617371094918507)
          ·
            refine ⟨784327829426056642377761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522885219617371094918507 784327829426056642377761)
            ·
              refine ⟨588245872069542481783321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784327829426056642377761 588245872069542481783321)
              ·
                refine ⟨441184404052156861337491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588245872069542481783321 441184404052156861337491)
                ·
                  refine ⟨661776606078235292006237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441184404052156861337491 661776606078235292006237)
                  ·
                    refine ⟨248166227279338234502339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661776606078235292006237 248166227279338234502339)
                    ·
                      rfl

theorem cell22_724953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 1, 3].length) (baseStart_724953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724953 prefixEnd_724953 := by exact prefixLift 724953
  have htrace : WordTrace (prefixWord ++ tailWord_724953) baseStart_724953 baseEnd_724953 := by
    simpa [prefixWord, tailWord_724953, baseEnd_724953] using wordTrace_append hprefix tailTrace_724953
  have hstable : (prefixWord ++ tailWord_724953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724953).length < 2 ^ (prefixWord ++ tailWord_724953).sum := by decide
  have hdescent : baseEnd_724953 < baseStart_724953 := by decide
  rcases family_descends (prefixWord ++ tailWord_724953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724975 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 1, 5]
def baseStart_724975 : Nat := 118140960795 + 724975 * 2 ^ 59
def prefixEnd_724975 : Nat := 4983230072969 + 3 ^ 40 * 724975 * 2
def baseEnd_724975 : Nat := 248173758328937510452271

theorem tailTrace_724975 : CollatzResearch.WordTrace tailWord_724975 prefixEnd_724975 248173758328937510452271 := by
  unfold tailWord_724975
  simp only [CollatzResearch.WordTrace]
  refine ⟨26442010548546865717624379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17628007032364577145082919 26442010548546865717624379)
  ·
    refine ⟨39663015822820298576436569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26442010548546865717624379 39663015822820298576436569)
    ·
      refine ⟨29747261867115223932327427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39663015822820298576436569 29747261867115223932327427)
      ·
        refine ⟨44620892800672835898491141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29747261867115223932327427 44620892800672835898491141)
        ·
          refine ⟨8366417400126156730967089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44620892800672835898491141 8366417400126156730967089)
          ·
            refine ⟨6274813050094617548225317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8366417400126156730967089 6274813050094617548225317)
            ·
              refine ⟨1176527446892740790292247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6274813050094617548225317 1176527446892740790292247)
              ·
                refine ⟨1764791170339111185438371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176527446892740790292247 1764791170339111185438371)
                ·
                  refine ⟨2647186755508666778157557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1764791170339111185438371 2647186755508666778157557)
                  ·
                    refine ⟨248173758328937510452271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2647186755508666778157557 248173758328937510452271)
                    ·
                      rfl

theorem cell22_724975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_724975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_724975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_724975 prefixEnd_724975 := by exact prefixLift 724975
  have htrace : WordTrace (prefixWord ++ tailWord_724975) baseStart_724975 baseEnd_724975 := by
    simpa [prefixWord, tailWord_724975, baseEnd_724975] using wordTrace_append hprefix tailTrace_724975
  have hstable : (prefixWord ++ tailWord_724975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724975).length < 2 ^ (prefixWord ++ tailWord_724975).sum := by decide
  have hdescent : baseEnd_724975 < baseStart_724975 := by decide
  rcases family_descends (prefixWord ++ tailWord_724975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725084 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 5]
def baseStart_725084 : Nat := 118140960795 + 725084 * 2 ^ 59
def prefixEnd_725084 : Nat := 4983230072969 + 3 ^ 40 * 725084 * 2
def baseEnd_725084 : Nat := 82737023752165853158979

theorem tailTrace_725084 : CollatzResearch.WordTrace tailWord_725084 prefixEnd_725084 82737023752165853158979 := by
  unfold tailWord_725084
  simp only [CollatzResearch.WordTrace]
  refine ⟨13222993052575988666671153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17630657403434651555561537 13222993052575988666671153)
  ·
    refine ⟨9917244789431991500003365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13222993052575988666671153 9917244789431991500003365)
    ·
      refine ⟨1859483398018498406250631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9917244789431991500003365 1859483398018498406250631)
      ·
        refine ⟨2789225097027747609375947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859483398018498406250631 2789225097027747609375947)
        ·
          refine ⟨4183837645541621414063921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2789225097027747609375947 4183837645541621414063921)
          ·
            refine ⟨3137878234156216060547941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4183837645541621414063921 3137878234156216060547941)
            ·
              refine ⟨588352168904290511352739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3137878234156216060547941 588352168904290511352739)
              ·
                refine ⟨882528253356435767029109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588352168904290511352739 882528253356435767029109)
                ·
                  refine ⟨82737023752165853158979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 882528253356435767029109 82737023752165853158979)
                  ·
                    rfl

theorem cell22_725084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_725084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725084 prefixEnd_725084 := by exact prefixLift 725084
  have htrace : WordTrace (prefixWord ++ tailWord_725084) baseStart_725084 baseEnd_725084 := by
    simpa [prefixWord, tailWord_725084, baseEnd_725084] using wordTrace_append hprefix tailTrace_725084
  have hstable : (prefixWord ++ tailWord_725084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725084).length < 2 ^ (prefixWord ++ tailWord_725084).sum := by decide
  have hdescent : baseEnd_725084 < baseStart_725084 := by decide
  rcases family_descends (prefixWord ++ tailWord_725084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725095 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 8]
def baseStart_725095 : Nat := 118140960795 + 725095 * 2 ^ 59
def prefixEnd_725095 : Nat := 4983230072969 + 3 ^ 40 * 725095 * 2
def baseEnd_725095 : Nat := 82738278927099065817301

theorem tailTrace_725095 : CollatzResearch.WordTrace tailWord_725095 prefixEnd_725095 82738278927099065817301 := by
  unfold tailWord_725095
  simp only [CollatzResearch.WordTrace]
  refine ⟨26446387308112126211992739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17630924872074750807995159 26446387308112126211992739)
  ·
    refine ⟨39669580962168189317989109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26446387308112126211992739 39669580962168189317989109)
    ·
      refine ⟨3719023215203267748561479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39669580962168189317989109 3719023215203267748561479)
      ·
        refine ⟨5578534822804901622842219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719023215203267748561479 5578534822804901622842219)
        ·
          refine ⟨8367802234207352434263329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5578534822804901622842219 8367802234207352434263329)
          ·
            refine ⟨6275851675655514325697497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8367802234207352434263329 6275851675655514325697497)
            ·
              refine ⟨4706888756741635744273123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6275851675655514325697497 4706888756741635744273123)
              ·
                refine ⟨7060333135112453616409685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4706888756741635744273123 7060333135112453616409685)
                ·
                  refine ⟨82738278927099065817301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7060333135112453616409685 82738278927099065817301)
                  ·
                    rfl

theorem cell22_725095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 8].length) (baseStart_725095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725095 prefixEnd_725095 := by exact prefixLift 725095
  have htrace : WordTrace (prefixWord ++ tailWord_725095) baseStart_725095 baseEnd_725095 := by
    simpa [prefixWord, tailWord_725095, baseEnd_725095] using wordTrace_append hprefix tailTrace_725095
  have hstable : (prefixWord ++ tailWord_725095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725095).length < 2 ^ (prefixWord ++ tailWord_725095).sum := by decide
  have hdescent : baseEnd_725095 < baseStart_725095 := by decide
  rcases family_descends (prefixWord ++ tailWord_725095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725112 : List Nat := [2, 1, 2, 1, 1, 1, 3, 7, 4]
def baseStart_725112 : Nat := 118140960795 + 725112 * 2 ^ 59
def prefixEnd_725112 : Nat := 4983230072969 + 3 ^ 40 * 725112 * 2
def baseEnd_725112 : Nat := 82740218742904939925617

theorem tailTrace_725112 : CollatzResearch.WordTrace tailWord_725112 prefixEnd_725112 82740218742904939925617 := by
  unfold tailWord_725112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223503674525269057680795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17631338232700358743574393 13223503674525269057680795)
  ·
    refine ⟨19835255511787903586521193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13223503674525269057680795 19835255511787903586521193)
    ·
      refine ⟨14876441633840927689890895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19835255511787903586521193 14876441633840927689890895)
      ·
        refine ⟨22314662450761391534836343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14876441633840927689890895 22314662450761391534836343)
        ·
          refine ⟨33471993676142087302254515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22314662450761391534836343 33471993676142087302254515)
          ·
            refine ⟨50207990514213130953381773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33471993676142087302254515 50207990514213130953381773)
            ·
              refine ⟨18827996442829924107518165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50207990514213130953381773 18827996442829924107518165)
              ·
                refine ⟨441281166628826346269957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18827996442829924107518165 441281166628826346269957)
                ·
                  refine ⟨82740218742904939925617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441281166628826346269957 82740218742904939925617)
                  ·
                    rfl

theorem cell22_725112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 7, 4].length) (baseStart_725112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725112 prefixEnd_725112 := by exact prefixLift 725112
  have htrace : WordTrace (prefixWord ++ tailWord_725112) baseStart_725112 baseEnd_725112 := by
    simpa [prefixWord, tailWord_725112, baseEnd_725112] using wordTrace_append hprefix tailTrace_725112
  have hstable : (prefixWord ++ tailWord_725112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725112).length < 2 ^ (prefixWord ++ tailWord_725112).sum := by decide
  have hdescent : baseEnd_725112 < baseStart_725112 := by decide
  rcases family_descends (prefixWord ++ tailWord_725112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725127 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 4, 3]
def baseStart_725127 : Nat := 118140960795 + 725127 * 2 ^ 59
def prefixEnd_725127 : Nat := 4983230072969 + 3 ^ 40 * 725127 * 2
def baseEnd_725127 : Nat := 248225791035259780651805

theorem tailTrace_725127 : CollatzResearch.WordTrace tailWord_725127 prefixEnd_725127 248225791035259780651805 := by
  unfold tailWord_725127
  simp only [CollatzResearch.WordTrace]
  refine ⟨26447554443996195677157635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17631702962664130451438423 26447554443996195677157635)
  ·
    refine ⟨39671331665994293515736453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26447554443996195677157635 39671331665994293515736453)
    ·
      refine ⟨7438374687373930034200585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39671331665994293515736453 7438374687373930034200585)
      ·
        refine ⟨5578781015530447525650439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7438374687373930034200585 5578781015530447525650439)
        ·
          refine ⟨8368171523295671288475659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5578781015530447525650439 8368171523295671288475659)
          ·
            refine ⟨12552257284943506932713489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8368171523295671288475659 12552257284943506932713489)
            ·
              refine ⟨9414192963707630199535117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12552257284943506932713489 9414192963707630199535117)
              ·
                refine ⟨3530322361390361324825669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9414192963707630199535117 3530322361390361324825669)
                ·
                  refine ⟨661935442760692748404813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3530322361390361324825669 661935442760692748404813)
                  ·
                    refine ⟨248225791035259780651805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 661935442760692748404813 248225791035259780651805)
                    ·
                      rfl

theorem cell22_725127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_725127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725127 prefixEnd_725127 := by exact prefixLift 725127
  have htrace : WordTrace (prefixWord ++ tailWord_725127) baseStart_725127 baseEnd_725127 := by
    simpa [prefixWord, tailWord_725127, baseEnd_725127] using wordTrace_append hprefix tailTrace_725127
  have hstable : (prefixWord ++ tailWord_725127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725127).length < 2 ^ (prefixWord ++ tailWord_725127).sum := by decide
  have hdescent : baseEnd_725127 < baseStart_725127 := by decide
  rcases family_descends (prefixWord ++ tailWord_725127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725144 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_725144 : Nat := 118140960795 + 725144 * 2 ^ 59
def prefixEnd_725144 : Nat := 4983230072969 + 3 ^ 40 * 725144 * 2
def baseEnd_725144 : Nat := 248231610482677402976753

theorem tailTrace_725144 : CollatzResearch.WordTrace tailWord_725144 prefixEnd_725144 248231610482677402976753 := by
  unfold tailWord_725144
  simp only [CollatzResearch.WordTrace]
  refine ⟨13224087242467303790263243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17632116323289738387017657 13224087242467303790263243)
  ·
    refine ⟨19836130863700955685394865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13224087242467303790263243 19836130863700955685394865)
    ·
      refine ⟨14877098147775716764046149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19836130863700955685394865 14877098147775716764046149)
      ·
        refine ⟨2789455902707946893258653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14877098147775716764046149 2789455902707946893258653)
        ·
          refine ⟨1046045963515480084971995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2789455902707946893258653 1046045963515480084971995)
          ·
            refine ⟨1569068945273220127457993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046045963515480084971995 1569068945273220127457993)
            ·
              refine ⟨1176801708954915095593495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569068945273220127457993 1176801708954915095593495)
              ·
                refine ⟨1765202563432372643390243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176801708954915095593495 1765202563432372643390243)
                ·
                  refine ⟨2647803845148558965085365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765202563432372643390243 2647803845148558965085365)
                  ·
                    refine ⟨248231610482677402976753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2647803845148558965085365 248231610482677402976753)
                    ·
                      rfl

theorem cell22_725144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_725144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725144 prefixEnd_725144 := by exact prefixLift 725144
  have htrace : WordTrace (prefixWord ++ tailWord_725144) baseStart_725144 baseEnd_725144 := by
    simpa [prefixWord, tailWord_725144, baseEnd_725144] using wordTrace_append hprefix tailTrace_725144
  have hstable : (prefixWord ++ tailWord_725144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725144).length < 2 ^ (prefixWord ++ tailWord_725144).sum := by decide
  have hdescent : baseEnd_725144 < baseStart_725144 := by decide
  rcases family_descends (prefixWord ++ tailWord_725144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725157 : List Nat := [1, 3, 1, 2, 1, 3, 5, 6]
def baseStart_725157 : Nat := 118140960795 + 725157 * 2 ^ 59
def prefixEnd_725157 : Nat := 4983230072969 + 3 ^ 40 * 725157 * 2
def baseEnd_725157 : Nat := 27581784516483300266857

theorem tailTrace_725157 : CollatzResearch.WordTrace tailWord_725157 prefixEnd_725157 27581784516483300266857 := by
  unfold tailWord_725157
  simp only [CollatzResearch.WordTrace]
  refine ⟨26448648633887510800749725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17632432422591673867166483 26448648633887510800749725)
  ·
    refine ⟨9918243237707816550281147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26448648633887510800749725 9918243237707816550281147)
    ·
      refine ⟨14877364856561724825421721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9918243237707816550281147 14877364856561724825421721)
      ·
        refine ⟨11158023642421293619066291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14877364856561724825421721 11158023642421293619066291)
        ·
          refine ⟨16737035463631940428599437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11158023642421293619066291 16737035463631940428599437)
          ·
            refine ⟨6276388298861977660724789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16737035463631940428599437 6276388298861977660724789)
            ·
              refine ⟨588411403018310405692949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6276388298861977660724789 588411403018310405692949)
              ·
                refine ⟨27581784516483300266857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 588411403018310405692949 27581784516483300266857)
                ·
                  rfl

theorem cell22_725157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 6].length) (baseStart_725157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725157 prefixEnd_725157 := by exact prefixLift 725157
  have htrace : WordTrace (prefixWord ++ tailWord_725157) baseStart_725157 baseEnd_725157 := by
    simpa [prefixWord, tailWord_725157, baseEnd_725157] using wordTrace_append hprefix tailTrace_725157
  have hstable : (prefixWord ++ tailWord_725157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725157).length < 2 ^ (prefixWord ++ tailWord_725157).sum := by decide
  have hdescent : baseEnd_725157 < baseStart_725157 := by decide
  rcases family_descends (prefixWord ++ tailWord_725157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725159 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 1, 6]
def baseStart_725159 : Nat := 118140960795 + 725159 * 2 ^ 59
def prefixEnd_725159 : Nat := 4983230072969 + 3 ^ 40 * 725159 * 2
def baseEnd_725159 : Nat := 248236745289222363851707

theorem tailTrace_725159 : CollatzResearch.WordTrace tailWord_725159 prefixEnd_725159 248236745289222363851707 := by
  unfold tailWord_725159
  simp only [CollatzResearch.WordTrace]
  refine ⟨26448721579880265142322531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17632481053253510094881687 26448721579880265142322531)
  ·
    refine ⟨39673082369820397713483797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26448721579880265142322531 39673082369820397713483797)
    ·
      refine ⟨1859675736085331142819553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39673082369820397713483797 1859675736085331142819553)
      ·
        refine ⟨1394756802063998357114665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1859675736085331142819553 1394756802063998357114665)
        ·
          refine ⟨1046067601547998767835999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1394756802063998357114665 1046067601547998767835999)
          ·
            refine ⟨1569101402321998151753999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046067601547998767835999 1569101402321998151753999)
            ·
              refine ⟨2353652103482997227630999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569101402321998151753999 2353652103482997227630999)
              ·
                refine ⟨3530478155224495841446499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2353652103482997227630999 3530478155224495841446499)
                ·
                  refine ⟨5295717232836743762169749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3530478155224495841446499 5295717232836743762169749)
                  ·
                    refine ⟨248236745289222363851707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5295717232836743762169749 248236745289222363851707)
                    ·
                      rfl

theorem cell22_725159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_725159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725159 prefixEnd_725159 := by exact prefixLift 725159
  have htrace : WordTrace (prefixWord ++ tailWord_725159) baseStart_725159 baseEnd_725159 := by
    simpa [prefixWord, tailWord_725159, baseEnd_725159] using wordTrace_append hprefix tailTrace_725159
  have hstable : (prefixWord ++ tailWord_725159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725159).length < 2 ^ (prefixWord ++ tailWord_725159).sum := by decide
  have hdescent : baseEnd_725159 < baseStart_725159 := by decide
  rcases family_descends (prefixWord ++ tailWord_725159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725223 : List Nat := [1, 1, 5, 3, 1, 1, 3, 3, 1, 3]
def baseStart_725223 : Nat := 118140960795 + 725223 * 2 ^ 59
def prefixEnd_725223 : Nat := 4983230072969 + 3 ^ 40 * 725223 * 2
def baseEnd_725223 : Nat := 248258653797147530251511

theorem tailTrace_725223 : CollatzResearch.WordTrace tailWord_725223 prefixEnd_725223 248258653797147530251511 := by
  unfold tailWord_725223
  simp only [CollatzResearch.WordTrace]
  refine ⟨26451055851648404072652323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17634037234432269381768215 26451055851648404072652323)
  ·
    refine ⟨39676583777472606108978485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26451055851648404072652323 39676583777472606108978485)
    ·
      refine ⟨3719679729138056822716733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39676583777472606108978485 3719679729138056822716733)
      ·
        refine ⟨1394879898426771308518775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3719679729138056822716733 1394879898426771308518775)
        ·
          refine ⟨2092319847640156962778163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394879898426771308518775 2092319847640156962778163)
          ·
            refine ⟨3138479771460235444167245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092319847640156962778163 3138479771460235444167245)
            ·
              refine ⟨1176929914297588291562717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3138479771460235444167245 1176929914297588291562717)
              ·
                refine ⟨441348717861595609336019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1176929914297588291562717 441348717861595609336019)
                ·
                  refine ⟨662023076792393414004029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441348717861595609336019 662023076792393414004029)
                  ·
                    refine ⟨248258653797147530251511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 662023076792393414004029 248258653797147530251511)
                    ·
                      rfl

theorem cell22_725223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_725223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725223 prefixEnd_725223 := by exact prefixLift 725223
  have htrace : WordTrace (prefixWord ++ tailWord_725223) baseStart_725223 baseEnd_725223 := by
    simpa [prefixWord, tailWord_725223, baseEnd_725223] using wordTrace_append hprefix tailTrace_725223
  have hstable : (prefixWord ++ tailWord_725223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725223).length < 2 ^ (prefixWord ++ tailWord_725223).sum := by decide
  have hdescent : baseEnd_725223 < baseStart_725223 := by decide
  rcases family_descends (prefixWord ++ tailWord_725223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725279 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 1, 5]
def baseStart_725279 : Nat := 118140960795 + 725279 * 2 ^ 59
def prefixEnd_725279 : Nat := 4983230072969 + 3 ^ 40 * 725279 * 2
def baseEnd_725279 : Nat := 248277823741582050851339

theorem tailTrace_725279 : CollatzResearch.WordTrace tailWord_725279 prefixEnd_725279 248277823741582050851339 := by
  unfold tailWord_725279
  simp only [CollatzResearch.WordTrace]
  refine ⟨26453098339445525636690891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17635398892963683757793927 26453098339445525636690891)
  ·
    refine ⟨39679647509168288455036337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26453098339445525636690891 39679647509168288455036337)
    ·
      refine ⟨29759735631876216341277253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39679647509168288455036337 29759735631876216341277253)
      ·
        refine ⟨5579950430976790563989485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29759735631876216341277253 5579950430976790563989485)
        ·
          refine ⟨2092481411616296461496057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5579950430976790563989485 2092481411616296461496057)
          ·
            refine ⟨1569361058712222346122043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2092481411616296461496057 1569361058712222346122043)
            ·
              refine ⟨2354041588068333519183065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569361058712222346122043 2354041588068333519183065)
              ·
                refine ⟨1765531191051250139387299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2354041588068333519183065 1765531191051250139387299)
                ·
                  refine ⟨2648296786576875209080949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765531191051250139387299 2648296786576875209080949)
                  ·
                    refine ⟨248277823741582050851339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2648296786576875209080949 248277823741582050851339)
                    ·
                      rfl

theorem cell22_725279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_725279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725279 prefixEnd_725279 := by exact prefixLift 725279
  have htrace : WordTrace (prefixWord ++ tailWord_725279) baseStart_725279 baseEnd_725279 := by
    simpa [prefixWord, tailWord_725279, baseEnd_725279] using wordTrace_append hprefix tailTrace_725279
  have hstable : (prefixWord ++ tailWord_725279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725279).length < 2 ^ (prefixWord ++ tailWord_725279).sum := by decide
  have hdescent : baseEnd_725279 < baseStart_725279 := by decide
  rcases family_descends (prefixWord ++ tailWord_725279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725337 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 7]
def baseStart_725337 : Nat := 118140960795 + 725337 * 2 ^ 59
def prefixEnd_725337 : Nat := 4983230072969 + 3 ^ 40 * 725337 * 2
def baseEnd_725337 : Nat := 82765892775629744300387

theorem tailTrace_725337 : CollatzResearch.WordTrace tailWord_725337 prefixEnd_725337 82765892775629744300387 := by
  unfold tailWord_725337
  simp only [CollatzResearch.WordTrace]
  refine ⟨26455213773235401542302265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17636809182156934361534843 26455213773235401542302265)
  ·
    refine ⟨19841410329926551156726699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26455213773235401542302265 19841410329926551156726699)
    ·
      refine ⟨29762115494889826735090049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19841410329926551156726699 29762115494889826735090049)
      ·
        refine ⟨22321586621167370051317537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29762115494889826735090049 22321586621167370051317537)
        ·
          refine ⟨16741189965875527538488153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22321586621167370051317537 16741189965875527538488153)
          ·
            refine ⟨12555892474406645653866115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16741189965875527538488153 12555892474406645653866115)
            ·
              refine ⟨18833838711609968480799173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12555892474406645653866115 18833838711609968480799173)
              ·
                refine ⟨3531344758426869090149845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18833838711609968480799173 3531344758426869090149845)
                ·
                  refine ⟨82765892775629744300387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3531344758426869090149845 82765892775629744300387)
                  ·
                    rfl

theorem cell22_725337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_725337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725337 prefixEnd_725337 := by exact prefixLift 725337
  have htrace : WordTrace (prefixWord ++ tailWord_725337) baseStart_725337 baseEnd_725337 := by
    simpa [prefixWord, tailWord_725337, baseEnd_725337] using wordTrace_append hprefix tailTrace_725337
  have hstable : (prefixWord ++ tailWord_725337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725337).length < 2 ^ (prefixWord ++ tailWord_725337).sum := by decide
  have hdescent : baseEnd_725337 < baseStart_725337 := by decide
  rcases family_descends (prefixWord ++ tailWord_725337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725367 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 2, 8]
def baseStart_725367 : Nat := 118140960795 + 725367 * 2 ^ 59
def prefixEnd_725367 : Nat := 4983230072969 + 3 ^ 40 * 725367 * 2
def baseEnd_725367 : Nat := 248307947939979154651069

theorem tailTrace_725367 : CollatzResearch.WordTrace tailWord_725367 prefixEnd_725367 248307947939979154651069 := by
  unfold tailWord_725367
  simp only [CollatzResearch.WordTrace]
  refine ⟨26456307963126716665894355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17637538642084477777262903 26456307963126716665894355)
  ·
    refine ⟨39684461944690074998841533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26456307963126716665894355 39684461944690074998841533)
    ·
      refine ⟨14881673229258778124565575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39684461944690074998841533 14881673229258778124565575)
      ·
        refine ⟨22322509843888167186848363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14881673229258778124565575 22322509843888167186848363)
        ·
          refine ⟨33483764765832250780272545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22322509843888167186848363 33483764765832250780272545)
          ·
            refine ⟨25112823574374188085204409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33483764765832250780272545 25112823574374188085204409)
            ·
              refine ⟨18834617680780641063903307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25112823574374188085204409 18834617680780641063903307)
              ·
                refine ⟨28251926521170961595854961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18834617680780641063903307 28251926521170961595854961)
                ·
                  refine ⟨21188944890878221196891221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28251926521170961595854961 21188944890878221196891221)
                  ·
                    refine ⟨248307947939979154651069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21188944890878221196891221 248307947939979154651069)
                    ·
                      rfl

theorem cell22_725367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_725367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725367 prefixEnd_725367 := by exact prefixLift 725367
  have htrace : WordTrace (prefixWord ++ tailWord_725367) baseStart_725367 baseEnd_725367 := by
    simpa [prefixWord, tailWord_725367, baseEnd_725367] using wordTrace_append hprefix tailTrace_725367
  have hstable : (prefixWord ++ tailWord_725367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725367).length < 2 ^ (prefixWord ++ tailWord_725367).sum := by decide
  have hdescent : baseEnd_725367 < baseStart_725367 := by decide
  rcases family_descends (prefixWord ++ tailWord_725367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725371 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 5]
def baseStart_725371 : Nat := 118140960795 + 725371 * 2 ^ 59
def prefixEnd_725371 : Nat := 4983230072969 + 3 ^ 40 * 725371 * 2
def baseEnd_725371 : Nat := 82769772407241492517019

theorem tailTrace_725371 : CollatzResearch.WordTrace tailWord_725371 prefixEnd_725371 82769772407241492517019 := by
  unfold tailWord_725371
  simp only [CollatzResearch.WordTrace]
  refine ⟨26456453855112225349039967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17637635903408150232693311 26456453855112225349039967)
  ·
    refine ⟨39684680782668338023559951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26456453855112225349039967 39684680782668338023559951)
    ·
      refine ⟨59527021174002507035339927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39684680782668338023559951 59527021174002507035339927)
      ·
        refine ⟨89290531761003760553009891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59527021174002507035339927 89290531761003760553009891)
        ·
          refine ⟨133935797641505640829514837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89290531761003760553009891 133935797641505640829514837)
          ·
            refine ⟨1569560128611394228470877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 133935797641505640829514837 1569560128611394228470877)
            ·
              refine ⟨588585048229272835676579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1569560128611394228470877 588585048229272835676579)
              ·
                refine ⟨882877572343909253514869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588585048229272835676579 882877572343909253514869)
                ·
                  refine ⟨82769772407241492517019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 882877572343909253514869 82769772407241492517019)
                  ·
                    rfl

theorem cell22_725371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 5].length) (baseStart_725371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725371 prefixEnd_725371 := by exact prefixLift 725371
  have htrace : WordTrace (prefixWord ++ tailWord_725371) baseStart_725371 baseEnd_725371 := by
    simpa [prefixWord, tailWord_725371, baseEnd_725371] using wordTrace_append hprefix tailTrace_725371
  have hstable : (prefixWord ++ tailWord_725371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725371).length < 2 ^ (prefixWord ++ tailWord_725371).sum := by decide
  have hdescent : baseEnd_725371 < baseStart_725371 := by decide
  rcases family_descends (prefixWord ++ tailWord_725371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725568 : List Nat := [2, 1, 1, 2, 2, 2, 5, 3, 4]
def baseStart_725568 : Nat := 118140960795 + 725568 * 2 ^ 59
def prefixEnd_725568 : Nat := 4983230072969 + 3 ^ 40 * 725568 * 2
def baseEnd_725568 : Nat := 82792251449227210125151

theorem tailTrace_725568 : CollatzResearch.WordTrace tailWord_725568 prefixEnd_725568 82792251449227210125151 := by
  unfold tailWord_725568
  simp only [CollatzResearch.WordTrace]
  refine ⟨13231819517699263996980679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17642426023599018662640905 13231819517699263996980679)
  ·
    refine ⟨19847729276548895995471019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13231819517699263996980679 19847729276548895995471019)
    ·
      refine ⟨29771593914823343993206529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19847729276548895995471019 29771593914823343993206529)
      ·
        refine ⟨22328695436117507994904897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29771593914823343993206529 22328695436117507994904897)
        ·
          refine ⟨16746521577088130996178673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22328695436117507994904897 16746521577088130996178673)
          ·
            refine ⟨12559891182816098247134005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16746521577088130996178673 12559891182816098247134005)
            ·
              refine ⟨1177489798389009210668813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12559891182816098247134005 1177489798389009210668813)
              ·
                refine ⟨441558674395878454000805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1177489798389009210668813 441558674395878454000805)
                ·
                  refine ⟨82792251449227210125151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441558674395878454000805 82792251449227210125151)
                  ·
                    rfl

theorem cell22_725568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 4].length) (baseStart_725568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725568 prefixEnd_725568 := by exact prefixLift 725568
  have htrace : WordTrace (prefixWord ++ tailWord_725568) baseStart_725568 baseEnd_725568 := by
    simpa [prefixWord, tailWord_725568, baseEnd_725568] using wordTrace_append hprefix tailTrace_725568
  have hstable : (prefixWord ++ tailWord_725568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725568).length < 2 ^ (prefixWord ++ tailWord_725568).sum := by decide
  have hdescent : baseEnd_725568 < baseStart_725568 := by decide
  rcases family_descends (prefixWord ++ tailWord_725568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725579 : List Nat := [1, 1, 1, 1, 3, 1, 14]
def baseStart_725579 : Nat := 118140960795 + 725579 * 2 ^ 59
def prefixEnd_725579 : Nat := 4983230072969 + 3 ^ 40 * 725579 * 2
def baseEnd_725579 : Nat := 9199278513795602531497

theorem tailTrace_725579 : CollatzResearch.WordTrace tailWord_725579 prefixEnd_725579 9199278513795602531497 := by
  unfold tailWord_725579
  simp only [CollatzResearch.WordTrace]
  refine ⟨26464040238358676872611791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17642693492239117915074527 26464040238358676872611791)
  ·
    refine ⟨39696060357538015308917687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26464040238358676872611791 39696060357538015308917687)
    ·
      refine ⟨59544090536307022963376531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39696060357538015308917687 59544090536307022963376531)
      ·
        refine ⟨89316135804460534445064797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59544090536307022963376531 89316135804460534445064797)
        ·
          refine ⟨33493550926672700416899299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89316135804460534445064797 33493550926672700416899299)
          ·
            refine ⟨50240326390009050625348949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33493550926672700416899299 50240326390009050625348949)
            ·
              refine ⟨9199278513795602531497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 50240326390009050625348949 9199278513795602531497)
              ·
                rfl

theorem cell22_725579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 14].length) (baseStart_725579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725579 prefixEnd_725579 := by exact prefixLift 725579
  have htrace : WordTrace (prefixWord ++ tailWord_725579) baseStart_725579 baseEnd_725579 := by
    simpa [prefixWord, tailWord_725579, baseEnd_725579] using wordTrace_append hprefix tailTrace_725579
  have hstable : (prefixWord ++ tailWord_725579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725579).length < 2 ^ (prefixWord ++ tailWord_725579).sum := by decide
  have hdescent : baseEnd_725579 < baseStart_725579 := by decide
  rcases family_descends (prefixWord ++ tailWord_725579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725585 : List Nat := [1, 2, 2, 1, 3, 4, 3, 2, 4]
def baseStart_725585 : Nat := 118140960795 + 725585 * 2 ^ 59
def prefixEnd_725585 : Nat := 4983230072969 + 3 ^ 40 * 725585 * 2
def baseEnd_725585 : Nat := 82794191265033084233467

theorem tailTrace_725585 : CollatzResearch.WordTrace tailWord_725585 prefixEnd_725585 82794191265033084233467 := by
  unfold tailWord_725585
  simp only [CollatzResearch.WordTrace]
  refine ⟨26464259076336939897330209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17642839384224626598220139 26464259076336939897330209)
  ·
    refine ⟨19848194307252704922997657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26464259076336939897330209 19848194307252704922997657)
    ·
      refine ⟨14886145730439528692248243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19848194307252704922997657 14886145730439528692248243)
      ·
        refine ⟨22329218595659293038372365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14886145730439528692248243 22329218595659293038372365)
        ·
          refine ⟨8373456973372234889389637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22329218595659293038372365 8373456973372234889389637)
          ·
            refine ⟨1570023182507294041760557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8373456973372234889389637 1570023182507294041760557)
            ·
              refine ⟨588758693440235265660209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1570023182507294041760557 588758693440235265660209)
              ·
                refine ⟨441569020080176449245157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588758693440235265660209 441569020080176449245157)
                ·
                  refine ⟨82794191265033084233467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441569020080176449245157 82794191265033084233467)
                  ·
                    rfl

theorem cell22_725585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 4].length) (baseStart_725585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725585 prefixEnd_725585 := by exact prefixLift 725585
  have htrace : WordTrace (prefixWord ++ tailWord_725585) baseStart_725585 baseEnd_725585 := by
    simpa [prefixWord, tailWord_725585, baseEnd_725585] using wordTrace_append hprefix tailTrace_725585
  have hstable : (prefixWord ++ tailWord_725585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725585).length < 2 ^ (prefixWord ++ tailWord_725585).sum := by decide
  have hdescent : baseEnd_725585 < baseStart_725585 := by decide
  rcases family_descends (prefixWord ++ tailWord_725585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725600 : List Nat := [2, 1, 1, 3, 2, 1, 6, 1, 2, 3]
def baseStart_725600 : Nat := 118140960795 + 725600 * 2 ^ 59
def prefixEnd_725600 : Nat := 4983230072969 + 3 ^ 40 * 725600 * 2
def baseEnd_725600 : Nat := 248387708601644213575355

theorem tailTrace_725600 : CollatzResearch.WordTrace tailWord_725600 prefixEnd_725600 248387708601644213575355 := by
  unfold tailWord_725600
  simp only [CollatzResearch.WordTrace]
  refine ⟨13232403085641298729563127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17643204114188398306084169 13232403085641298729563127)
  ·
    refine ⟨19848604628461948094344691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13232403085641298729563127 19848604628461948094344691)
    ·
      refine ⟨29772906942692922141517037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19848604628461948094344691 29772906942692922141517037)
      ·
        refine ⟨11164840103509845803068889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29772906942692922141517037 11164840103509845803068889)
        ·
          refine ⟨8373630077632384352301667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11164840103509845803068889 8373630077632384352301667)
          ·
            refine ⟨12560445116448576528452501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8373630077632384352301667 12560445116448576528452501)
            ·
              refine ⟨588770864833527024771211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12560445116448576528452501 588770864833527024771211)
              ·
                refine ⟨883156297250290537156817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588770864833527024771211 883156297250290537156817)
                ·
                  refine ⟨662367222937717902867613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 883156297250290537156817 662367222937717902867613)
                  ·
                    refine ⟨248387708601644213575355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 662367222937717902867613 248387708601644213575355)
                    ·
                      rfl

theorem cell22_725600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 2, 3].length) (baseStart_725600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725600 prefixEnd_725600 := by exact prefixLift 725600
  have htrace : WordTrace (prefixWord ++ tailWord_725600) baseStart_725600 baseEnd_725600 := by
    simpa [prefixWord, tailWord_725600, baseEnd_725600] using wordTrace_append hprefix tailTrace_725600
  have hstable : (prefixWord ++ tailWord_725600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725600).length < 2 ^ (prefixWord ++ tailWord_725600).sum := by decide
  have hdescent : baseEnd_725600 < baseStart_725600 := by decide
  rcases family_descends (prefixWord ++ tailWord_725600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725709 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 5]
def baseStart_725709 : Nat := 118140960795 + 725709 * 2 ^ 59
def prefixEnd_725709 : Nat := 4983230072969 + 3 ^ 40 * 725709 * 2
def baseEnd_725709 : Nat := 82808340509734754200007

theorem tailTrace_725709 : CollatzResearch.WordTrace tailWord_725709 prefixEnd_725709 82808340509734754200007 := by
  unfold tailWord_725709
  simp only [CollatzResearch.WordTrace]
  refine ⟨26468781727887709074844181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17645854485258472716562787 26468781727887709074844181)
  ·
    refine ⟨1240724143494736362883321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26468781727887709074844181 1240724143494736362883321)
    ·
      refine ⟨930543107621052272162491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1240724143494736362883321 930543107621052272162491)
      ·
        refine ⟨1395814661431578408243737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930543107621052272162491 1395814661431578408243737)
        ·
          refine ⟨1046860996073683806182803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395814661431578408243737 1046860996073683806182803)
          ·
            refine ⟨1570291494110525709274205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046860996073683806182803 1570291494110525709274205)
            ·
              refine ⟨588859310291447140977827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1570291494110525709274205 588859310291447140977827)
              ·
                refine ⟨883288965437170711466741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588859310291447140977827 883288965437170711466741)
                ·
                  refine ⟨82808340509734754200007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 883288965437170711466741 82808340509734754200007)
                  ·
                    rfl

theorem cell22_725709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_725709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725709 prefixEnd_725709 := by exact prefixLift 725709
  have htrace : WordTrace (prefixWord ++ tailWord_725709) baseStart_725709 baseEnd_725709 := by
    simpa [prefixWord, tailWord_725709, baseEnd_725709] using wordTrace_append hprefix tailTrace_725709
  have hstable : (prefixWord ++ tailWord_725709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725709).length < 2 ^ (prefixWord ++ tailWord_725709).sum := by decide
  have hdescent : baseEnd_725709 < baseStart_725709 := by decide
  rcases family_descends (prefixWord ++ tailWord_725709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725733 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_725733 : Nat := 118140960795 + 725733 * 2 ^ 59
def prefixEnd_725733 : Nat := 4983230072969 + 3 ^ 40 * 725733 * 2
def baseEnd_725733 : Nat := 248433237219676199999947

theorem tailTrace_725733 : CollatzResearch.WordTrace tailWord_725733 prefixEnd_725733 248433237219676199999947 := by
  unfold tailWord_725733
  simp only [CollatzResearch.WordTrace]
  refine ⟨26469657079800761173717853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17646438053200507449145235 26469657079800761173717853)
  ·
    refine ⟨9926121404925285440144195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26469657079800761173717853 9926121404925285440144195)
    ·
      refine ⟨14889182107387928160216293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9926121404925285440144195 14889182107387928160216293)
      ·
        refine ⟨2791721645135236530040555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14889182107387928160216293 2791721645135236530040555)
        ·
          refine ⟨4187582467702854795060833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791721645135236530040555 4187582467702854795060833)
          ·
            refine ⟨3140686850777141096295625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4187582467702854795060833 3140686850777141096295625)
            ·
              refine ⟨2355515138082855822221719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3140686850777141096295625 2355515138082855822221719)
              ·
                refine ⟨3533272707124283733332579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355515138082855822221719 3533272707124283733332579)
                ·
                  refine ⟨5299909060686425599998869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533272707124283733332579 5299909060686425599998869)
                  ·
                    refine ⟨248433237219676199999947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5299909060686425599998869 248433237219676199999947)
                    ·
                      rfl

theorem cell22_725733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_725733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725733 prefixEnd_725733 := by exact prefixLift 725733
  have htrace : WordTrace (prefixWord ++ tailWord_725733) baseStart_725733 baseEnd_725733 := by
    simpa [prefixWord, tailWord_725733, baseEnd_725733] using wordTrace_append hprefix tailTrace_725733
  have hstable : (prefixWord ++ tailWord_725733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725733).length < 2 ^ (prefixWord ++ tailWord_725733).sum := by decide
  have hdescent : baseEnd_725733 < baseStart_725733 := by decide
  rcases family_descends (prefixWord ++ tailWord_725733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725750 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_725750 : Nat := 118140960795 + 725750 * 2 ^ 59
def prefixEnd_725750 : Nat := 4983230072969 + 3 ^ 40 * 725750 * 2
def baseEnd_725750 : Nat := 248439056667093822324895

theorem tailTrace_725750 : CollatzResearch.WordTrace tailWord_725750 prefixEnd_725750 248439056667093822324895 := by
  unfold tailWord_725750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654392320046198317317919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17646851413826115384724469 1654392320046198317317919)
  ·
    refine ⟨2481588480069297475976879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1654392320046198317317919 2481588480069297475976879)
    ·
      refine ⟨3722382720103946213965319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2481588480069297475976879 3722382720103946213965319)
      ·
        refine ⟨5583574080155919320947979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722382720103946213965319 5583574080155919320947979)
        ·
          refine ⟨8375361120233878981421969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583574080155919320947979 8375361120233878981421969)
          ·
            refine ⟨6281520840175409236066477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8375361120233878981421969 6281520840175409236066477)
            ·
              refine ⟨2355570315065778463524929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6281520840175409236066477 2355570315065778463524929)
              ·
                refine ⟨1766677736299333847643697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2355570315065778463524929 1766677736299333847643697)
                ·
                  refine ⟨1325008302224500385732773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1766677736299333847643697 1325008302224500385732773)
                  ·
                    refine ⟨248439056667093822324895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325008302224500385732773 248439056667093822324895)
                    ·
                      rfl

theorem cell22_725750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_725750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725750 prefixEnd_725750 := by exact prefixLift 725750
  have htrace : WordTrace (prefixWord ++ tailWord_725750) baseStart_725750 baseEnd_725750 := by
    simpa [prefixWord, tailWord_725750, baseEnd_725750] using wordTrace_append hprefix tailTrace_725750
  have hstable : (prefixWord ++ tailWord_725750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725750).length < 2 ^ (prefixWord ++ tailWord_725750).sum := by decide
  have hdescent : baseEnd_725750 < baseStart_725750 := by decide
  rcases family_descends (prefixWord ++ tailWord_725750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725797 : List Nat := [1, 3, 1, 2, 3, 1, 2, 5, 1, 3]
def baseStart_725797 : Nat := 118140960795 + 725797 * 2 ^ 59
def prefixEnd_725797 : Nat := 4983230072969 + 3 ^ 40 * 725797 * 2
def baseEnd_725797 : Nat := 248455145727601366399751

theorem tailTrace_725797 : CollatzResearch.WordTrace tailWord_725797 prefixEnd_725797 248455145727601366399751 := by
  unfold tailWord_725797
  simp only [CollatzResearch.WordTrace]
  refine ⟨26471991351568900104047645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17647994234379266736031763 26471991351568900104047645)
  ·
    refine ⟨9926996756838337539017867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26471991351568900104047645 9926996756838337539017867)
    ·
      refine ⟨14890495135257506308526801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9926996756838337539017867 14890495135257506308526801)
      ·
        refine ⟨11167871351443129731395101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14890495135257506308526801 11167871351443129731395101)
        ·
          refine ⟨4187951756791173649273163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11167871351443129731395101 4187951756791173649273163)
          ·
            refine ⟨6281927635186760473909745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187951756791173649273163 6281927635186760473909745)
            ·
              refine ⟨4711445726390070355432309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6281927635186760473909745 4711445726390070355432309)
              ·
                refine ⟨441698036849069095821779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4711445726390070355432309 441698036849069095821779)
                ·
                  refine ⟨662547055273603643732669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441698036849069095821779 662547055273603643732669)
                  ·
                    refine ⟨248455145727601366399751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 662547055273603643732669 248455145727601366399751)
                    ·
                      rfl

theorem cell22_725797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_725797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725797 prefixEnd_725797 := by exact prefixLift 725797
  have htrace : WordTrace (prefixWord ++ tailWord_725797) baseStart_725797 baseEnd_725797 := by
    simpa [prefixWord, tailWord_725797, baseEnd_725797] using wordTrace_append hprefix tailTrace_725797
  have hstable : (prefixWord ++ tailWord_725797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725797).length < 2 ^ (prefixWord ++ tailWord_725797).sum := by decide
  have hdescent : baseEnd_725797 < baseStart_725797 := by decide
  rcases family_descends (prefixWord ++ tailWord_725797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725810 : List Nat := [3, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_725810 : Nat := 118140960795 + 725810 * 2 ^ 59
def prefixEnd_725810 : Nat := 4983230072969 + 3 ^ 40 * 725810 * 2
def baseEnd_725810 : Nat := 82819865297757888608237

theorem tailTrace_725810 : CollatzResearch.WordTrace tailWord_725810 prefixEnd_725810 82819865297757888608237 := by
  unfold tailWord_725810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6618116375130450831067721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17648310333681202216180589 6618116375130450831067721)
  ·
    refine ⟨4963587281347838123300791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6618116375130450831067721 4963587281347838123300791)
    ·
      refine ⟨7445380922021757184951187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4963587281347838123300791 7445380922021757184951187)
      ·
        refine ⟨11168071383032635777426781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7445380922021757184951187 11168071383032635777426781)
        ·
          refine ⟨4188026768637238416535043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11168071383032635777426781 4188026768637238416535043)
          ·
            refine ⟨6282040152955857624802565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4188026768637238416535043 6282040152955857624802565)
            ·
              refine ⟨1177882528679223304650481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6282040152955857624802565 1177882528679223304650481)
              ·
                refine ⟨883411896509417478487861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177882528679223304650481 883411896509417478487861)
                ·
                  refine ⟨82819865297757888608237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 883411896509417478487861 82819865297757888608237)
                  ·
                    rfl

theorem cell22_725810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_725810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725810 prefixEnd_725810 := by exact prefixLift 725810
  have htrace : WordTrace (prefixWord ++ tailWord_725810) baseStart_725810 baseEnd_725810 := by
    simpa [prefixWord, tailWord_725810, baseEnd_725810] using wordTrace_append hprefix tailTrace_725810
  have hstable : (prefixWord ++ tailWord_725810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725810).length < 2 ^ (prefixWord ++ tailWord_725810).sum := by decide
  have hdescent : baseEnd_725810 < baseStart_725810 := by decide
  rcases family_descends (prefixWord ++ tailWord_725810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725900 : List Nat := [2, 2, 1, 2, 1, 2, 6, 6]
def baseStart_725900 : Nat := 118140960795 + 725900 * 2 ^ 59
def prefixEnd_725900 : Nat := 4983230072969 + 3 ^ 40 * 725900 * 2
def baseEnd_725900 : Nat := 27610044970282603452715

theorem tailTrace_725900 : CollatzResearch.WordTrace tailWord_725900 prefixEnd_725900 27610044970282603452715 := by
  unfold tailWord_725900
  simp only [CollatzResearch.WordTrace]
  refine ⟨13237874035097874347523577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17650498713463832463364769 13237874035097874347523577)
  ·
    refine ⟨9928405526323405760642683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13237874035097874347523577 9928405526323405760642683)
    ·
      refine ⟨14892608289485108640964025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9928405526323405760642683 14892608289485108640964025)
      ·
        refine ⟨11169456217113831480723019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14892608289485108640964025 11169456217113831480723019)
        ·
          refine ⟨16754184325670747221084529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169456217113831480723019 16754184325670747221084529)
          ·
            refine ⟨12565638244253060415813397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16754184325670747221084529 12565638244253060415813397)
            ·
              refine ⟨589014292699362206991253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12565638244253060415813397 589014292699362206991253)
              ·
                refine ⟨27610044970282603452715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 589014292699362206991253 27610044970282603452715)
                ·
                  rfl

theorem cell22_725900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 6].length) (baseStart_725900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725900 prefixEnd_725900 := by exact prefixLift 725900
  have htrace : WordTrace (prefixWord ++ tailWord_725900) baseStart_725900 baseEnd_725900 := by
    simpa [prefixWord, tailWord_725900, baseEnd_725900] using wordTrace_append hprefix tailTrace_725900
  have hstable : (prefixWord ++ tailWord_725900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725900).length < 2 ^ (prefixWord ++ tailWord_725900).sum := by decide
  have hdescent : baseEnd_725900 < baseStart_725900 := by decide
  rcases family_descends (prefixWord ++ tailWord_725900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725906 : List Nat := [3, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_725906 : Nat := 118140960795 + 725906 * 2 ^ 59
def prefixEnd_725906 : Nat := 4983230072969 + 3 ^ 40 * 725906 * 2
def baseEnd_725906 : Nat := 82830819551720471808139

theorem tailTrace_725906 : CollatzResearch.WordTrace tailWord_725906 prefixEnd_725906 82830819551720471808139 := by
  unfold tailWord_725906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6618991727043502929941393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17650644605449341146510381 6618991727043502929941393)
  ·
    refine ⟨4964243795282627197456045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6618991727043502929941393 4964243795282627197456045)
    ·
      refine ⟨1861591423230985199046017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4964243795282627197456045 1861591423230985199046017)
      ·
        refine ⟨1396193567423238899284513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1861591423230985199046017 1396193567423238899284513)
        ·
          refine ⟨1047145175567429174463385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1396193567423238899284513 1047145175567429174463385)
          ·
            refine ⟨785358881675571880847539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047145175567429174463385 785358881675571880847539)
            ·
              refine ⟨1178038322513357821271309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785358881675571880847539 1178038322513357821271309)
              ·
                refine ⟨441764370942509182976741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1178038322513357821271309 441764370942509182976741)
                ·
                  refine ⟨82830819551720471808139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441764370942509182976741 82830819551720471808139)
                  ·
                    rfl

theorem cell22_725906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_725906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725906 prefixEnd_725906 := by exact prefixLift 725906
  have htrace : WordTrace (prefixWord ++ tailWord_725906) baseStart_725906 baseEnd_725906 := by
    simpa [prefixWord, tailWord_725906, baseEnd_725906] using wordTrace_append hprefix tailTrace_725906
  have hstable : (prefixWord ++ tailWord_725906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725906).length < 2 ^ (prefixWord ++ tailWord_725906).sum := by decide
  have hdescent : baseEnd_725906 < baseStart_725906 := by decide
  rcases family_descends (prefixWord ++ tailWord_725906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725913 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_725913 : Nat := 118140960795 + 725913 * 2 ^ 59
def prefixEnd_725913 : Nat := 4983230072969 + 3 ^ 40 * 725913 * 2
def baseEnd_725913 : Nat := 248494854898215730499395

theorem tailTrace_725913 : CollatzResearch.WordTrace tailWord_725913 prefixEnd_725913 248494854898215730499395 := by
  unfold tailWord_725913
  simp only [CollatzResearch.WordTrace]
  refine ⟨26476222219148651915270393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17650814812765767943513595 26476222219148651915270393)
  ·
    refine ⟨19857166664361488936452795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26476222219148651915270393 19857166664361488936452795)
    ·
      refine ⟨29785749996542233404679193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19857166664361488936452795 29785749996542233404679193)
      ·
        refine ⟨22339312497406675053509395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29785749996542233404679193 22339312497406675053509395)
        ·
          refine ⟨33508968746110012580264093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22339312497406675053509395 33508968746110012580264093)
          ·
            refine ⟨12565863279791254717599035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33508968746110012580264093 12565863279791254717599035)
            ·
              refine ⟨18848794919686882076398553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12565863279791254717599035 18848794919686882076398553)
              ·
                refine ⟨14136596189765161557298915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18848794919686882076398553 14136596189765161557298915)
                ·
                  refine ⟨21204894284647742335948373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14136596189765161557298915 21204894284647742335948373)
                  ·
                    refine ⟨248494854898215730499395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21204894284647742335948373 248494854898215730499395)
                    ·
                      rfl

theorem cell22_725913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_725913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725913 prefixEnd_725913 := by exact prefixLift 725913
  have htrace : WordTrace (prefixWord ++ tailWord_725913) baseStart_725913 baseEnd_725913 := by
    simpa [prefixWord, tailWord_725913, baseEnd_725913] using wordTrace_append hprefix tailTrace_725913
  have hstable : (prefixWord ++ tailWord_725913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725913).length < 2 ^ (prefixWord ++ tailWord_725913).sum := by decide
  have hdescent : baseEnd_725913 < baseStart_725913 := by decide
  rcases family_descends (prefixWord ++ tailWord_725913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725983 : List Nat := [1, 1, 2, 3, 5, 2, 2, 2, 1, 3]
def baseStart_725983 : Nat := 118140960795 + 725983 * 2 ^ 59
def prefixEnd_725983 : Nat := 4983230072969 + 3 ^ 40 * 725983 * 2
def baseEnd_725983 : Nat := 248518817328758881249181

theorem tailTrace_725983 : CollatzResearch.WordTrace tailWord_725983 prefixEnd_725983 248518817328758881249181 := by
  unfold tailWord_725983
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478775328895053870318603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17652516885930035913545735 26478775328895053870318603)
  ·
    refine ⟨39718162993342580805477905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26478775328895053870318603 39718162993342580805477905)
    ·
      refine ⟨29788622245006935604108429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39718162993342580805477905 29788622245006935604108429)
      ·
        refine ⟨11170733341877600851540661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29788622245006935604108429 11170733341877600851540661)
        ·
          refine ⟨1047256250801025079831937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11170733341877600851540661 1047256250801025079831937)
          ·
            refine ⟨785442188100768809873953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047256250801025079831937 785442188100768809873953)
            ·
              refine ⟨589081641075576607405465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785442188100768809873953 589081641075576607405465)
              ·
                refine ⟨441811230806682455554099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589081641075576607405465 441811230806682455554099)
                ·
                  refine ⟨662716846210023683331149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441811230806682455554099 662716846210023683331149)
                  ·
                    refine ⟨248518817328758881249181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 662716846210023683331149 248518817328758881249181)
                    ·
                      rfl

theorem cell22_725983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 3].length) (baseStart_725983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_725983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_725983 prefixEnd_725983 := by exact prefixLift 725983
  have htrace : WordTrace (prefixWord ++ tailWord_725983) baseStart_725983 baseEnd_725983 := by
    simpa [prefixWord, tailWord_725983, baseEnd_725983] using wordTrace_append hprefix tailTrace_725983
  have hstable : (prefixWord ++ tailWord_725983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725983).length < 2 ^ (prefixWord ++ tailWord_725983).sum := by decide
  have hdescent : baseEnd_725983 < baseStart_725983 := by decide
  rcases family_descends (prefixWord ++ tailWord_725983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726024 : List Nat := [2, 1, 3, 2, 1, 4, 2, 3, 4]
def baseStart_726024 : Nat := 118140960795 + 726024 * 2 ^ 59
def prefixEnd_726024 : Nat := 4983230072969 + 3 ^ 40 * 726024 * 2
def baseEnd_726024 : Nat := 82844284155549480324685

theorem tailTrace_726024 : CollatzResearch.WordTrace tailWord_726024 prefixEnd_726024 82844284155549480324685 := by
  unfold tailWord_726024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13240135360873258936280563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17653513814497678581707417 13240135360873258936280563)
  ·
    refine ⟨19860203041309888404420845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13240135360873258936280563 19860203041309888404420845)
    ·
      refine ⟨7447576140491208151657817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19860203041309888404420845 7447576140491208151657817)
      ·
        refine ⟨5585682105368406113743363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7447576140491208151657817 5585682105368406113743363)
        ·
          refine ⟨8378523158052609170615045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5585682105368406113743363 8378523158052609170615045)
          ·
            refine ⟨1570973092134864219490321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8378523158052609170615045 1570973092134864219490321)
            ·
              refine ⟨1178229819101148164617741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1570973092134864219490321 1178229819101148164617741)
              ·
                refine ⟨441836182162930561731653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1178229819101148164617741 441836182162930561731653)
                ·
                  refine ⟨82844284155549480324685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441836182162930561731653 82844284155549480324685)
                  ·
                    rfl

theorem cell22_726024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 4].length) (baseStart_726024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726024 prefixEnd_726024 := by exact prefixLift 726024
  have htrace : WordTrace (prefixWord ++ tailWord_726024) baseStart_726024 baseEnd_726024 := by
    simpa [prefixWord, tailWord_726024, baseEnd_726024] using wordTrace_append hprefix tailTrace_726024
  have hstable : (prefixWord ++ tailWord_726024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726024).length < 2 ^ (prefixWord ++ tailWord_726024).sum := by decide
  have hdescent : baseEnd_726024 < baseStart_726024 := by decide
  rcases family_descends (prefixWord ++ tailWord_726024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726026 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 1, 4]
def baseStart_726026 : Nat := 118140960795 + 726026 * 2 ^ 59
def prefixEnd_726026 : Nat := 4983230072969 + 3 ^ 40 * 726026 * 2
def baseEnd_726026 : Nat := 248533537107521102424049

theorem tailTrace_726026 : CollatzResearch.WordTrace tailWord_726026 prefixEnd_726026 248533537107521102424049 := by
  unfold tailWord_726026
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620085916934818053533483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17653562445159514809422621 6620085916934818053533483)
  ·
    refine ⟨9930128875402227080300225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6620085916934818053533483 9930128875402227080300225)
    ·
      refine ⟨7447596656551670310225169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9930128875402227080300225 7447596656551670310225169)
      ·
        refine ⟨5585697492413752732668877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7447596656551670310225169 5585697492413752732668877)
        ·
          refine ⟨2094636559655157274750829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5585697492413752732668877 2094636559655157274750829)
          ·
            refine ⟨785488709870683978031561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2094636559655157274750829 785488709870683978031561)
            ·
              refine ⟨589116532403012983523671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785488709870683978031561 589116532403012983523671)
              ·
                refine ⟨883674798604519475285507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589116532403012983523671 883674798604519475285507)
                ·
                  refine ⟨1325512197906779212928261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883674798604519475285507 1325512197906779212928261)
                  ·
                    refine ⟨248533537107521102424049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325512197906779212928261 248533537107521102424049)
                    ·
                      rfl

theorem cell22_726026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_726026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726026 prefixEnd_726026 := by exact prefixLift 726026
  have htrace : WordTrace (prefixWord ++ tailWord_726026) baseStart_726026 baseEnd_726026 := by
    simpa [prefixWord, tailWord_726026, baseEnd_726026] using wordTrace_append hprefix tailTrace_726026
  have hstable : (prefixWord ++ tailWord_726026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726026).length < 2 ^ (prefixWord ++ tailWord_726026).sum := by decide
  have hdescent : baseEnd_726026 < baseStart_726026 := by decide
  rcases family_descends (prefixWord ++ tailWord_726026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726039 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 4, 3]
def baseStart_726039 : Nat := 118140960795 + 726039 * 2 ^ 59
def prefixEnd_726039 : Nat := 4983230072969 + 3 ^ 40 * 726039 * 2
def baseEnd_726039 : Nat := 248537987273193401849009

theorem tailTrace_726039 : CollatzResearch.WordTrace tailWord_726039 prefixEnd_726039 248537987273193401849009 := by
  unfold tailWord_726039
  simp only [CollatzResearch.WordTrace]
  refine ⟨26480817816692175434357171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17653878544461450289571447 26480817816692175434357171)
  ·
    refine ⟨39721226725038263151535757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26480817816692175434357171 39721226725038263151535757)
    ·
      refine ⟨14895460021889348681825909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39721226725038263151535757 14895460021889348681825909)
      ·
        refine ⟨1396449377052126438921179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14895460021889348681825909 1396449377052126438921179)
        ·
          refine ⟨2094674065578189658381769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396449377052126438921179 2094674065578189658381769)
          ·
            refine ⟨1571005549183642243786327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094674065578189658381769 1571005549183642243786327)
            ·
              refine ⟨2356508323775463365679491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571005549183642243786327 2356508323775463365679491)
              ·
                refine ⟨3534762485663195048519237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356508323775463365679491 3534762485663195048519237)
                ·
                  refine ⟨662767966061849071597357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3534762485663195048519237 662767966061849071597357)
                  ·
                    refine ⟨248537987273193401849009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 662767966061849071597357 248537987273193401849009)
                    ·
                      rfl

theorem cell22_726039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_726039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726039 prefixEnd_726039 := by exact prefixLift 726039
  have htrace : WordTrace (prefixWord ++ tailWord_726039) baseStart_726039 baseEnd_726039 := by
    simpa [prefixWord, tailWord_726039, baseEnd_726039] using wordTrace_append hprefix tailTrace_726039
  have hstable : (prefixWord ++ tailWord_726039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726039).length < 2 ^ (prefixWord ++ tailWord_726039).sum := by decide
  have hdescent : baseEnd_726039 < baseStart_726039 := by decide
  rcases family_descends (prefixWord ++ tailWord_726039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726080 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 9]
def baseStart_726080 : Nat := 118140960795 + 726080 * 2 ^ 59
def prefixEnd_726080 : Nat := 4983230072969 + 3 ^ 40 * 726080 * 2
def baseEnd_726080 : Nat := 82850674137027653857961

theorem tailTrace_726080 : CollatzResearch.WordTrace tailWord_726080 prefixEnd_726080 82850674137027653857961 := by
  unfold tailWord_726080
  simp only [CollatzResearch.WordTrace]
  refine ⟨13241156604771819718299847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17654875473029092957733129 13241156604771819718299847)
  ·
    refine ⟨19861734907157729577449771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13241156604771819718299847 19861734907157729577449771)
    ·
      refine ⟨29792602360736594366174657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19861734907157729577449771 29792602360736594366174657)
      ·
        refine ⟨22344451770552445774630993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29792602360736594366174657 22344451770552445774630993)
        ·
          refine ⟨16758338827914334330973245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22344451770552445774630993 16758338827914334330973245)
          ·
            refine ⟨6284377060467875374114967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16758338827914334330973245 6284377060467875374114967)
            ·
              refine ⟨9426565590701813061172451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284377060467875374114967 9426565590701813061172451)
              ·
                refine ⟨14139848386052719591758677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9426565590701813061172451 14139848386052719591758677)
                ·
                  refine ⟨82850674137027653857961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14139848386052719591758677 82850674137027653857961)
                  ·
                    rfl

theorem cell22_726080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_726080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726080 prefixEnd_726080 := by exact prefixLift 726080
  have htrace : WordTrace (prefixWord ++ tailWord_726080) baseStart_726080 baseEnd_726080 := by
    simpa [prefixWord, tailWord_726080, baseEnd_726080] using wordTrace_append hprefix tailTrace_726080
  have hstable : (prefixWord ++ tailWord_726080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726080).length < 2 ^ (prefixWord ++ tailWord_726080).sum := by decide
  have hdescent : baseEnd_726080 < baseStart_726080 := by decide
  rcases family_descends (prefixWord ++ tailWord_726080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726127 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 3, 4]
def baseStart_726127 : Nat := 118140960795 + 726127 * 2 ^ 59
def prefixEnd_726127 : Nat := 4983230072969 + 3 ^ 40 * 726127 * 2
def baseEnd_726127 : Nat := 248568111471590505648739

theorem tailTrace_726127 : CollatzResearch.WordTrace tailWord_726127 prefixEnd_726127 248568111471590505648739 := by
  unfold tailWord_726127
  simp only [CollatzResearch.WordTrace]
  refine ⟨26484027440373366463560635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17656018293582244309040423 26484027440373366463560635)
  ·
    refine ⟨39726041160560049695340953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26484027440373366463560635 39726041160560049695340953)
    ·
      refine ⟨29794530870420037271505715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39726041160560049695340953 29794530870420037271505715)
      ·
        refine ⟨44691796305630055907258573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29794530870420037271505715 44691796305630055907258573)
        ·
          refine ⟨16759423614611270965221965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44691796305630055907258573 16759423614611270965221965)
          ·
            refine ⟨6284783855479226611958237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16759423614611270965221965 6284783855479226611958237)
            ·
              refine ⟨2356793945804709979484339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6284783855479226611958237 2356793945804709979484339)
              ·
                refine ⟨3535190918707064969226509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356793945804709979484339 3535190918707064969226509)
                ·
                  refine ⟨1325696594515149363459941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3535190918707064969226509 1325696594515149363459941)
                  ·
                    refine ⟨248568111471590505648739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1325696594515149363459941 248568111471590505648739)
                    ·
                      rfl

theorem cell22_726127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_726127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726127 prefixEnd_726127 := by exact prefixLift 726127
  have htrace : WordTrace (prefixWord ++ tailWord_726127) baseStart_726127 baseEnd_726127 := by
    simpa [prefixWord, tailWord_726127, baseEnd_726127] using wordTrace_append hprefix tailTrace_726127
  have hstable : (prefixWord ++ tailWord_726127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726127).length < 2 ^ (prefixWord ++ tailWord_726127).sum := by decide
  have hdescent : baseEnd_726127 < baseStart_726127 := by decide
  rcases family_descends (prefixWord ++ tailWord_726127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726152 : List Nat := [2, 1, 3, 4, 3, 1, 2, 2, 1, 3]
def baseStart_726152 : Nat := 118140960795 + 726152 * 2 ^ 59
def prefixEnd_726152 : Nat := 4983230072969 + 3 ^ 40 * 726152 * 2
def baseEnd_726152 : Nat := 248576669482498773773663

theorem tailTrace_726152 : CollatzResearch.WordTrace tailWord_726152 prefixEnd_726152 248576669482498773773663 := by
  unfold tailWord_726152
  simp only [CollatzResearch.WordTrace]
  refine ⟨13242469632641397866610355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17656626176855197155480473 13242469632641397866610355)
  ·
    refine ⟨19863704448962096799915533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13242469632641397866610355 19863704448962096799915533)
    ·
      refine ⟨7448889168360786299968325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19863704448962096799915533 7448889168360786299968325)
      ·
        refine ⟨1396666719067647431244061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7448889168360786299968325 1396666719067647431244061)
        ·
          refine ⟨523750019650367786716523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1396666719067647431244061 523750019650367786716523)
          ·
            refine ⟨785625029475551680074785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523750019650367786716523 785625029475551680074785)
            ·
              refine ⟨589218772106663760056089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785625029475551680074785 589218772106663760056089)
              ·
                refine ⟨441914079079997820042067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589218772106663760056089 441914079079997820042067)
                ·
                  refine ⟨662871118619996730063101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441914079079997820042067 662871118619996730063101)
                  ·
                    refine ⟨248576669482498773773663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 662871118619996730063101 248576669482498773773663)
                    ·
                      rfl

theorem cell22_726152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_726152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726152 prefixEnd_726152 := by exact prefixLift 726152
  have htrace : WordTrace (prefixWord ++ tailWord_726152) baseStart_726152 baseEnd_726152 := by
    simpa [prefixWord, tailWord_726152, baseEnd_726152] using wordTrace_append hprefix tailTrace_726152
  have hstable : (prefixWord ++ tailWord_726152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726152).length < 2 ^ (prefixWord ++ tailWord_726152).sum := by decide
  have hdescent : baseEnd_726152 < baseStart_726152 := by decide
  rcases family_descends (prefixWord ++ tailWord_726152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726208 : List Nat := [2, 1, 1, 2, 6, 2, 1, 2, 2, 3]
def baseStart_726208 : Nat := 118140960795 + 726208 * 2 ^ 59
def prefixEnd_726208 : Nat := 4983230072969 + 3 ^ 40 * 726208 * 2
def baseEnd_726208 : Nat := 248595839426933294373491

theorem tailTrace_726208 : CollatzResearch.WordTrace tailWord_726208 prefixEnd_726208 248595839426933294373491 := by
  unfold tailWord_726208
  simp only [CollatzResearch.WordTrace]
  refine ⟨13243490876539958648629639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17657987835386611531506185 13243490876539958648629639)
  ·
    refine ⟨19865236314809937972944459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13243490876539958648629639 19865236314809937972944459)
    ·
      refine ⟨29797854472214906959416689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19865236314809937972944459 29797854472214906959416689)
      ·
        refine ⟨22348390854161180219562517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29797854472214906959416689 22348390854161180219562517)
        ·
          refine ⟨1047580821288805322791993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22348390854161180219562517 1047580821288805322791993)
          ·
            refine ⟨785685615966603992093995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047580821288805322791993 785685615966603992093995)
            ·
              refine ⟨1178528423949905988140993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785685615966603992093995 1178528423949905988140993)
              ·
                refine ⟨883896317962429491105745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178528423949905988140993 883896317962429491105745)
                ·
                  refine ⟨662922238471822118329309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 883896317962429491105745 662922238471822118329309)
                  ·
                    refine ⟨248595839426933294373491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 662922238471822118329309 248595839426933294373491)
                    ·
                      rfl

theorem cell22_726208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_726208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726208 prefixEnd_726208 := by exact prefixLift 726208
  have htrace : WordTrace (prefixWord ++ tailWord_726208) baseStart_726208 baseEnd_726208 := by
    simpa [prefixWord, tailWord_726208, baseEnd_726208] using wordTrace_append hprefix tailTrace_726208
  have hstable : (prefixWord ++ tailWord_726208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726208).length < 2 ^ (prefixWord ++ tailWord_726208).sum := by decide
  have hdescent : baseEnd_726208 < baseStart_726208 := by decide
  rcases family_descends (prefixWord ++ tailWord_726208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726296 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_726296 : Nat := 118140960795 + 726296 * 2 ^ 59
def prefixEnd_726296 : Nat := 4983230072969 + 3 ^ 40 * 726296 * 2
def baseEnd_726296 : Nat := 248625963625330398173221

theorem tailTrace_726296 : CollatzResearch.WordTrace tailWord_726296 prefixEnd_726296 248625963625330398173221 := by
  unfold tailWord_726296
  simp only [CollatzResearch.WordTrace]
  refine ⟨13245095688380554163231371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17660127584507405550975161 13245095688380554163231371)
  ·
    refine ⟨19867643532570831244847057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13245095688380554163231371 19867643532570831244847057)
    ·
      refine ⟨14900732649428123433635293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19867643532570831244847057 14900732649428123433635293)
      ·
        refine ⟨5587774743535546287613235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14900732649428123433635293 5587774743535546287613235)
        ·
          refine ⟨8381662115303319431419853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5587774743535546287613235 8381662115303319431419853)
          ·
            refine ⟨3143123293238744786782445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8381662115303319431419853 3143123293238744786782445)
            ·
              refine ⟨1178671234964529295043417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3143123293238744786782445 1178671234964529295043417)
              ·
                refine ⟨884003426223396971282563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178671234964529295043417 884003426223396971282563)
                ·
                  refine ⟨1326005139335095456923845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884003426223396971282563 1326005139335095456923845)
                  ·
                    refine ⟨248625963625330398173221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326005139335095456923845 248625963625330398173221)
                    ·
                      rfl

theorem cell22_726296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_726296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726296 prefixEnd_726296 := by exact prefixLift 726296
  have htrace : WordTrace (prefixWord ++ tailWord_726296) baseStart_726296 baseEnd_726296 := by
    simpa [prefixWord, tailWord_726296, baseEnd_726296] using wordTrace_append hprefix tailTrace_726296
  have hstable : (prefixWord ++ tailWord_726296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726296).length < 2 ^ (prefixWord ++ tailWord_726296).sum := by decide
  have hdescent : baseEnd_726296 < baseStart_726296 := by decide
  rcases family_descends (prefixWord ++ tailWord_726296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726309 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_726309 : Nat := 118140960795 + 726309 * 2 ^ 59
def prefixEnd_726309 : Nat := 4983230072969 + 3 ^ 40 * 726309 * 2
def baseEnd_726309 : Nat := 248630413791002697598181

theorem tailTrace_726309 : CollatzResearch.WordTrace tailWord_726309 prefixEnd_726309 248630413791002697598181 := by
  unfold tailWord_726309
  simp only [CollatzResearch.WordTrace]
  refine ⟨26490665525714011546685981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17660443683809341031123987 26490665525714011546685981)
  ·
    refine ⟨9933999572142754330007243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26490665525714011546685981 9933999572142754330007243)
    ·
      refine ⟨14900999358214131495010865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9933999572142754330007243 14900999358214131495010865)
      ·
        refine ⟨11175749518660598621258149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14900999358214131495010865 11175749518660598621258149)
        ·
          refine ⟨2095453034748862241485903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11175749518660598621258149 2095453034748862241485903)
          ·
            refine ⟨3143179552123293362228855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095453034748862241485903 3143179552123293362228855)
            ·
              refine ⟨4714769328184940043343283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143179552123293362228855 4714769328184940043343283)
              ·
                refine ⟨7072153992277410065014925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4714769328184940043343283 7072153992277410065014925)
                ·
                  refine ⟨2652057747104028774380597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7072153992277410065014925 2652057747104028774380597)
                  ·
                    refine ⟨248630413791002697598181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2652057747104028774380597 248630413791002697598181)
                    ·
                      rfl

theorem cell22_726309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_726309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726309 prefixEnd_726309 := by exact prefixLift 726309
  have htrace : WordTrace (prefixWord ++ tailWord_726309) baseStart_726309 baseEnd_726309 := by
    simpa [prefixWord, tailWord_726309, baseEnd_726309] using wordTrace_append hprefix tailTrace_726309
  have hstable : (prefixWord ++ tailWord_726309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726309).length < 2 ^ (prefixWord ++ tailWord_726309).sum := by decide
  have hdescent : baseEnd_726309 < baseStart_726309 := by decide
  rcases family_descends (prefixWord ++ tailWord_726309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726356 : List Nat := [2, 4, 1, 1, 2, 1, 5, 6]
def baseStart_726356 : Nat := 118140960795 + 726356 * 2 ^ 59
def prefixEnd_726356 : Nat := 4983230072969 + 3 ^ 40 * 726356 * 2
def baseEnd_726356 : Nat := 27627389205723360185893

theorem tailTrace_726356 : CollatzResearch.WordTrace tailWord_726356 prefixEnd_726356 27627389205723360185893 := by
  unfold tailWord_726356
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246189878271869286823461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17661586504362492382431281 13246189878271869286823461)
  ·
    refine ⟨2483660602175975491279399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13246189878271869286823461 2483660602175975491279399)
    ·
      refine ⟨3725490903263963236919099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483660602175975491279399 3725490903263963236919099)
      ·
        refine ⟨5588236354895944855378649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725490903263963236919099 5588236354895944855378649)
        ·
          refine ⟨4191177266171958641533987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5588236354895944855378649 4191177266171958641533987)
          ·
            refine ⟨6286765899257937962300981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191177266171958641533987 6286765899257937962300981)
            ·
              refine ⟨589384303055431683965717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6286765899257937962300981 589384303055431683965717)
              ·
                refine ⟨27627389205723360185893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 589384303055431683965717 27627389205723360185893)
                ·
                  rfl

theorem cell22_726356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 6].length) (baseStart_726356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726356 prefixEnd_726356 := by exact prefixLift 726356
  have htrace : WordTrace (prefixWord ++ tailWord_726356) baseStart_726356 baseEnd_726356 := by
    simpa [prefixWord, tailWord_726356, baseEnd_726356] using wordTrace_append hprefix tailTrace_726356
  have hstable : (prefixWord ++ tailWord_726356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726356).length < 2 ^ (prefixWord ++ tailWord_726356).sum := by decide
  have hdescent : baseEnd_726356 < baseStart_726356 := by decide
  rcases family_descends (prefixWord ++ tailWord_726356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726384 : List Nat := [2, 1, 1, 1, 4, 2, 3, 1, 7]
def baseStart_726384 : Nat := 118140960795 + 726384 * 2 ^ 59
def prefixEnd_726384 : Nat := 4983230072969 + 3 ^ 40 * 726384 * 2
def baseEnd_726384 : Nat := 82885362607909167324317

theorem tailTrace_726384 : CollatzResearch.WordTrace tailWord_726384 prefixEnd_726384 82885362607909167324317 := by
  unfold tailWord_726384
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246700500221149677833103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17662267333628199570444137 13246700500221149677833103)
  ·
    refine ⟨19870050750331724516749655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13246700500221149677833103 19870050750331724516749655)
    ·
      refine ⟨29805076125497586775124483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19870050750331724516749655 29805076125497586775124483)
      ·
        refine ⟨44707614188246380162686725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29805076125497586775124483 44707614188246380162686725)
        ·
          refine ⟨8382677660296196280503761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44707614188246380162686725 8382677660296196280503761)
          ·
            refine ⟨6287008245222147210377821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8382677660296196280503761 6287008245222147210377821)
            ·
              refine ⟨2357628091958305203891683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6287008245222147210377821 2357628091958305203891683)
              ·
                refine ⟨3536442137937457805837525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357628091958305203891683 3536442137937457805837525)
                ·
                  refine ⟨82885362607909167324317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3536442137937457805837525 82885362607909167324317)
                  ·
                    rfl

theorem cell22_726384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_726384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726384 prefixEnd_726384 := by exact prefixLift 726384
  have htrace : WordTrace (prefixWord ++ tailWord_726384) baseStart_726384 baseEnd_726384 := by
    simpa [prefixWord, tailWord_726384, baseEnd_726384] using wordTrace_append hprefix tailTrace_726384
  have hstable : (prefixWord ++ tailWord_726384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726384).length < 2 ^ (prefixWord ++ tailWord_726384).sum := by decide
  have hdescent : baseEnd_726384 < baseStart_726384 := by decide
  rcases family_descends (prefixWord ++ tailWord_726384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726461 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_726461 : Nat := 118140960795 + 726461 * 2 ^ 59
def prefixEnd_726461 : Nat := 4983230072969 + 3 ^ 40 * 726461 * 2
def baseEnd_726461 : Nat := 248682446497324967797715

theorem tailTrace_726461 : CollatzResearch.WordTrace tailWord_726461 prefixEnd_726461 248682446497324967797715 := by
  unfold tailWord_726461
  simp only [CollatzResearch.WordTrace]
  refine ⟨26496209421163341506219237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17664139614108894337479491 26496209421163341506219237)
  ·
    refine ⟨4968039266468126532416107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26496209421163341506219237 4968039266468126532416107)
    ·
      refine ⟨7452058899702189798624161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4968039266468126532416107 7452058899702189798624161)
      ·
        refine ⟨5589044174776642348968121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7452058899702189798624161 5589044174776642348968121)
        ·
          refine ⟨4191783131082481761726091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5589044174776642348968121 4191783131082481761726091)
          ·
            refine ⟨6287674696623722642589137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191783131082481761726091 6287674696623722642589137)
            ·
              refine ⟨4715756022467791981941853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6287674696623722642589137 4715756022467791981941853)
              ·
                refine ⟨1768408508425421993228195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4715756022467791981941853 1768408508425421993228195)
                ·
                  refine ⟨2652612762638132989842293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1768408508425421993228195 2652612762638132989842293)
                  ·
                    refine ⟨248682446497324967797715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2652612762638132989842293 248682446497324967797715)
                    ·
                      rfl

theorem cell22_726461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_726461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726461 prefixEnd_726461 := by exact prefixLift 726461
  have htrace : WordTrace (prefixWord ++ tailWord_726461) baseStart_726461 baseEnd_726461 := by
    simpa [prefixWord, tailWord_726461, baseEnd_726461] using wordTrace_append hprefix tailTrace_726461
  have hstable : (prefixWord ++ tailWord_726461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726461).length < 2 ^ (prefixWord ++ tailWord_726461).sum := by decide
  have hdescent : baseEnd_726461 < baseStart_726461 := by decide
  rcases family_descends (prefixWord ++ tailWord_726461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726493 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_726493 : Nat := 118140960795 + 726493 * 2 ^ 59
def prefixEnd_726493 : Nat := 4983230072969 + 3 ^ 40 * 726493 * 2
def baseEnd_726493 : Nat := 248693400751287550997617

theorem tailTrace_726493 : CollatzResearch.WordTrace tailWord_726493 prefixEnd_726493 248693400751287550997617 := by
  unfold tailWord_726493
  simp only [CollatzResearch.WordTrace]
  refine ⟨26497376557047410971384133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17664917704698273980922755 26497376557047410971384133)
  ·
    refine ⟨4968258104446389557134525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26497376557047410971384133 4968258104446389557134525)
    ·
      refine ⟨1863096789167396083925447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4968258104446389557134525 1863096789167396083925447)
      ·
        refine ⟨2794645183751094125888171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863096789167396083925447 2794645183751094125888171)
        ·
          refine ⟨4191967775626641188832257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794645183751094125888171 4191967775626641188832257)
          ·
            refine ⟨3143975831719980891624193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4191967775626641188832257 3143975831719980891624193)
            ·
              refine ⟨2357981873789985668718145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143975831719980891624193 2357981873789985668718145)
              ·
                refine ⟨1768486405342489251538609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2357981873789985668718145 1768486405342489251538609)
                ·
                  refine ⟨1326364804006866938653957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768486405342489251538609 1326364804006866938653957)
                  ·
                    refine ⟨248693400751287550997617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326364804006866938653957 248693400751287550997617)
                    ·
                      rfl

theorem cell22_726493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_726493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726493 prefixEnd_726493 := by exact prefixLift 726493
  have htrace : WordTrace (prefixWord ++ tailWord_726493) baseStart_726493 baseEnd_726493 := by
    simpa [prefixWord, tailWord_726493, baseEnd_726493] using wordTrace_append hprefix tailTrace_726493
  have hstable : (prefixWord ++ tailWord_726493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726493).length < 2 ^ (prefixWord ++ tailWord_726493).sum := by decide
  have hdescent : baseEnd_726493 < baseStart_726493 := by decide
  rcases family_descends (prefixWord ++ tailWord_726493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726570 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_726570 : Nat := 118140960795 + 726570 * 2 ^ 59
def prefixEnd_726570 : Nat := 4983230072969 + 3 ^ 40 * 726570 * 2
def baseEnd_726570 : Nat := 82906586474961672274127

theorem tailTrace_726570 : CollatzResearch.WordTrace tailWord_726570 prefixEnd_726570 82906586474961672274127 := by
  unfold tailWord_726570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6625046244442113280484291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17666789985178968747958109 6625046244442113280484291)
  ·
    refine ⟨9937569366663169920726437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6625046244442113280484291 9937569366663169920726437)
    ·
      refine ⟨1863294256249344360136207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9937569366663169920726437 1863294256249344360136207)
      ·
        refine ⟨2794941384374016540204311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863294256249344360136207 2794941384374016540204311)
        ·
          refine ⟨4192412076561024810306467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794941384374016540204311 4192412076561024810306467)
          ·
            refine ⟨6288618114841537215459701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192412076561024810306467 6288618114841537215459701)
            ·
              refine ⟨589557948266394113949347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6288618114841537215459701 589557948266394113949347)
              ·
                refine ⟨884336922399591170924021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589557948266394113949347 884336922399591170924021)
                ·
                  refine ⟨82906586474961672274127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 884336922399591170924021 82906586474961672274127)
                  ·
                    rfl

theorem cell22_726570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_726570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726570 prefixEnd_726570 := by exact prefixLift 726570
  have htrace : WordTrace (prefixWord ++ tailWord_726570) baseStart_726570 baseEnd_726570 := by
    simpa [prefixWord, tailWord_726570, baseEnd_726570] using wordTrace_append hprefix tailTrace_726570
  have hstable : (prefixWord ++ tailWord_726570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726570).length < 2 ^ (prefixWord ++ tailWord_726570).sum := by decide
  have hdescent : baseEnd_726570 < baseStart_726570 := by decide
  rcases family_descends (prefixWord ++ tailWord_726570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726583 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 1, 4]
def baseStart_726583 : Nat := 118140960795 + 726583 * 2 ^ 59
def prefixEnd_726583 : Nat := 4983230072969 + 3 ^ 40 * 726583 * 2
def baseEnd_726583 : Nat := 248724209590557316247341

theorem tailTrace_726583 : CollatzResearch.WordTrace tailWord_726583 prefixEnd_726583 248724209590557316247341 := by
  unfold tailWord_726583
  simp only [CollatzResearch.WordTrace]
  refine ⟨26500659126721356342160403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17667106084480904228106935 26500659126721356342160403)
  ·
    refine ⟨39750988690082034513240605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26500659126721356342160403 39750988690082034513240605)
    ·
      refine ⟨14906620758780762942465227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39750988690082034513240605 14906620758780762942465227)
      ·
        refine ⟨22359931138171144413697841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14906620758780762942465227 22359931138171144413697841)
        ·
          refine ⟨16769948353628358310273381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22359931138171144413697841 16769948353628358310273381)
          ·
            refine ⟨3144365316305317183176259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16769948353628358310273381 3144365316305317183176259)
            ·
              refine ⟨4716547974457975774764389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144365316305317183176259 4716547974457975774764389)
              ·
                refine ⟨884352745210870457768323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4716547974457975774764389 884352745210870457768323)
                ·
                  refine ⟨1326529117816305686652485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884352745210870457768323 1326529117816305686652485)
                  ·
                    refine ⟨248724209590557316247341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326529117816305686652485 248724209590557316247341)
                    ·
                      rfl

theorem cell22_726583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_726583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726583 prefixEnd_726583 := by exact prefixLift 726583
  have htrace : WordTrace (prefixWord ++ tailWord_726583) baseStart_726583 baseEnd_726583 := by
    simpa [prefixWord, tailWord_726583, baseEnd_726583] using wordTrace_append hprefix tailTrace_726583
  have hstable : (prefixWord ++ tailWord_726583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726583).length < 2 ^ (prefixWord ++ tailWord_726583).sum := by decide
  have hdescent : baseEnd_726583 < baseStart_726583 := by decide
  rcases family_descends (prefixWord ++ tailWord_726583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726621 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 5]
def baseStart_726621 : Nat := 118140960795 + 726621 * 2 ^ 59
def prefixEnd_726621 : Nat := 4983230072969 + 3 ^ 40 * 726621 * 2
def baseEnd_726621 : Nat := 82912405922379294599075

theorem tailTrace_726621 : CollatzResearch.WordTrace tailWord_726621 prefixEnd_726621 82912405922379294599075 := by
  unfold tailWord_726621
  simp only [CollatzResearch.WordTrace]
  refine ⟨26502045100583688832043717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17668030067055792554695811 26502045100583688832043717)
  ·
    refine ⟨4969133456359441656008197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26502045100583688832043717 4969133456359441656008197)
    ·
      refine ⟨931712523067395310501537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4969133456359441656008197 931712523067395310501537)
      ·
        refine ⟨698784392300546482876153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 931712523067395310501537 698784392300546482876153)
        ·
          refine ⟨524088294225409862157115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698784392300546482876153 524088294225409862157115)
          ·
            refine ⟨786132441338114793235673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524088294225409862157115 786132441338114793235673)
            ·
              refine ⟨589599331003586094926755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786132441338114793235673 589599331003586094926755)
              ·
                refine ⟨884398996505379142390133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589599331003586094926755 884398996505379142390133)
                ·
                  refine ⟨82912405922379294599075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 884398996505379142390133 82912405922379294599075)
                  ·
                    rfl

theorem cell22_726621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_726621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726621 prefixEnd_726621 := by exact prefixLift 726621
  have htrace : WordTrace (prefixWord ++ tailWord_726621) baseStart_726621 baseEnd_726621 := by
    simpa [prefixWord, tailWord_726621, baseEnd_726621] using wordTrace_append hprefix tailTrace_726621
  have hstable : (prefixWord ++ tailWord_726621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726621).length < 2 ^ (prefixWord ++ tailWord_726621).sum := by decide
  have hdescent : baseEnd_726621 < baseStart_726621 := by decide
  rcases family_descends (prefixWord ++ tailWord_726621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726641 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_726641 : Nat := 118140960795 + 726641 * 2 ^ 59
def prefixEnd_726641 : Nat := 4983230072969 + 3 ^ 40 * 726641 * 2
def baseEnd_726641 : Nat := 248744064175864498297163

theorem tailTrace_726641 : CollatzResearch.WordTrace tailWord_726641 prefixEnd_726641 248744064175864498297163 := by
  unfold tailWord_726641
  simp only [CollatzResearch.WordTrace]
  refine ⟨26502774560511232247771777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17668516373674154831847851 26502774560511232247771777)
  ·
    refine ⟨19877080920383424185828833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26502774560511232247771777 19877080920383424185828833)
    ·
      refine ⟨14907810690287568139371625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19877080920383424185828833 14907810690287568139371625)
      ·
        refine ⟨11180858017715676104528719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14907810690287568139371625 11180858017715676104528719)
        ·
          refine ⟨16771287026573514156793079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11180858017715676104528719 16771287026573514156793079)
          ·
            refine ⟨25156930539860271235189619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16771287026573514156793079 25156930539860271235189619)
            ·
              refine ⟨37735395809790406852784429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25156930539860271235189619 37735395809790406852784429)
              ·
                refine ⟨14150773428671402569794161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37735395809790406852784429 14150773428671402569794161)
                ·
                  refine ⟨10613080071503551927345621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14150773428671402569794161 10613080071503551927345621)
                  ·
                    refine ⟨248744064175864498297163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10613080071503551927345621 248744064175864498297163)
                    ·
                      rfl

theorem cell22_726641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_726641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726641 prefixEnd_726641 := by exact prefixLift 726641
  have htrace : WordTrace (prefixWord ++ tailWord_726641) baseStart_726641 baseEnd_726641 := by
    simpa [prefixWord, tailWord_726641, baseEnd_726641] using wordTrace_append hprefix tailTrace_726641
  have hstable : (prefixWord ++ tailWord_726641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726641).length < 2 ^ (prefixWord ++ tailWord_726641).sum := by decide
  have hdescent : baseEnd_726641 < baseStart_726641 := by decide
  rcases family_descends (prefixWord ++ tailWord_726641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726645 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_726645 : Nat := 118140960795 + 726645 * 2 ^ 59
def prefixEnd_726645 : Nat := 4983230072969 + 3 ^ 40 * 726645 * 2
def baseEnd_726645 : Nat := 248745433457609821197151

theorem tailTrace_726645 : CollatzResearch.WordTrace tailWord_726645 prefixEnd_726645 248745433457609821197151 := by
  unfold tailWord_726645
  simp only [CollatzResearch.WordTrace]
  refine ⟨26502920452496740930917389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17668613634997827287278259 26502920452496740930917389)
  ·
    refine ⟨9938595169686277849094021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26502920452496740930917389 9938595169686277849094021)
    ·
      refine ⟨1863486594316177096705129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9938595169686277849094021 1863486594316177096705129)
      ·
        refine ⟨1397614945737132822528847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1863486594316177096705129 1397614945737132822528847)
        ·
          refine ⟨2096422418605699233793271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397614945737132822528847 2096422418605699233793271)
          ·
            refine ⟨3144633627908548850689907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096422418605699233793271 3144633627908548850689907)
            ·
              refine ⟨4716950441862823276034861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3144633627908548850689907 4716950441862823276034861)
              ·
                refine ⟨1768856415698558728513073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4716950441862823276034861 1768856415698558728513073)
                ·
                  refine ⟨1326642311773919046384805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768856415698558728513073 1326642311773919046384805)
                  ·
                    refine ⟨248745433457609821197151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326642311773919046384805 248745433457609821197151)
                    ·
                      rfl

theorem cell22_726645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_726645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726645 prefixEnd_726645 := by exact prefixLift 726645
  have htrace : WordTrace (prefixWord ++ tailWord_726645) baseStart_726645 baseEnd_726645 := by
    simpa [prefixWord, tailWord_726645, baseEnd_726645] using wordTrace_append hprefix tailTrace_726645
  have hstable : (prefixWord ++ tailWord_726645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726645).length < 2 ^ (prefixWord ++ tailWord_726645).sum := by decide
  have hdescent : baseEnd_726645 < baseStart_726645 := by decide
  rcases family_descends (prefixWord ++ tailWord_726645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726664 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 2, 3]
def baseStart_726664 : Nat := 118140960795 + 726664 * 2 ^ 59
def prefixEnd_726664 : Nat := 4983230072969 + 3 ^ 40 * 726664 * 2
def baseEnd_726664 : Nat := 248751937545900104972093

theorem tailTrace_726664 : CollatzResearch.WordTrace tailWord_726664 prefixEnd_726664 248751937545900104972093 := by
  unfold tailWord_726664
  simp only [CollatzResearch.WordTrace]
  refine ⟨13251806719713953587929523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17669075626285271450572697 13251806719713953587929523)
  ·
    refine ⟨19877710079570930381894285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13251806719713953587929523 19877710079570930381894285)
    ·
      refine ⟨7454141279839098893210357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19877710079570930381894285 7454141279839098893210357)
      ·
        refine ⟨698825744984915521238471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7454141279839098893210357 698825744984915521238471)
        ·
          refine ⟨1048238617477373281857707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698825744984915521238471 1048238617477373281857707)
          ·
            refine ⟨1572357926216059922786561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048238617477373281857707 1572357926216059922786561)
            ·
              refine ⟨1179268444662044942089921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1572357926216059922786561 1179268444662044942089921)
              ·
                refine ⟨884451333496533706567441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1179268444662044942089921 884451333496533706567441)
                ·
                  refine ⟨663338500122400279925581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 884451333496533706567441 663338500122400279925581)
                  ·
                    refine ⟨248751937545900104972093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 663338500122400279925581 248751937545900104972093)
                    ·
                      rfl

theorem cell22_726664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_726664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726664 prefixEnd_726664 := by exact prefixLift 726664
  have htrace : WordTrace (prefixWord ++ tailWord_726664) baseStart_726664 baseEnd_726664 := by
    simpa [prefixWord, tailWord_726664, baseEnd_726664] using wordTrace_append hprefix tailTrace_726664
  have hstable : (prefixWord ++ tailWord_726664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726664).length < 2 ^ (prefixWord ++ tailWord_726664).sum := by decide
  have hdescent : baseEnd_726664 < baseStart_726664 := by decide
  rcases family_descends (prefixWord ++ tailWord_726664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726696 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 2, 4]
def baseStart_726696 : Nat := 118140960795 + 726696 * 2 ^ 59
def prefixEnd_726696 : Nat := 4983230072969 + 3 ^ 40 * 726696 * 2
def baseEnd_726696 : Nat := 248762891799862688171995

theorem tailTrace_726696 : CollatzResearch.WordTrace tailWord_726696 prefixEnd_726696 248762891799862688171995 := by
  unfold tailWord_726696
  simp only [CollatzResearch.WordTrace]
  refine ⟨13252390287655988320511971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17669853716874651094015961 13252390287655988320511971)
  ·
    refine ⟨19878585431483982480767957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13252390287655988320511971 19878585431483982480767957)
    ·
      refine ⟨465904346050405839392999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19878585431483982480767957 465904346050405839392999)
      ·
        refine ⟨698856519075608759089499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465904346050405839392999 698856519075608759089499)
        ·
          refine ⟨1048284778613413138634249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698856519075608759089499 1048284778613413138634249)
          ·
            refine ⟨786213583960059853975687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048284778613413138634249 786213583960059853975687)
            ·
              refine ⟨1179320375940089780963531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786213583960059853975687 1179320375940089780963531)
              ·
                refine ⟨1768980563910134671445297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179320375940089780963531 1768980563910134671445297)
                ·
                  refine ⟨1326735422932601003583973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1768980563910134671445297 1326735422932601003583973)
                  ·
                    refine ⟨248762891799862688171995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326735422932601003583973 248762891799862688171995)
                    ·
                      rfl

theorem cell22_726696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_726696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726696 prefixEnd_726696 := by exact prefixLift 726696
  have htrace : WordTrace (prefixWord ++ tailWord_726696) baseStart_726696 baseEnd_726696 := by
    simpa [prefixWord, tailWord_726696, baseEnd_726696] using wordTrace_append hprefix tailTrace_726696
  have hstable : (prefixWord ++ tailWord_726696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726696).length < 2 ^ (prefixWord ++ tailWord_726696).sum := by decide
  have hdescent : baseEnd_726696 < baseStart_726696 := by decide
  rcases family_descends (prefixWord ++ tailWord_726696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726726 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_726726 : Nat := 118140960795 + 726726 * 2 ^ 59
def prefixEnd_726726 : Nat := 4983230072969 + 3 ^ 40 * 726726 * 2
def baseEnd_726726 : Nat := 248773161412952609921903

theorem tailTrace_726726 : CollatzResearch.WordTrace tailWord_726726 prefixEnd_726726 248773161412952609921903 := by
  unfold tailWord_726726
  simp only [CollatzResearch.WordTrace]
  refine ⟨828308586412602867644251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17670583176802194509744021 828308586412602867644251)
  ·
    refine ⟨1242462879618904301466377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 828308586412602867644251 1242462879618904301466377)
    ·
      refine ⟨931847159714178226099783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1242462879618904301466377 931847159714178226099783)
      ·
        refine ⟨1397770739571267339149675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931847159714178226099783 1397770739571267339149675)
        ·
          refine ⟨2096656109356901008724513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397770739571267339149675 2096656109356901008724513)
          ·
            refine ⟨1572492082017675756543385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2096656109356901008724513 1572492082017675756543385)
            ·
              refine ⟨1179369061513256817407539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1572492082017675756543385 1179369061513256817407539)
              ·
                refine ⟨1769053592269885226111309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179369061513256817407539 1769053592269885226111309)
                ·
                  refine ⟨663395097101206959791741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1769053592269885226111309 663395097101206959791741)
                  ·
                    refine ⟨248773161412952609921903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 663395097101206959791741 248773161412952609921903)
                    ·
                      rfl

theorem cell22_726726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_726726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726726 prefixEnd_726726 := by exact prefixLift 726726
  have htrace : WordTrace (prefixWord ++ tailWord_726726) baseStart_726726 baseEnd_726726 := by
    simpa [prefixWord, tailWord_726726, baseEnd_726726] using wordTrace_append hprefix tailTrace_726726
  have hstable : (prefixWord ++ tailWord_726726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726726).length < 2 ^ (prefixWord ++ tailWord_726726).sum := by decide
  have hdescent : baseEnd_726726 < baseStart_726726 := by decide
  rcases family_descends (prefixWord ++ tailWord_726726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726763 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 1, 6]
def baseStart_726763 : Nat := 118140960795 + 726763 * 2 ^ 59
def prefixEnd_726763 : Nat := 4983230072969 + 3 ^ 40 * 726763 * 2
def baseEnd_726763 : Nat := 248785827269096846746789

theorem tailTrace_726763 : CollatzResearch.WordTrace tailWord_726763 prefixEnd_726763 248785827269096846746789 := by
  unfold tailWord_726763
  simp only [CollatzResearch.WordTrace]
  refine ⟨26507224266069247083712943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17671482844046164722475295 26507224266069247083712943)
  ·
    refine ⟨39760836399103870625569415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26507224266069247083712943 39760836399103870625569415)
    ·
      refine ⟨59641254598655805938354123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39760836399103870625569415 59641254598655805938354123)
      ·
        refine ⟨89461881897983708907531185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59641254598655805938354123 89461881897983708907531185)
        ·
          refine ⟨67096411423487781680648389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89461881897983708907531185 67096411423487781680648389)
          ·
            refine ⟨12580577141903959065121573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67096411423487781680648389 12580577141903959065121573)
            ·
              refine ⟨2358858214106992324710295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12580577141903959065121573 2358858214106992324710295)
              ·
                refine ⟨3538287321160488487065443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358858214106992324710295 3538287321160488487065443)
                ·
                  refine ⟨5307430981740732730598165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3538287321160488487065443 5307430981740732730598165)
                  ·
                    refine ⟨248785827269096846746789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5307430981740732730598165 248785827269096846746789)
                    ·
                      rfl

theorem cell22_726763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 6].length) (baseStart_726763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726763 prefixEnd_726763 := by exact prefixLift 726763
  have htrace : WordTrace (prefixWord ++ tailWord_726763) baseStart_726763 baseEnd_726763 := by
    simpa [prefixWord, tailWord_726763, baseEnd_726763] using wordTrace_append hprefix tailTrace_726763
  have hstable : (prefixWord ++ tailWord_726763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726763).length < 2 ^ (prefixWord ++ tailWord_726763).sum := by decide
  have hdescent : baseEnd_726763 < baseStart_726763 := by decide
  rcases family_descends (prefixWord ++ tailWord_726763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726780 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_726780 : Nat := 118140960795 + 726780 * 2 ^ 59
def prefixEnd_726780 : Nat := 4983230072969 + 3 ^ 40 * 726780 * 2
def baseEnd_726780 : Nat := 248791646716514469071737

theorem tailTrace_726780 : CollatzResearch.WordTrace tailWord_726780 prefixEnd_726780 248791646716514469071737 := by
  unfold tailWord_726780
  simp only [CollatzResearch.WordTrace]
  refine ⟨13253922153503829493540897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17671896204671772658054529 13253922153503829493540897)
  ·
    refine ⟨9940441615127872120155673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13253922153503829493540897 9940441615127872120155673)
    ·
      refine ⟨7455331211345904090116755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9940441615127872120155673 7455331211345904090116755)
      ·
        refine ⟨11182996817018856135175133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7455331211345904090116755 11182996817018856135175133)
        ·
          refine ⟨4193623806382071050690675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11182996817018856135175133 4193623806382071050690675)
          ·
            refine ⟨6290435709573106576036013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4193623806382071050690675 6290435709573106576036013)
            ·
              refine ⟨2358913391089914966013505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6290435709573106576036013 2358913391089914966013505)
              ·
                refine ⟨1769185043317436224510129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2358913391089914966013505 1769185043317436224510129)
                ·
                  refine ⟨1326888782488077168382597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1769185043317436224510129 1326888782488077168382597)
                  ·
                    refine ⟨248791646716514469071737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1326888782488077168382597 248791646716514469071737)
                    ·
                      rfl

theorem cell22_726780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_726780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726780 prefixEnd_726780 := by exact prefixLift 726780
  have htrace : WordTrace (prefixWord ++ tailWord_726780) baseStart_726780 baseEnd_726780 := by
    simpa [prefixWord, tailWord_726780, baseEnd_726780] using wordTrace_append hprefix tailTrace_726780
  have hstable : (prefixWord ++ tailWord_726780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726780).length < 2 ^ (prefixWord ++ tailWord_726780).sum := by decide
  have hdescent : baseEnd_726780 < baseStart_726780 := by decide
  rcases family_descends (prefixWord ++ tailWord_726780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726840 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 5]
def baseStart_726840 : Nat := 118140960795 + 726840 * 2 ^ 59
def prefixEnd_726840 : Nat := 4983230072969 + 3 ^ 40 * 726840 * 2
def baseEnd_726840 : Nat := 82937395314231437523851

theorem tailTrace_726840 : CollatzResearch.WordTrace tailWord_726840 prefixEnd_726840 82937395314231437523851 := by
  unfold tailWord_726840
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255016343395144617132987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17673355124526859489510649 13255016343395144617132987)
  ·
    refine ⟨19882524515092716925699481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13255016343395144617132987 19882524515092716925699481)
    ·
      refine ⟨14911893386319537694274611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19882524515092716925699481 14911893386319537694274611)
      ·
        refine ⟨22367840079479306541411917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14911893386319537694274611 22367840079479306541411917)
        ·
          refine ⟨8387940029804739953029469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22367840079479306541411917 8387940029804739953029469)
          ·
            refine ⟨3145477511176777482386051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8387940029804739953029469 3145477511176777482386051)
            ·
              refine ⟨4718216266765166223579077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145477511176777482386051 4718216266765166223579077)
              ·
                refine ⟨884665550018468666921077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4718216266765166223579077 884665550018468666921077)
                ·
                  refine ⟨82937395314231437523851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 884665550018468666921077 82937395314231437523851)
                  ·
                    rfl

theorem cell22_726840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_726840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726840 prefixEnd_726840 := by exact prefixLift 726840
  have htrace : WordTrace (prefixWord ++ tailWord_726840) baseStart_726840 baseEnd_726840 := by
    simpa [prefixWord, tailWord_726840, baseEnd_726840] using wordTrace_append hprefix tailTrace_726840
  have hstable : (prefixWord ++ tailWord_726840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726840).length < 2 ^ (prefixWord ++ tailWord_726840).sum := by decide
  have hdescent : baseEnd_726840 < baseStart_726840 := by decide
  rcases family_descends (prefixWord ++ tailWord_726840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726887 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 1, 4]
def baseStart_726887 : Nat := 118140960795 + 726887 * 2 ^ 59
def prefixEnd_726887 : Nat := 4983230072969 + 3 ^ 40 * 726887 * 2
def baseEnd_726887 : Nat := 248828275003201856646409

theorem tailTrace_726887 : CollatzResearch.WordTrace tailWord_726887 prefixEnd_726887 248828275003201856646409 := by
  unfold tailWord_726887
  simp only [CollatzResearch.WordTrace]
  refine ⟨26511746917620016261226915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17674497945080010840817943 26511746917620016261226915)
  ·
    refine ⟨39767620376430024391840373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26511746917620016261226915 39767620376430024391840373)
    ·
      refine ⟨3728214410290314786735035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39767620376430024391840373 3728214410290314786735035)
      ·
        refine ⟨5592321615435472180102553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728214410290314786735035 5592321615435472180102553)
        ·
          refine ⟨4194241211576604135076915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5592321615435472180102553 4194241211576604135076915)
          ·
            refine ⟨6291361817364906202615373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4194241211576604135076915 6291361817364906202615373)
            ·
              refine ⟨2359260681511839825980765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6291361817364906202615373 2359260681511839825980765)
              ·
                refine ⟨884722755566939934742787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2359260681511839825980765 884722755566939934742787)
                ·
                  refine ⟨1327084133350409902114181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884722755566939934742787 1327084133350409902114181)
                  ·
                    refine ⟨248828275003201856646409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1327084133350409902114181 248828275003201856646409)
                    ·
                      rfl

theorem cell22_726887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_726887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726887 prefixEnd_726887 := by exact prefixLift 726887
  have htrace : WordTrace (prefixWord ++ tailWord_726887) baseStart_726887 baseEnd_726887 := by
    simpa [prefixWord, tailWord_726887, baseEnd_726887] using wordTrace_append hprefix tailTrace_726887
  have hstable : (prefixWord ++ tailWord_726887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726887).length < 2 ^ (prefixWord ++ tailWord_726887).sum := by decide
  have hdescent : baseEnd_726887 < baseStart_726887 := by decide
  rcases family_descends (prefixWord ++ tailWord_726887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726915 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 1, 6]
def baseStart_726915 : Nat := 118140960795 + 726915 * 2 ^ 59
def prefixEnd_726915 : Nat := 4983230072969 + 3 ^ 40 * 726915 * 2
def baseEnd_726915 : Nat := 248837859975419116946323

theorem tailTrace_726915 : CollatzResearch.WordTrace tailWord_726915 prefixEnd_726915 248837859975419116946323 := by
  unfold tailWord_726915
  simp only [CollatzResearch.WordTrace]
  refine ⟨26512768161518577043246199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17675178774345718028830799 26512768161518577043246199)
  ·
    refine ⟨39769152242277865564869299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26512768161518577043246199 39769152242277865564869299)
    ·
      refine ⟨59653728363416798347303949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39769152242277865564869299 59653728363416798347303949)
      ·
        refine ⟨22370148136281299380238981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59653728363416798347303949 22370148136281299380238981)
        ·
          refine ⟨4194402775552743633794809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22370148136281299380238981 4194402775552743633794809)
          ·
            refine ⟨3145802081664557725346107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194402775552743633794809 3145802081664557725346107)
            ·
              refine ⟨4718703122496836588019161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145802081664557725346107 4718703122496836588019161)
              ·
                refine ⟨3539027341872627441014371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4718703122496836588019161 3539027341872627441014371)
                ·
                  refine ⟨5308541012808941161521557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539027341872627441014371 5308541012808941161521557)
                  ·
                    refine ⟨248837859975419116946323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5308541012808941161521557 248837859975419116946323)
                    ·
                      rfl

theorem cell22_726915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_726915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726915 prefixEnd_726915 := by exact prefixLift 726915
  have htrace : WordTrace (prefixWord ++ tailWord_726915) baseStart_726915 baseEnd_726915 := by
    simpa [prefixWord, tailWord_726915, baseEnd_726915] using wordTrace_append hprefix tailTrace_726915
  have hstable : (prefixWord ++ tailWord_726915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726915).length < 2 ^ (prefixWord ++ tailWord_726915).sum := by decide
  have hdescent : baseEnd_726915 < baseStart_726915 := by decide
  rcases family_descends (prefixWord ++ tailWord_726915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726932 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_726932 : Nat := 118140960795 + 726932 * 2 ^ 59
def prefixEnd_726932 : Nat := 4983230072969 + 3 ^ 40 * 726932 * 2
def baseEnd_726932 : Nat := 248843679422836739271271

theorem tailTrace_726932 : CollatzResearch.WordTrace tailWord_726932 prefixEnd_726932 248843679422836739271271 := by
  unfold tailWord_726932
  simp only [CollatzResearch.WordTrace]
  refine ⟨13256694101228494473307525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17675592134971325964410033 13256694101228494473307525)
  ·
    refine ⟨2485630143980342713745161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13256694101228494473307525 2485630143980342713745161)
    ·
      refine ⟨1864222607985257035308871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2485630143980342713745161 1864222607985257035308871)
      ·
        refine ⟨2796333911977885552963307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864222607985257035308871 2796333911977885552963307)
        ·
          refine ⟨4194500867966828329444961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796333911977885552963307 4194500867966828329444961)
          ·
            refine ⟨3145875650975121247083721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194500867966828329444961 3145875650975121247083721)
            ·
              refine ⟨2359406738231340935312791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3145875650975121247083721 2359406738231340935312791)
              ·
                refine ⟨3539110107347011402969187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359406738231340935312791 3539110107347011402969187)
                ·
                  refine ⟨5308665161020517104453781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3539110107347011402969187 5308665161020517104453781)
                  ·
                    refine ⟨248843679422836739271271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5308665161020517104453781 248843679422836739271271)
                    ·
                      rfl

theorem cell22_726932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_726932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726932 prefixEnd_726932 := by exact prefixLift 726932
  have htrace : WordTrace (prefixWord ++ tailWord_726932) baseStart_726932 baseEnd_726932 := by
    simpa [prefixWord, tailWord_726932, baseEnd_726932] using wordTrace_append hprefix tailTrace_726932
  have hstable : (prefixWord ++ tailWord_726932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726932).length < 2 ^ (prefixWord ++ tailWord_726932).sum := by decide
  have hdescent : baseEnd_726932 < baseStart_726932 := by decide
  rcases family_descends (prefixWord ++ tailWord_726932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726996 : List Nat := [2, 4, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_726996 : Nat := 118140960795 + 726996 * 2 ^ 59
def prefixEnd_726996 : Nat := 4983230072969 + 3 ^ 40 * 726996 * 2
def baseEnd_726996 : Nat := 248865587930761905671075

theorem tailTrace_726996 : CollatzResearch.WordTrace tailWord_726996 prefixEnd_726996 248865587930761905671075 := by
  unfold tailWord_726996
  simp only [CollatzResearch.WordTrace]
  refine ⟨13257861237112563938472421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17677148316150085251296561 13257861237112563938472421)
  ·
    refine ⟨2485848981958605738463579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13257861237112563938472421 2485848981958605738463579)
    ·
      refine ⟨3728773472937908607695369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485848981958605738463579 3728773472937908607695369)
      ·
        refine ⟨2796580104703431455771527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3728773472937908607695369 2796580104703431455771527)
        ·
          refine ⟨4194870157055147183657291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796580104703431455771527 4194870157055147183657291)
          ·
            refine ⟨6292305235582720775485937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4194870157055147183657291 6292305235582720775485937)
            ·
              refine ⟨4719228926687040581614453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6292305235582720775485937 4719228926687040581614453)
              ·
                refine ⟨442427711876910054526355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4719228926687040581614453 442427711876910054526355)
                ·
                  refine ⟨663641567815365081789533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442427711876910054526355 663641567815365081789533)
                  ·
                    refine ⟨248865587930761905671075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 663641567815365081789533 248865587930761905671075)
                    ·
                      rfl

theorem cell22_726996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_726996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_726996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_726996 prefixEnd_726996 := by exact prefixLift 726996
  have htrace : WordTrace (prefixWord ++ tailWord_726996) baseStart_726996 baseEnd_726996 := by
    simpa [prefixWord, tailWord_726996, baseEnd_726996] using wordTrace_append hprefix tailTrace_726996
  have hstable : (prefixWord ++ tailWord_726996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726996).length < 2 ^ (prefixWord ++ tailWord_726996).sum := by decide
  have hdescent : baseEnd_726996 < baseStart_726996 := by decide
  rcases family_descends (prefixWord ++ tailWord_726996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727020 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 10]
def baseStart_727020 : Nat := 118140960795 + 727020 * 2 ^ 59
def prefixEnd_727020 : Nat := 4983230072969 + 3 ^ 40 * 727020 * 2
def baseEnd_727020 : Nat := 82957934540411281023667

theorem tailTrace_727020 : CollatzResearch.WordTrace tailWord_727020 prefixEnd_727020 82957934540411281023667 := by
  unfold tailWord_727020
  simp only [CollatzResearch.WordTrace]
  refine ⟨13258298913069089987909257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17677731884092119983879009 13258298913069089987909257)
  ·
    refine ⟨9943724184801817490931943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13258298913069089987909257 9943724184801817490931943)
    ·
      refine ⟨14915586277202726236397915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9943724184801817490931943 14915586277202726236397915)
      ·
        refine ⟨22373379415804089354596873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14915586277202726236397915 22373379415804089354596873)
        ·
          refine ⟨16780034561853067015947655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22373379415804089354596873 16780034561853067015947655)
          ·
            refine ⟨25170051842779600523921483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16780034561853067015947655 25170051842779600523921483)
            ·
              refine ⟨37755077764169400785882225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25170051842779600523921483 37755077764169400785882225)
              ·
                refine ⟨28316308323127050589411669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37755077764169400785882225 28316308323127050589411669)
                ·
                  refine ⟨82957934540411281023667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 28316308323127050589411669 82957934540411281023667)
                  ·
                    rfl

theorem cell22_727020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_727020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727020 prefixEnd_727020 := by exact prefixLift 727020
  have htrace : WordTrace (prefixWord ++ tailWord_727020) baseStart_727020 baseEnd_727020 := by
    simpa [prefixWord, tailWord_727020, baseEnd_727020] using wordTrace_append hprefix tailTrace_727020
  have hstable : (prefixWord ++ tailWord_727020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727020).length < 2 ^ (prefixWord ++ tailWord_727020).sum := by decide
  have hdescent : baseEnd_727020 < baseStart_727020 := by decide
  rcases family_descends (prefixWord ++ tailWord_727020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727052 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_727052 : Nat := 118140960795 + 727052 * 2 ^ 59
def prefixEnd_727052 : Nat := 4983230072969 + 3 ^ 40 * 727052 * 2
def baseEnd_727052 : Nat := 248884757875196426270903

theorem tailTrace_727052 : CollatzResearch.WordTrace tailWord_727052 prefixEnd_727052 248884757875196426270903 := by
  unfold tailWord_727052
  simp only [CollatzResearch.WordTrace]
  refine ⟨13258882481011124720491705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17678509974681499627322273 13258882481011124720491705)
  ·
    refine ⟨9944161860758343540368779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13258882481011124720491705 9944161860758343540368779)
    ·
      refine ⟨14916242791137515310553169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9944161860758343540368779 14916242791137515310553169)
      ·
        refine ⟨11187182093353136482914877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14916242791137515310553169 11187182093353136482914877)
        ·
          refine ⟨4195193285007426181093079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11187182093353136482914877 4195193285007426181093079)
          ·
            refine ⟨6292789927511139271639619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4195193285007426181093079 6292789927511139271639619)
            ·
              refine ⟨9439184891266708907459429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6292789927511139271639619 9439184891266708907459429)
              ·
                refine ⟨1769847167112507920148643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9439184891266708907459429 1769847167112507920148643)
                ·
                  refine ⟨2654770750668761880222965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769847167112507920148643 2654770750668761880222965)
                  ·
                    refine ⟨248884757875196426270903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2654770750668761880222965 248884757875196426270903)
                    ·
                      rfl

theorem cell22_727052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_727052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727052 prefixEnd_727052 := by exact prefixLift 727052
  have htrace : WordTrace (prefixWord ++ tailWord_727052) baseStart_727052 baseEnd_727052 := by
    simpa [prefixWord, tailWord_727052, baseEnd_727052] using wordTrace_append hprefix tailTrace_727052
  have hstable : (prefixWord ++ tailWord_727052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727052).length < 2 ^ (prefixWord ++ tailWord_727052).sum := by decide
  have hdescent : baseEnd_727052 < baseStart_727052 := by decide
  rcases family_descends (prefixWord ++ tailWord_727052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727060 : List Nat := [2, 4, 3, 2, 2, 1, 1, 2, 5]
def baseStart_727060 : Nat := 118140960795 + 727060 * 2 ^ 59
def prefixEnd_727060 : Nat := 4983230072969 + 3 ^ 40 * 727060 * 2
def baseEnd_727060 : Nat := 82962498812895690690293

theorem tailTrace_727060 : CollatzResearch.WordTrace tailWord_727060 prefixEnd_727060 82962498812895690690293 := by
  unfold tailWord_727060
  simp only [CollatzResearch.WordTrace]
  refine ⟨13259028372996633403637317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17678704497328844538183089 13259028372996633403637317)
  ·
    refine ⟨2486067819936868763181997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13259028372996633403637317 2486067819936868763181997)
    ·
      refine ⟨932275432476325786193249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2486067819936868763181997 932275432476325786193249)
      ·
        refine ⟨699206574357244339644937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 932275432476325786193249 699206574357244339644937)
        ·
          refine ⟨524404930767933254733703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699206574357244339644937 524404930767933254733703)
          ·
            refine ⟨786607396151899882100555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524404930767933254733703 786607396151899882100555)
            ·
              refine ⟨1179911094227849823150833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786607396151899882100555 1179911094227849823150833)
              ·
                refine ⟨884933320670887367363125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1179911094227849823150833 884933320670887367363125)
                ·
                  refine ⟨82962498812895690690293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 884933320670887367363125 82962498812895690690293)
                  ·
                    rfl

theorem cell22_727060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_727060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727060 prefixEnd_727060 := by exact prefixLift 727060
  have htrace : WordTrace (prefixWord ++ tailWord_727060) baseStart_727060 baseEnd_727060 := by
    simpa [prefixWord, tailWord_727060, baseEnd_727060] using wordTrace_append hprefix tailTrace_727060
  have hstable : (prefixWord ++ tailWord_727060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727060).length < 2 ^ (prefixWord ++ tailWord_727060).sum := by decide
  have hdescent : baseEnd_727060 < baseStart_727060 := by decide
  rcases family_descends (prefixWord ++ tailWord_727060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727086 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_727086 : Nat := 118140960795 + 727086 * 2 ^ 59
def prefixEnd_727086 : Nat := 4983230072969 + 3 ^ 40 * 727086 * 2
def baseEnd_727086 : Nat := 248896396770031670920799

theorem tailTrace_727086 : CollatzResearch.WordTrace tailWord_727086 prefixEnd_727086 248896396770031670920799 := by
  unfold tailWord_727086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314875630487384155965139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17679336695932715498480741 3314875630487384155965139)
  ·
    refine ⟨4972313445731076233947709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3314875630487384155965139 4972313445731076233947709)
    ·
      refine ⟨1864617542149153587730391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4972313445731076233947709 1864617542149153587730391)
      ·
        refine ⟨2796926313223730381595587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1864617542149153587730391 2796926313223730381595587)
        ·
          refine ⟨4195389469835595572393381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796926313223730381595587 4195389469835595572393381)
          ·
            refine ⟨786635525594174169823759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4195389469835595572393381 786635525594174169823759)
            ·
              refine ⟨1179953288391261254735639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786635525594174169823759 1179953288391261254735639)
              ·
                refine ⟨1769929932586891882103459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179953288391261254735639 1769929932586891882103459)
                ·
                  refine ⟨2654894898880337823155189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1769929932586891882103459 2654894898880337823155189)
                  ·
                    refine ⟨248896396770031670920799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2654894898880337823155189 248896396770031670920799)
                    ·
                      rfl

theorem cell22_727086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_727086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727086 prefixEnd_727086 := by exact prefixLift 727086
  have htrace : WordTrace (prefixWord ++ tailWord_727086) baseStart_727086 baseEnd_727086 := by
    simpa [prefixWord, tailWord_727086, baseEnd_727086] using wordTrace_append hprefix tailTrace_727086
  have hstable : (prefixWord ++ tailWord_727086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727086).length < 2 ^ (prefixWord ++ tailWord_727086).sum := by decide
  have hdescent : baseEnd_727086 < baseStart_727086 := by decide
  rcases family_descends (prefixWord ++ tailWord_727086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727127 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 7]
def baseStart_727127 : Nat := 118140960795 + 727127 * 2 ^ 59
def prefixEnd_727127 : Nat := 4983230072969 + 3 ^ 40 * 727127 * 2
def baseEnd_727127 : Nat := 82970143969307076881891

theorem tailTrace_727127 : CollatzResearch.WordTrace tailWord_727127 prefixEnd_727127 82970143969307076881891 := by
  unfold tailWord_727127
  simp only [CollatzResearch.WordTrace]
  refine ⟨26520500436750537249963635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17680333624500358166642423 26520500436750537249963635)
  ·
    refine ⟨39780750655125805874945453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26520500436750537249963635 39780750655125805874945453)
    ·
      refine ⟨14917781495672177203104545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39780750655125805874945453 14917781495672177203104545)
      ·
        refine ⟨11188336121754132902328409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14917781495672177203104545 11188336121754132902328409)
        ·
          refine ⟨8391252091315599676746307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11188336121754132902328409 8391252091315599676746307)
          ·
            refine ⟨12586878136973399515119461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8391252091315599676746307 12586878136973399515119461)
            ·
              refine ⟨2360039650682512409084899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12586878136973399515119461 2360039650682512409084899)
              ·
                refine ⟨3540059476023768613627349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360039650682512409084899 3540059476023768613627349)
                ·
                  refine ⟨82970143969307076881891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3540059476023768613627349 82970143969307076881891)
                  ·
                    rfl

theorem cell22_727127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 7].length) (baseStart_727127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727127 prefixEnd_727127 := by exact prefixLift 727127
  have htrace : WordTrace (prefixWord ++ tailWord_727127) baseStart_727127 baseEnd_727127 := by
    simpa [prefixWord, tailWord_727127, baseEnd_727127] using wordTrace_append hprefix tailTrace_727127
  have hstable : (prefixWord ++ tailWord_727127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727127).length < 2 ^ (prefixWord ++ tailWord_727127).sum := by decide
  have hdescent : baseEnd_727127 < baseStart_727127 := by decide
  rcases family_descends (prefixWord ++ tailWord_727127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727182 : List Nat := [4, 1, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_727182 : Nat := 118140960795 + 727182 * 2 ^ 59
def prefixEnd_727182 : Nat := 4983230072969 + 3 ^ 40 * 727182 * 2
def baseEnd_727182 : Nat := 248929259531919420520505

theorem tailTrace_727182 : CollatzResearch.WordTrace tailWord_727182 prefixEnd_727182 248929259531919420520505 := by
  unfold tailWord_727182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315313306443910205401975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17681670967700854428810533 3315313306443910205401975)
  ·
    refine ⟨4972969959665865308102963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3315313306443910205401975 4972969959665865308102963)
    ·
      refine ⟨7459454939498797962154445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4972969959665865308102963 7459454939498797962154445)
      ·
        refine ⟨2797295602312049235807917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7459454939498797962154445 2797295602312049235807917)
        ·
          refine ⟨1048985850867018463427969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2797295602312049235807917 1048985850867018463427969)
          ·
            refine ⟨786739388150263847570977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048985850867018463427969 786739388150263847570977)
            ·
              refine ⟨590054541112697885678233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786739388150263847570977 590054541112697885678233)
              ·
                refine ⟨442540905834523414258675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590054541112697885678233 442540905834523414258675)
                ·
                  refine ⟨663811358751785121388013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442540905834523414258675 663811358751785121388013)
                  ·
                    refine ⟨248929259531919420520505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 663811358751785121388013 248929259531919420520505)
                    ·
                      rfl

theorem cell22_727182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_727182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727182 prefixEnd_727182 := by exact prefixLift 727182
  have htrace : WordTrace (prefixWord ++ tailWord_727182) baseStart_727182 baseEnd_727182 := by
    simpa [prefixWord, tailWord_727182, baseEnd_727182] using wordTrace_append hprefix tailTrace_727182
  have hstable : (prefixWord ++ tailWord_727182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727182).length < 2 ^ (prefixWord ++ tailWord_727182).sum := by decide
  have hdescent : baseEnd_727182 < baseStart_727182 := by decide
  rcases family_descends (prefixWord ++ tailWord_727182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727187 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 5, 5]
def baseStart_727187 : Nat := 118140960795 + 727187 * 2 ^ 59
def prefixEnd_727187 : Nat := 4983230072969 + 3 ^ 40 * 727187 * 2
def baseEnd_727187 : Nat := 248930971134101074145489

theorem tailTrace_727187 : CollatzResearch.WordTrace tailWord_727187 prefixEnd_727187 248930971134101074145489 := by
  unfold tailWord_727187
  simp only [CollatzResearch.WordTrace]
  refine ⟨26522688816533167497147815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17681792544355444998098543 26522688816533167497147815)
  ·
    refine ⟨39784033224799751245721723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26522688816533167497147815 39784033224799751245721723)
    ·
      refine ⟨59676049837199626868582585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39784033224799751245721723 59676049837199626868582585)
      ·
        refine ⟨44757037377899720151436939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59676049837199626868582585 44757037377899720151436939)
        ·
          refine ⟨67135556066849580227155409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44757037377899720151436939 67135556066849580227155409)
          ·
            refine ⟨50351667050137185170366557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67135556066849580227155409 50351667050137185170366557)
            ·
              refine ⟨18881875143801444438887459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50351667050137185170366557 18881875143801444438887459)
              ·
                refine ⟨28322812715702166658331189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18881875143801444438887459 28322812715702166658331189)
                ·
                  refine ⟨2655263692097078124218549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28322812715702166658331189 2655263692097078124218549)
                  ·
                    refine ⟨248930971134101074145489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2655263692097078124218549 248930971134101074145489)
                    ·
                      rfl

theorem cell22_727187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_727187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727187 prefixEnd_727187 := by exact prefixLift 727187
  have htrace : WordTrace (prefixWord ++ tailWord_727187) baseStart_727187 baseEnd_727187 := by
    simpa [prefixWord, tailWord_727187, baseEnd_727187] using wordTrace_append hprefix tailTrace_727187
  have hstable : (prefixWord ++ tailWord_727187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727187).length < 2 ^ (prefixWord ++ tailWord_727187).sum := by decide
  have hdescent : baseEnd_727187 < baseStart_727187 := by decide
  rcases family_descends (prefixWord ++ tailWord_727187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727279 : List Nat := [1, 1, 2, 1, 6, 1, 1, 2, 7]
def baseStart_727279 : Nat := 118140960795 + 727279 * 2 ^ 59
def prefixEnd_727279 : Nat := 4983230072969 + 3 ^ 40 * 727279 * 2
def baseEnd_727279 : Nat := 82987488204747833615069

theorem tailTrace_727279 : CollatzResearch.WordTrace tailWord_727279 prefixEnd_727279 82987488204747833615069 := by
  unfold tailWord_727279
  simp only [CollatzResearch.WordTrace]
  refine ⟨26526044332199867209496891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17684029554799911472997927 26526044332199867209496891)
  ·
    refine ⟨39789066498299800814245337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26526044332199867209496891 39789066498299800814245337)
    ·
      refine ⟨29841799873724850610684003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39789066498299800814245337 29841799873724850610684003)
      ·
        refine ⟨44762699810587275916026005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29841799873724850610684003 44762699810587275916026005)
        ·
          refine ⟨2098251553621278558563719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44762699810587275916026005 2098251553621278558563719)
          ·
            refine ⟨3147377330431917837845579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098251553621278558563719 3147377330431917837845579)
            ·
              refine ⟨4721065995647876756768369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147377330431917837845579 4721065995647876756768369)
              ·
                refine ⟨3540799496735907567576277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4721065995647876756768369 3540799496735907567576277)
                ·
                  refine ⟨82987488204747833615069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3540799496735907567576277 82987488204747833615069)
                  ·
                    rfl

theorem cell22_727279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 7].length) (baseStart_727279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727279 prefixEnd_727279 := by exact prefixLift 727279
  have htrace : WordTrace (prefixWord ++ tailWord_727279) baseStart_727279 baseEnd_727279 := by
    simpa [prefixWord, tailWord_727279, baseEnd_727279] using wordTrace_append hprefix tailTrace_727279
  have hstable : (prefixWord ++ tailWord_727279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727279).length < 2 ^ (prefixWord ++ tailWord_727279).sum := by decide
  have hdescent : baseEnd_727279 < baseStart_727279 := by decide
  rcases family_descends (prefixWord ++ tailWord_727279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727300 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_727300 : Nat := 118140960795 + 727300 * 2 ^ 59
def prefixEnd_727300 : Nat := 4983230072969 + 3 ^ 40 * 727300 * 2
def baseEnd_727300 : Nat := 248969653343406446070143

theorem tailTrace_727300 : CollatzResearch.WordTrace tailWord_727300 prefixEnd_727300 248969653343406446070143 := by
  unfold tailWord_727300
  simp only [CollatzResearch.WordTrace]
  refine ⟨13263405132561893898005677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17684540176749191864007569 13263405132561893898005677)
  ·
    refine ⟨4973776924710710211752129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13263405132561893898005677 4973776924710710211752129)
    ·
      refine ⟨3730332693533032658814097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4973776924710710211752129 3730332693533032658814097)
      ·
        refine ⟨2797749520149774494110573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3730332693533032658814097 2797749520149774494110573)
        ·
          refine ⟨1049156070056165435291465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2797749520149774494110573 1049156070056165435291465)
          ·
            refine ⟨786867052542124076468599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1049156070056165435291465 786867052542124076468599)
            ·
              refine ⟨1180300578813186114702899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786867052542124076468599 1180300578813186114702899)
              ·
                refine ⟨1770450868219779172054349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180300578813186114702899 1770450868219779172054349)
                ·
                  refine ⟨663919075582417189520381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1770450868219779172054349 663919075582417189520381)
                  ·
                    refine ⟨248969653343406446070143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 663919075582417189520381 248969653343406446070143)
                    ·
                      rfl

theorem cell22_727300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_727300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727300 prefixEnd_727300 := by exact prefixLift 727300
  have htrace : WordTrace (prefixWord ++ tailWord_727300) baseStart_727300 baseEnd_727300 := by
    simpa [prefixWord, tailWord_727300, baseEnd_727300] using wordTrace_append hprefix tailTrace_727300
  have hstable : (prefixWord ++ tailWord_727300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727300).length < 2 ^ (prefixWord ++ tailWord_727300).sum := by decide
  have hdescent : baseEnd_727300 < baseStart_727300 := by decide
  rcases family_descends (prefixWord ++ tailWord_727300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727313 : List Nat := [1, 2, 2, 1, 1, 7, 2, 1, 5]
def baseStart_727313 : Nat := 118140960795 + 727313 * 2 ^ 59
def prefixEnd_727313 : Nat := 4983230072969 + 3 ^ 40 * 727313 * 2
def baseEnd_727313 : Nat := 82991367836359581831701

theorem tailTrace_727313 : CollatzResearch.WordTrace tailWord_727313 prefixEnd_727313 82991367836359581831701 := by
  unfold tailWord_727313
  simp only [CollatzResearch.WordTrace]
  refine ⟨26527284414076691016234593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17684856276051127344156395 26527284414076691016234593)
  ·
    refine ⟨19895463310557518262175945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26527284414076691016234593 19895463310557518262175945)
    ·
      refine ⟨14921597482918138696631959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19895463310557518262175945 14921597482918138696631959)
      ·
        refine ⟨22382396224377208044947939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14921597482918138696631959 22382396224377208044947939)
        ·
          refine ⟨33573594336565812067421909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22382396224377208044947939 33573594336565812067421909)
          ·
            refine ⟨786881117263261220330201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 33573594336565812067421909 786881117263261220330201)
            ·
              refine ⟨590160837947445915247651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786881117263261220330201 590160837947445915247651)
              ·
                refine ⟨885241256921168872871477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590160837947445915247651 885241256921168872871477)
                ·
                  refine ⟨82991367836359581831701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 885241256921168872871477 82991367836359581831701)
                  ·
                    rfl

theorem cell22_727313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 5].length) (baseStart_727313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727313 prefixEnd_727313 := by exact prefixLift 727313
  have htrace : WordTrace (prefixWord ++ tailWord_727313) baseStart_727313 baseEnd_727313 := by
    simpa [prefixWord, tailWord_727313, baseEnd_727313] using wordTrace_append hprefix tailTrace_727313
  have hstable : (prefixWord ++ tailWord_727313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727313).length < 2 ^ (prefixWord ++ tailWord_727313).sum := by decide
  have hdescent : baseEnd_727313 < baseStart_727313 := by decide
  rcases family_descends (prefixWord ++ tailWord_727313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727324 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 8]
def baseStart_727324 : Nat := 118140960795 + 727324 * 2 ^ 59
def prefixEnd_727324 : Nat := 4983230072969 + 3 ^ 40 * 727324 * 2
def baseEnd_727324 : Nat := 82992623011292794490023

theorem tailTrace_727324 : CollatzResearch.WordTrace tailWord_727324 prefixEnd_727324 82992623011292794490023 := by
  unfold tailWord_727324
  simp only [CollatzResearch.WordTrace]
  refine ⟨13263842808518419947442513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17685123744691226596590017 13263842808518419947442513)
  ·
    refine ⟨9947882106388814960581885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13263842808518419947442513 9947882106388814960581885)
    ·
      refine ⟨3730455789895805610218207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9947882106388814960581885 3730455789895805610218207)
      ·
        refine ⟨5595683684843708415327311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3730455789895805610218207 5595683684843708415327311)
        ·
          refine ⟨8393525527265562622990967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5595683684843708415327311 8393525527265562622990967)
          ·
            refine ⟨12590288290898343934486451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393525527265562622990967 12590288290898343934486451)
            ·
              refine ⟨18885432436347515901729677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12590288290898343934486451 18885432436347515901729677)
              ·
                refine ⟨7082037163630318463148629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18885432436347515901729677 7082037163630318463148629)
                ·
                  refine ⟨82992623011292794490023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7082037163630318463148629 82992623011292794490023)
                  ·
                    rfl

theorem cell22_727324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_727324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727324 prefixEnd_727324 := by exact prefixLift 727324
  have htrace : WordTrace (prefixWord ++ tailWord_727324) baseStart_727324 baseEnd_727324 := by
    simpa [prefixWord, tailWord_727324, baseEnd_727324] using wordTrace_append hprefix tailTrace_727324
  have hstable : (prefixWord ++ tailWord_727324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727324).length < 2 ^ (prefixWord ++ tailWord_727324).sum := by decide
  have hdescent : baseEnd_727324 < baseStart_727324 := by decide
  rcases family_descends (prefixWord ++ tailWord_727324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727384 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_727384 : Nat := 118140960795 + 727384 * 2 ^ 59
def prefixEnd_727384 : Nat := 4983230072969 + 3 ^ 40 * 727384 * 2
def baseEnd_727384 : Nat := 248998408260058226969885

theorem tailTrace_727384 : CollatzResearch.WordTrace tailWord_727384 prefixEnd_727384 248998408260058226969885 := by
  unfold tailWord_727384
  simp only [CollatzResearch.WordTrace]
  refine ⟨13264936998409735071034603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17686582664546313428046137 13264936998409735071034603)
  ·
    refine ⟨19897405497614602606551905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13264936998409735071034603 19897405497614602606551905)
    ·
      refine ⟨14923054123210951954913929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19897405497614602606551905 14923054123210951954913929)
      ·
        refine ⟨11192290592408213966185447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14923054123210951954913929 11192290592408213966185447)
        ·
          refine ⟨16788435888612320949278171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11192290592408213966185447 16788435888612320949278171)
          ·
            refine ⟨25182653832918481423917257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16788435888612320949278171 25182653832918481423917257)
            ·
              refine ⟨18886990374688861067937943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25182653832918481423917257 18886990374688861067937943)
              ·
                refine ⟨28330485562033291601906915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18886990374688861067937943 28330485562033291601906915)
                ·
                  refine ⟨42495728343049937402860373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28330485562033291601906915 42495728343049937402860373)
                  ·
                    refine ⟨248998408260058226969885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 42495728343049937402860373 248998408260058226969885)
                    ·
                      rfl

theorem cell22_727384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_727384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727384 prefixEnd_727384 := by exact prefixLift 727384
  have htrace : WordTrace (prefixWord ++ tailWord_727384) baseStart_727384 baseEnd_727384 := by
    simpa [prefixWord, tailWord_727384, baseEnd_727384] using wordTrace_append hprefix tailTrace_727384
  have hstable : (prefixWord ++ tailWord_727384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727384).length < 2 ^ (prefixWord ++ tailWord_727384).sum := by decide
  have hdescent : baseEnd_727384 < baseStart_727384 := by decide
  rcases family_descends (prefixWord ++ tailWord_727384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727401 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 5, 3]
def baseStart_727401 : Nat := 118140960795 + 727401 * 2 ^ 59
def prefixEnd_727401 : Nat := 4983230072969 + 3 ^ 40 * 727401 * 2
def baseEnd_727401 : Nat := 249004227707475849294833

theorem tailTrace_727401 : CollatzResearch.WordTrace tailWord_727401 prefixEnd_727401 249004227707475849294833 := by
  unfold tailWord_727401
  simp only [CollatzResearch.WordTrace]
  refine ⟨26530494037757882045438057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17686996025171921363625371 26530494037757882045438057)
  ·
    refine ⟨19897870528318411534078543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26530494037757882045438057 19897870528318411534078543)
    ·
      refine ⟨29846805792477617301117815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19897870528318411534078543 29846805792477617301117815)
      ·
        refine ⟨44770208688716425951676723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29846805792477617301117815 44770208688716425951676723)
        ·
          refine ⟨67155313033074638927515085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44770208688716425951676723 67155313033074638927515085)
          ·
            refine ⟨25183242387402989597818157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67155313033074638927515085 25183242387402989597818157)
            ·
              refine ⟨9443715895276121099181809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25183242387402989597818157 9443715895276121099181809)
              ·
                refine ⟨7082786921457090824386357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9443715895276121099181809 7082786921457090824386357)
                ·
                  refine ⟨664011273886602264786221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7082786921457090824386357 664011273886602264786221)
                  ·
                    refine ⟨249004227707475849294833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664011273886602264786221 249004227707475849294833)
                    ·
                      rfl

theorem cell22_727401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_727401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727401 prefixEnd_727401 := by exact prefixLift 727401
  have htrace : WordTrace (prefixWord ++ tailWord_727401) baseStart_727401 baseEnd_727401 := by
    simpa [prefixWord, tailWord_727401, baseEnd_727401] using wordTrace_append hprefix tailTrace_727401
  have hstable : (prefixWord ++ tailWord_727401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727401).length < 2 ^ (prefixWord ++ tailWord_727401).sum := by decide
  have hdescent : baseEnd_727401 < baseStart_727401 := by decide
  rcases family_descends (prefixWord ++ tailWord_727401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727469 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_727469 : Nat := 118140960795 + 727469 * 2 ^ 59
def prefixEnd_727469 : Nat := 4983230072969 + 3 ^ 40 * 727469 * 2
def baseEnd_727469 : Nat := 249027505497146338594625

theorem tailTrace_727469 : CollatzResearch.WordTrace tailWord_727469 prefixEnd_727469 249027505497146338594625 := by
  unfold tailWord_727469
  simp only [CollatzResearch.WordTrace]
  refine ⟨26532974201511529658913461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17688649467674353105942307 26532974201511529658913461)
  ·
    refine ⟨2487466331391705905523137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26532974201511529658913461 2487466331391705905523137)
    ·
      refine ⟨1865599748543779429142353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2487466331391705905523137 1865599748543779429142353)
      ·
        refine ⟨1399199811407834571856765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1865599748543779429142353 1399199811407834571856765)
        ·
          refine ⟨524699929277937964446287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1399199811407834571856765 524699929277937964446287)
          ·
            refine ⟨787049893916906946669431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524699929277937964446287 787049893916906946669431)
            ·
              refine ⟨1180574840875360420004147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787049893916906946669431 1180574840875360420004147)
              ·
                refine ⟨1770862261313040630006221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180574840875360420004147 1770862261313040630006221)
                ·
                  refine ⟨664073347992390236252333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1770862261313040630006221 664073347992390236252333)
                  ·
                    refine ⟨249027505497146338594625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664073347992390236252333 249027505497146338594625)
                    ·
                      rfl

theorem cell22_727469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_727469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727469 prefixEnd_727469 := by exact prefixLift 727469
  have htrace : WordTrace (prefixWord ++ tailWord_727469) baseStart_727469 baseEnd_727469 := by
    simpa [prefixWord, tailWord_727469, baseEnd_727469] using wordTrace_append hprefix tailTrace_727469
  have hstable : (prefixWord ++ tailWord_727469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727469).length < 2 ^ (prefixWord ++ tailWord_727469).sum := by decide
  have hdescent : baseEnd_727469 < baseStart_727469 := by decide
  rcases family_descends (prefixWord ++ tailWord_727469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727491 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 1, 5]
def baseStart_727491 : Nat := 118140960795 + 727491 * 2 ^ 59
def prefixEnd_727491 : Nat := 4983230072969 + 3 ^ 40 * 727491 * 2
def baseEnd_727491 : Nat := 249035036546745614544557

theorem tailTrace_727491 : CollatzResearch.WordTrace tailWord_727491 prefixEnd_727491 249035036546745614544557 := by
  unfold tailWord_727491
  simp only [CollatzResearch.WordTrace]
  refine ⟨26533776607431827416214327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17689184404954551610809551 26533776607431827416214327)
  ·
    refine ⟨39800664911147741124321491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26533776607431827416214327 39800664911147741124321491)
    ·
      refine ⟨59700997366721611686482237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39800664911147741124321491 59700997366721611686482237)
      ·
        refine ⟨22387874012520604382430839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59700997366721611686482237 22387874012520604382430839)
        ·
          refine ⟨33581811018780906573646259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22387874012520604382430839 33581811018780906573646259)
          ·
            refine ⟨50372716528171359860469389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33581811018780906573646259 50372716528171359860469389)
            ·
              refine ⟨18889768698064259947676021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50372716528171359860469389 18889768698064259947676021)
              ·
                refine ⟨1770915815443524370094627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18889768698064259947676021 1770915815443524370094627)
                ·
                  refine ⟨2656373723165286555141941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770915815443524370094627 2656373723165286555141941)
                  ·
                    refine ⟨249035036546745614544557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2656373723165286555141941 249035036546745614544557)
                    ·
                      rfl

theorem cell22_727491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 5].length) (baseStart_727491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727491 prefixEnd_727491 := by exact prefixLift 727491
  have htrace : WordTrace (prefixWord ++ tailWord_727491) baseStart_727491 baseEnd_727491 := by
    simpa [prefixWord, tailWord_727491, baseEnd_727491] using wordTrace_append hprefix tailTrace_727491
  have hstable : (prefixWord ++ tailWord_727491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727491).length < 2 ^ (prefixWord ++ tailWord_727491).sum := by decide
  have hdescent : baseEnd_727491 < baseStart_727491 := by decide
  rcases family_descends (prefixWord ++ tailWord_727491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727495 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 1, 4]
def baseStart_727495 : Nat := 118140960795 + 727495 * 2 ^ 59
def prefixEnd_727495 : Nat := 4983230072969 + 3 ^ 40 * 727495 * 2
def baseEnd_727495 : Nat := 249036405828490937444545

theorem tailTrace_727495 : CollatzResearch.WordTrace tailWord_727495 prefixEnd_727495 249036405828490937444545 := by
  unfold tailWord_727495
  simp only [CollatzResearch.WordTrace]
  refine ⟨26533922499417336099359939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17689281666278224066239959 26533922499417336099359939)
  ·
    refine ⟨39800883749126004149039909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26533922499417336099359939 39800883749126004149039909)
    ·
      refine ⟨7462665702961125777944983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39800883749126004149039909 7462665702961125777944983)
      ·
        refine ⟨11193998554441688666917475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7462665702961125777944983 11193998554441688666917475)
        ·
          refine ⟨16790997831662533000376213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11193998554441688666917475 16790997831662533000376213)
          ·
            refine ⟨787078023359181234392635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16790997831662533000376213 787078023359181234392635)
            ·
              refine ⟨1180617035038771851588953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787078023359181234392635 1180617035038771851588953)
              ·
                refine ⟨885462776279078888691715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180617035038771851588953 885462776279078888691715)
                ·
                  refine ⟨1328194164418618333037573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885462776279078888691715 1328194164418618333037573)
                  ·
                    refine ⟨249036405828490937444545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1328194164418618333037573 249036405828490937444545)
                    ·
                      rfl

theorem cell22_727495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_727495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727495 prefixEnd_727495 := by exact prefixLift 727495
  have htrace : WordTrace (prefixWord ++ tailWord_727495) baseStart_727495 baseEnd_727495 := by
    simpa [prefixWord, tailWord_727495, baseEnd_727495] using wordTrace_append hprefix tailTrace_727495
  have hstable : (prefixWord ++ tailWord_727495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727495).length < 2 ^ (prefixWord ++ tailWord_727495).sum := by decide
  have hdescent : baseEnd_727495 < baseStart_727495 := by decide
  rcases family_descends (prefixWord ++ tailWord_727495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727508 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_727508 : Nat := 118140960795 + 727508 * 2 ^ 59
def prefixEnd_727508 : Nat := 4983230072969 + 3 ^ 40 * 727508 * 2
def baseEnd_727508 : Nat := 249040855994163236869505

theorem tailTrace_727508 : CollatzResearch.WordTrace tailWord_727508 prefixEnd_727508 249040855994163236869505 := by
  unfold tailWord_727508
  simp only [CollatzResearch.WordTrace]
  refine ⟨13267198324185119659791589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17689597765580159546388785 13267198324185119659791589)
  ·
    refine ⟨2487599685784709936210923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13267198324185119659791589 2487599685784709936210923)
    ·
      refine ⟨3731399528677064904316385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2487599685784709936210923 3731399528677064904316385)
      ·
        refine ⟨2798549646507798678237289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3731399528677064904316385 2798549646507798678237289)
        ·
          refine ⟨2098912234880849008677967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2798549646507798678237289 2098912234880849008677967)
          ·
            refine ⟨3148368352321273513016951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098912234880849008677967 3148368352321273513016951)
            ·
              refine ⟨4722552528481910269525427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148368352321273513016951 4722552528481910269525427)
              ·
                refine ⟨7083828792722865404288141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4722552528481910269525427 7083828792722865404288141)
                ·
                  refine ⟨2656435797271074526608053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7083828792722865404288141 2656435797271074526608053)
                  ·
                    refine ⟨249040855994163236869505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2656435797271074526608053 249040855994163236869505)
                    ·
                      rfl

theorem cell22_727508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_727508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727508 prefixEnd_727508 := by exact prefixLift 727508
  have htrace : WordTrace (prefixWord ++ tailWord_727508) baseStart_727508 baseEnd_727508 := by
    simpa [prefixWord, tailWord_727508, baseEnd_727508] using wordTrace_append hprefix tailTrace_727508
  have hstable : (prefixWord ++ tailWord_727508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727508).length < 2 ^ (prefixWord ++ tailWord_727508).sum := by decide
  have hdescent : baseEnd_727508 < baseStart_727508 := by decide
  rcases family_descends (prefixWord ++ tailWord_727508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727551 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 2, 6]
def baseStart_727551 : Nat := 118140960795 + 727551 * 2 ^ 59
def prefixEnd_727551 : Nat := 4983230072969 + 3 ^ 40 * 727551 * 2
def baseEnd_727551 : Nat := 249055575772925458044373

theorem tailTrace_727551 : CollatzResearch.WordTrace tailWord_727551 prefixEnd_727551 249055575772925458044373 := by
  unfold tailWord_727551
  simp only [CollatzResearch.WordTrace]
  refine ⟨26535964987214457663398507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17690643324809638442265671 26535964987214457663398507)
  ·
    refine ⟨39803947480821686495097761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26535964987214457663398507 39803947480821686495097761)
    ·
      refine ⟨29852960610616264871323321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39803947480821686495097761 29852960610616264871323321)
      ·
        refine ⟨22389720457962198653492491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29852960610616264871323321 22389720457962198653492491)
        ·
          refine ⟨33584580686943297980238737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22389720457962198653492491 33584580686943297980238737)
          ·
            refine ⟨25188435515207473485179053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33584580686943297980238737 25188435515207473485179053)
            ·
              refine ⟨9445663318202802556942145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25188435515207473485179053 9445663318202802556942145)
              ·
                refine ⟨7084247488652101917706609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9445663318202802556942145 7084247488652101917706609)
                ·
                  refine ⟨5313185616489076438279957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7084247488652101917706609 5313185616489076438279957)
                  ·
                    refine ⟨249055575772925458044373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5313185616489076438279957 249055575772925458044373)
                    ·
                      rfl

theorem cell22_727551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_727551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727551 prefixEnd_727551 := by exact prefixLift 727551
  have htrace : WordTrace (prefixWord ++ tailWord_727551) baseStart_727551 baseEnd_727551 := by
    simpa [prefixWord, tailWord_727551, baseEnd_727551] using wordTrace_append hprefix tailTrace_727551
  have hstable : (prefixWord ++ tailWord_727551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727551).length < 2 ^ (prefixWord ++ tailWord_727551).sum := by decide
  have hdescent : baseEnd_727551 < baseStart_727551 := by decide
  rcases family_descends (prefixWord ++ tailWord_727551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727587 : List Nat := [1, 1, 1, 4, 4, 1, 2, 4, 1, 3]
def baseStart_727587 : Nat := 118140960795 + 727587 * 2 ^ 59
def prefixEnd_727587 : Nat := 4983230072969 + 3 ^ 40 * 727587 * 2
def baseEnd_727587 : Nat := 249067899308633364144263

theorem tailTrace_727587 : CollatzResearch.WordTrace tailWord_727587 prefixEnd_727587 249067899308633364144263 := by
  unfold tailWord_727587
  simp only [CollatzResearch.WordTrace]
  refine ⟨26537278015084035811709015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17691518676722690541139343 26537278015084035811709015)
  ·
    refine ⟨39805917022626053717563523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26537278015084035811709015 39805917022626053717563523)
    ·
      refine ⟨59708875533939080576345285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39805917022626053717563523 59708875533939080576345285)
      ·
        refine ⟨11195414162613577608064741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59708875533939080576345285 11195414162613577608064741)
        ·
          refine ⟨2099140155490045801512139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11195414162613577608064741 2099140155490045801512139)
          ·
            refine ⟨3148710233235068702268209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099140155490045801512139 3148710233235068702268209)
            ·
              refine ⟨2361532674926301526701157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148710233235068702268209 2361532674926301526701157)
              ·
                refine ⟨442787376548681536256467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2361532674926301526701157 442787376548681536256467)
                ·
                  refine ⟨664181064823022304384701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442787376548681536256467 664181064823022304384701)
                  ·
                    refine ⟨249067899308633364144263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664181064823022304384701 249067899308633364144263)
                    ·
                      rfl

theorem cell22_727587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 3].length) (baseStart_727587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727587 prefixEnd_727587 := by exact prefixLift 727587
  have htrace : WordTrace (prefixWord ++ tailWord_727587) baseStart_727587 baseEnd_727587 := by
    simpa [prefixWord, tailWord_727587, baseEnd_727587] using wordTrace_append hprefix tailTrace_727587
  have hstable : (prefixWord ++ tailWord_727587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727587).length < 2 ^ (prefixWord ++ tailWord_727587).sum := by decide
  have hdescent : baseEnd_727587 < baseStart_727587 := by decide
  rcases family_descends (prefixWord ++ tailWord_727587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727611 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 12]
def baseStart_727611 : Nat := 118140960795 + 727611 * 2 ^ 59
def prefixEnd_727611 : Nat := 4983230072969 + 3 ^ 40 * 727611 * 2
def baseEnd_727611 : Nat := 83025371666368433848063

theorem tailTrace_727611 : CollatzResearch.WordTrace tailWord_727611 prefixEnd_727611 83025371666368433848063 := by
  unfold tailWord_727611
  simp only [CollatzResearch.WordTrace]
  refine ⟨26538153366997087910582687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17692102244664725273721791 26538153366997087910582687)
  ·
    refine ⟨39807230050495631865874031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26538153366997087910582687 39807230050495631865874031)
    ·
      refine ⟨59710845075743447798811047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39807230050495631865874031 59710845075743447798811047)
      ·
        refine ⟨89566267613615171698216571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59710845075743447798811047 89566267613615171698216571)
        ·
          refine ⟨134349401420422757547324857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89566267613615171698216571 134349401420422757547324857)
          ·
            refine ⟨100762051065317068160493643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134349401420422757547324857 100762051065317068160493643)
            ·
              refine ⟨151143076597975602240740465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100762051065317068160493643 151143076597975602240740465)
              ·
                refine ⟨113357307448481701680555349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151143076597975602240740465 113357307448481701680555349)
                ·
                  refine ⟨83025371666368433848063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 113357307448481701680555349 83025371666368433848063)
                  ·
                    rfl

theorem cell22_727611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 12].length) (baseStart_727611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727611 prefixEnd_727611 := by exact prefixLift 727611
  have htrace : WordTrace (prefixWord ++ tailWord_727611) baseStart_727611 baseEnd_727611 := by
    simpa [prefixWord, tailWord_727611, baseEnd_727611] using wordTrace_append hprefix tailTrace_727611
  have hstable : (prefixWord ++ tailWord_727611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727611).length < 2 ^ (prefixWord ++ tailWord_727611).sum := by decide
  have hdescent : baseEnd_727611 < baseStart_727611 := by decide
  rcases family_descends (prefixWord ++ tailWord_727611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727630 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_727630 : Nat := 118140960795 + 727630 * 2 ^ 59
def prefixEnd_727630 : Nat := 4983230072969 + 3 ^ 40 * 727630 * 2
def baseEnd_727630 : Nat := 249082619087395585319131

theorem tailTrace_727630 : CollatzResearch.WordTrace tailWord_727630 prefixEnd_727630 249082619087395585319131 := by
  unfold tailWord_727630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317355794241031769440543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17692564235952169437016229 3317355794241031769440543)
  ·
    refine ⟨4976033691361547654160815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3317355794241031769440543 4976033691361547654160815)
    ·
      refine ⟨7464050537042321481241223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4976033691361547654160815 7464050537042321481241223)
      ·
        refine ⟨11196075805563482221861835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7464050537042321481241223 11196075805563482221861835)
        ·
          refine ⟨16794113708345223332792753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11196075805563482221861835 16794113708345223332792753)
          ·
            refine ⟨12595585281258917499594565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16794113708345223332792753 12595585281258917499594565)
            ·
              refine ⟨2361672240236047031173981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12595585281258917499594565 2361672240236047031173981)
              ·
                refine ⟨885627090088517636690243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2361672240236047031173981 885627090088517636690243)
                ·
                  refine ⟨1328440635132776455035365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885627090088517636690243 1328440635132776455035365)
                  ·
                    refine ⟨249082619087395585319131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1328440635132776455035365 249082619087395585319131)
                    ·
                      rfl

theorem cell22_727630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_727630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727630 prefixEnd_727630 := by exact prefixLift 727630
  have htrace : WordTrace (prefixWord ++ tailWord_727630) baseStart_727630 baseEnd_727630 := by
    simpa [prefixWord, tailWord_727630, baseEnd_727630] using wordTrace_append hprefix tailTrace_727630
  have hstable : (prefixWord ++ tailWord_727630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727630).length < 2 ^ (prefixWord ++ tailWord_727630).sum := by decide
  have hdescent : baseEnd_727630 < baseStart_727630 := by decide
  rcases family_descends (prefixWord ++ tailWord_727630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727664 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 1, 4]
def baseStart_727664 : Nat := 118140960795 + 727664 * 2 ^ 59
def prefixEnd_727664 : Nat := 4983230072969 + 3 ^ 40 * 727664 * 2
def baseEnd_727664 : Nat := 249094257982230829969027

theorem tailTrace_727664 : CollatzResearch.WordTrace tailWord_727664 prefixEnd_727664 249094257982230829969027 := by
  unfold tailWord_727664
  simp only [CollatzResearch.WordTrace]
  refine ⟨13270043217902538981131023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17693390957203385308174697 13270043217902538981131023)
  ·
    refine ⟨19905064826853808471696535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13270043217902538981131023 19905064826853808471696535)
    ·
      refine ⟨29857597240280712707544803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19905064826853808471696535 29857597240280712707544803)
      ·
        refine ⟨44786395860421069061317205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29857597240280712707544803 44786395860421069061317205)
        ·
          refine ⟨524840576489309403062311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 44786395860421069061317205 524840576489309403062311)
          ·
            refine ⟨787260864733964104593467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524840576489309403062311 787260864733964104593467)
            ·
              refine ⟨1180891297100946156890201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787260864733964104593467 1180891297100946156890201)
              ·
                refine ⟨885668472825709617667651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180891297100946156890201 885668472825709617667651)
                ·
                  refine ⟨1328502709238564426501477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885668472825709617667651 1328502709238564426501477)
                  ·
                    refine ⟨249094257982230829969027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1328502709238564426501477 249094257982230829969027)
                    ·
                      rfl

theorem cell22_727664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 4].length) (baseStart_727664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727664 prefixEnd_727664 := by exact prefixLift 727664
  have htrace : WordTrace (prefixWord ++ tailWord_727664) baseStart_727664 baseEnd_727664 := by
    simpa [prefixWord, tailWord_727664, baseEnd_727664] using wordTrace_append hprefix tailTrace_727664
  have hstable : (prefixWord ++ tailWord_727664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727664).length < 2 ^ (prefixWord ++ tailWord_727664).sum := by decide
  have hdescent : baseEnd_727664 < baseStart_727664 := by decide
  rcases family_descends (prefixWord ++ tailWord_727664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727673 : List Nat := [1, 2, 1, 3, 3, 2, 2, 8]
def baseStart_727673 : Nat := 118140960795 + 727673 * 2 ^ 59
def prefixEnd_727673 : Nat := 4983230072969 + 3 ^ 40 * 727673 * 2
def baseEnd_727673 : Nat := 27677482096239756277111

theorem tailTrace_727673 : CollatzResearch.WordTrace tailWord_727673 prefixEnd_727673 27677482096239756277111 := by
  unfold tailWord_727673
  simp only [CollatzResearch.WordTrace]
  refine ⟨26540414692772472499339673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17693609795181648332893115 26540414692772472499339673)
  ·
    refine ⟨19905311019579354374504755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26540414692772472499339673 19905311019579354374504755)
    ·
      refine ⟨29857966529369031561757133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19905311019579354374504755 29857966529369031561757133)
      ·
        refine ⟨11196737448513386835658925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29857966529369031561757133 11196737448513386835658925)
        ·
          refine ⟨4198776543192520063372097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11196737448513386835658925 4198776543192520063372097)
          ·
            refine ⟨3149082407394390047529073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4198776543192520063372097 3149082407394390047529073)
            ·
              refine ⟨2361811805545792535646805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3149082407394390047529073 2361811805545792535646805)
              ·
                refine ⟨27677482096239756277111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2361811805545792535646805 27677482096239756277111)
                ·
                  rfl

theorem cell22_727673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 8].length) (baseStart_727673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727673 prefixEnd_727673 := by exact prefixLift 727673
  have htrace : WordTrace (prefixWord ++ tailWord_727673) baseStart_727673 baseEnd_727673 := by
    simpa [prefixWord, tailWord_727673, baseEnd_727673] using wordTrace_append hprefix tailTrace_727673
  have hstable : (prefixWord ++ tailWord_727673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727673).length < 2 ^ (prefixWord ++ tailWord_727673).sum := by decide
  have hdescent : baseEnd_727673 < baseStart_727673 := by decide
  rcases family_descends (prefixWord ++ tailWord_727673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727690 : List Nat := [3, 1, 2, 3, 4, 9]
def baseStart_727690 : Nat := 118140960795 + 727690 * 2 ^ 59
def prefixEnd_727690 : Nat := 4983230072969 + 3 ^ 40 * 727690 * 2
def baseEnd_727690 : Nat := 3075347633500931219987

theorem tailTrace_727690 : CollatzResearch.WordTrace tailWord_727690 prefixEnd_727690 3075347633500931219987 := by
  unfold tailWord_727690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6635258683427721100677131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17694023155807256268472349 6635258683427721100677131)
  ·
    refine ⟨9952888025141581651015697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6635258683427721100677131 9952888025141581651015697)
    ·
      refine ⟨7464666018856186238261773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9952888025141581651015697 7464666018856186238261773)
      ·
        refine ⟨2799249757071069839348165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7464666018856186238261773 2799249757071069839348165)
        ·
          refine ⟨524859329450825594877781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2799249757071069839348165 524859329450825594877781)
          ·
            refine ⟨3075347633500931219987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 524859329450825594877781 3075347633500931219987)
            ·
              rfl

theorem cell22_727690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 9].length) (baseStart_727690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727690 prefixEnd_727690 := by exact prefixLift 727690
  have htrace : WordTrace (prefixWord ++ tailWord_727690) baseStart_727690 baseEnd_727690 := by
    simpa [prefixWord, tailWord_727690, baseEnd_727690] using wordTrace_append hprefix tailTrace_727690
  have hstable : (prefixWord ++ tailWord_727690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727690).length < 2 ^ (prefixWord ++ tailWord_727690).sum := by decide
  have hdescent : baseEnd_727690 < baseStart_727690 := by decide
  rcases family_descends (prefixWord ++ tailWord_727690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727703 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 1, 8]
def baseStart_727703 : Nat := 118140960795 + 727703 * 2 ^ 59
def prefixEnd_727703 : Nat := 4983230072969 + 3 ^ 40 * 727703 * 2
def baseEnd_727703 : Nat := 249107608479247728243907

theorem tailTrace_727703 : CollatzResearch.WordTrace tailWord_727703 prefixEnd_727703 249107608479247728243907 := by
  unfold tailWord_727703
  simp only [CollatzResearch.WordTrace]
  refine ⟨26541508882663787622931763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17694339255109191748621175 26541508882663787622931763)
  ·
    refine ⟨39812263323995681434397645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26541508882663787622931763 39812263323995681434397645)
    ·
      refine ⟨14929598746498380537899117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39812263323995681434397645 14929598746498380537899117)
      ·
        refine ⟨5598599529936892701712169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14929598746498380537899117 5598599529936892701712169)
        ·
          refine ⟨4198949647452669526284127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5598599529936892701712169 4198949647452669526284127)
          ·
            refine ⟨6298424471179004289426191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198949647452669526284127 6298424471179004289426191)
            ·
              refine ⟨9447636706768506434139287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298424471179004289426191 9447636706768506434139287)
              ·
                refine ⟨14171455060152759651208931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9447636706768506434139287 14171455060152759651208931)
                ·
                  refine ⟨21257182590229139476813397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14171455060152759651208931 21257182590229139476813397)
                  ·
                    refine ⟨249107608479247728243907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21257182590229139476813397 249107608479247728243907)
                    ·
                      rfl

theorem cell22_727703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_727703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727703 prefixEnd_727703 := by exact prefixLift 727703
  have htrace : WordTrace (prefixWord ++ tailWord_727703) baseStart_727703 baseEnd_727703 := by
    simpa [prefixWord, tailWord_727703, baseEnd_727703] using wordTrace_append hprefix tailTrace_727703
  have hstable : (prefixWord ++ tailWord_727703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727703).length < 2 ^ (prefixWord ++ tailWord_727703).sum := by decide
  have hdescent : baseEnd_727703 < baseStart_727703 := by decide
  rcases family_descends (prefixWord ++ tailWord_727703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727705 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 3, 3]
def baseStart_727705 : Nat := 118140960795 + 727705 * 2 ^ 59
def prefixEnd_727705 : Nat := 4983230072969 + 3 ^ 40 * 727705 * 2
def baseEnd_727705 : Nat := 249108293120120389693901

theorem tailTrace_727705 : CollatzResearch.WordTrace tailWord_727705 prefixEnd_727705 249108293120120389693901 := by
  unfold tailWord_727705
  simp only [CollatzResearch.WordTrace]
  refine ⟨26541581828656541964504569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17694387885771027976336379 26541581828656541964504569)
  ·
    refine ⟨19906186371492406473378427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26541581828656541964504569 19906186371492406473378427)
    ·
      refine ⟨29859279557238609710067641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19906186371492406473378427 29859279557238609710067641)
      ·
        refine ⟨22394459667928957282550731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29859279557238609710067641 22394459667928957282550731)
        ·
          refine ⟨33591689501893435923826097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22394459667928957282550731 33591689501893435923826097)
          ·
            refine ⟨25193767126420076942869573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33591689501893435923826097 25193767126420076942869573)
            ·
              refine ⟨4723831336203764426788045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25193767126420076942869573 4723831336203764426788045)
              ·
                refine ⟨1771436751076411660045517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4723831336203764426788045 1771436751076411660045517)
                ·
                  refine ⟨664288781653654372517069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1771436751076411660045517 664288781653654372517069)
                  ·
                    refine ⟨249108293120120389693901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664288781653654372517069 249108293120120389693901)
                    ·
                      rfl

theorem cell22_727705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 3].length) (baseStart_727705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727705 prefixEnd_727705 := by exact prefixLift 727705
  have htrace : WordTrace (prefixWord ++ tailWord_727705) baseStart_727705 baseEnd_727705 := by
    simpa [prefixWord, tailWord_727705, baseEnd_727705] using wordTrace_append hprefix tailTrace_727705
  have hstable : (prefixWord ++ tailWord_727705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727705).length < 2 ^ (prefixWord ++ tailWord_727705).sum := by decide
  have hdescent : baseEnd_727705 < baseStart_727705 := by decide
  rcases family_descends (prefixWord ++ tailWord_727705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727752 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 5]
def baseStart_727752 : Nat := 118140960795 + 727752 * 2 ^ 59
def prefixEnd_727752 : Nat := 4983230072969 + 3 ^ 40 * 727752 * 2
def baseEnd_727752 : Nat := 83041460726875977922919

theorem tailTrace_727752 : CollatzResearch.WordTrace tailWord_727752 prefixEnd_727752 83041460726875977922919 := by
  unfold tailWord_727752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13271648029743134495732755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17695530706324179327643673 13271648029743134495732755)
  ·
    refine ⟨19907472044614701743599133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13271648029743134495732755 19907472044614701743599133)
    ·
      refine ⟨7465302016730513153849675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19907472044614701743599133 7465302016730513153849675)
      ·
        refine ⟨11197953025095769730774513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465302016730513153849675 11197953025095769730774513)
        ·
          refine ⟨8398464768821827298080885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11197953025095769730774513 8398464768821827298080885)
          ·
            refine ⟨787356072077046309195083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8398464768821827298080885 787356072077046309195083)
            ·
              refine ⟨1181034108115569463792625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787356072077046309195083 1181034108115569463792625)
              ·
                refine ⟨885775581086677097844469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181034108115569463792625 885775581086677097844469)
                ·
                  refine ⟨83041460726875977922919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 885775581086677097844469 83041460726875977922919)
                  ·
                    rfl

theorem cell22_727752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_727752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_727752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_727752 prefixEnd_727752 := by exact prefixLift 727752
  have htrace : WordTrace (prefixWord ++ tailWord_727752) baseStart_727752 baseEnd_727752 := by
    simpa [prefixWord, tailWord_727752, baseEnd_727752] using wordTrace_append hprefix tailTrace_727752
  have hstable : (prefixWord ++ tailWord_727752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727752).length < 2 ^ (prefixWord ++ tailWord_727752).sum := by decide
  have hdescent : baseEnd_727752 < baseStart_727752 := by decide
  rcases family_descends (prefixWord ++ tailWord_727752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
