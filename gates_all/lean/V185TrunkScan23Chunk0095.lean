import V185TrunkScan23Chunk0094

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_563733 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_563733 : Nat := 118140960795 + 563733 * 2 ^ 59
def prefixEnd_563733 : Nat := 4983230072969 + 3 ^ 40 * 563733 * 2
def baseEnd_563733 : Nat := 96488663267049375248315

theorem tailTrace_563733 : CollatzResearch.WordTrace tailWord_563733 prefixEnd_563733 96488663267049375248315 := by
  unfold tailWord_563733
  simp only [CollatzResearch.WordTrace]
  refine ⟨20561031666699093776431853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13707354444466062517621235 20561031666699093776431853)
  ·
    refine ⟨7710386875012160166161945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20561031666699093776431853 7710386875012160166161945)
    ·
      refine ⟨5782790156259120124621459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7710386875012160166161945 5782790156259120124621459)
      ·
        refine ⟨8674185234388680186932189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5782790156259120124621459 8674185234388680186932189)
        ·
          refine ⟨3252819462895755070099571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8674185234388680186932189 3252819462895755070099571)
          ·
            refine ⟨4879229194343632605149357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252819462895755070099571 4879229194343632605149357)
            ·
              refine ⟨1829710947878862226931009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4879229194343632605149357 1829710947878862226931009)
              ·
                refine ⟨1372283210909146670198257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829710947878862226931009 1372283210909146670198257)
                ·
                  refine ⟨1029212408181860002648693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372283210909146670198257 1029212408181860002648693)
                  ·
                    refine ⟨96488663267049375248315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1029212408181860002648693 96488663267049375248315)
                    ·
                      rfl

theorem cell23_563733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_563733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563733 prefixEnd_563733 := by exact prefixLift 563733
  have htrace : WordTrace (prefixWord ++ tailWord_563733) baseStart_563733 baseEnd_563733 := by
    simpa [prefixWord, tailWord_563733, baseEnd_563733] using wordTrace_append hprefix tailTrace_563733
  have hstable : (prefixWord ++ tailWord_563733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563733).length < 2 ^ (prefixWord ++ tailWord_563733).sum := by decide
  have hdescent : baseEnd_563733 < baseStart_563733 := by decide
  rcases family_descends (prefixWord ++ tailWord_563733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563748 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_563748 : Nat := 118140960795 + 563748 * 2 ^ 59
def prefixEnd_563748 : Nat := 4983230072969 + 3 ^ 40 * 563748 * 2
def baseEnd_563748 : Nat := 289473692010965567057377

theorem tailTrace_563748 : CollatzResearch.WordTrace tailWord_563748 prefixEnd_563748 289473692010965567057377 := by
  unfold tailWord_563748
  simp only [CollatzResearch.WordTrace]
  refine ⟨10280789380822375669113949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13707719174429834225485265 10280789380822375669113949)
  ·
    refine ⟨3855296017808390875917731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10280789380822375669113949 3855296017808390875917731)
    ·
      refine ⟨5782944026712586313876597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3855296017808390875917731 5782944026712586313876597)
      ·
        refine ⟨542151002504304966925931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5782944026712586313876597 542151002504304966925931)
        ·
          refine ⟨813226503756457450388897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542151002504304966925931 813226503756457450388897)
          ·
            refine ⟨609919877817343087791673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 813226503756457450388897 609919877817343087791673)
            ·
              refine ⟨457439908363007315843755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 609919877817343087791673 457439908363007315843755)
              ·
                refine ⟨686159862544510973765633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457439908363007315843755 686159862544510973765633)
                ·
                  refine ⟨514619896908383230324225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 686159862544510973765633 514619896908383230324225)
                  ·
                    refine ⟨385964922681287422743169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 514619896908383230324225 385964922681287422743169)
                    ·
                      refine ⟨289473692010965567057377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 385964922681287422743169 289473692010965567057377)
                      ·
                        rfl

theorem cell23_563748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_563748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563748 prefixEnd_563748 := by exact prefixLift 563748
  have htrace : WordTrace (prefixWord ++ tailWord_563748) baseStart_563748 baseEnd_563748 := by
    simpa [prefixWord, tailWord_563748, baseEnd_563748] using wordTrace_append hprefix tailTrace_563748
  have hstable : (prefixWord ++ tailWord_563748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563748).length < 2 ^ (prefixWord ++ tailWord_563748).sum := by decide
  have hdescent : baseEnd_563748 < baseStart_563748 := by decide
  rcases family_descends (prefixWord ++ tailWord_563748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563756 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_563756 : Nat := 118140960795 + 563756 * 2 ^ 59
def prefixEnd_563756 : Nat := 4983230072969 + 3 ^ 40 * 563756 * 2
def baseEnd_563756 : Nat := 289477799856201535757339

theorem tailTrace_563756 : CollatzResearch.WordTrace tailWord_563756 prefixEnd_563756 289477799856201535757339 := by
  unfold tailWord_563756
  simp only [CollatzResearch.WordTrace]
  refine ⟨10280935272807884352259561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13707913697077179136346081 10280935272807884352259561)
  ·
    refine ⟨7710701454605913264194671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10280935272807884352259561 7710701454605913264194671)
    ·
      refine ⟨11566052181908869896292007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7710701454605913264194671 11566052181908869896292007)
      ·
        refine ⟨17349078272863304844438011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11566052181908869896292007 17349078272863304844438011)
        ·
          refine ⟨26023617409294957266657017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17349078272863304844438011 26023617409294957266657017)
          ·
            refine ⟨19517713056971217949992763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26023617409294957266657017 19517713056971217949992763)
            ·
              refine ⟨29276569585456826924989145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19517713056971217949992763 29276569585456826924989145)
              ·
                refine ⟨21957427189092620193741859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29276569585456826924989145 21957427189092620193741859)
                ·
                  refine ⟨32936140783638930290612789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21957427189092620193741859 32936140783638930290612789)
                  ·
                    refine ⟨3087763198466149714744949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32936140783638930290612789 3087763198466149714744949)
                    ·
                      refine ⟨289477799856201535757339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3087763198466149714744949 289477799856201535757339)
                      ·
                        rfl

theorem cell23_563756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_563756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563756 prefixEnd_563756 := by exact prefixLift 563756
  have htrace : WordTrace (prefixWord ++ tailWord_563756) baseStart_563756 baseEnd_563756 := by
    simpa [prefixWord, tailWord_563756, baseEnd_563756] using wordTrace_append hprefix tailTrace_563756
  have hstable : (prefixWord ++ tailWord_563756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563756).length < 2 ^ (prefixWord ++ tailWord_563756).sum := by decide
  have hdescent : baseEnd_563756 < baseStart_563756 := by decide
  rcases family_descends (prefixWord ++ tailWord_563756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563763 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 5, 4]
def baseStart_563763 : Nat := 118140960795 + 563763 * 2 ^ 59
def prefixEnd_563763 : Nat := 4983230072969 + 3 ^ 40 * 563763 * 2
def baseEnd_563763 : Nat := 96493798073594336123269

theorem tailTrace_563763 : CollatzResearch.WordTrace tailWord_563763 prefixEnd_563763 96493798073594336123269 := by
  unfold tailWord_563763
  simp only [CollatzResearch.WordTrace]
  refine ⟨20562125856590408900023943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13708083904393605933349295 20562125856590408900023943)
  ·
    refine ⟨30843188784885613350035915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20562125856590408900023943 30843188784885613350035915)
    ·
      refine ⟨46264783177328420025053873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30843188784885613350035915 46264783177328420025053873)
      ·
        refine ⟨34698587382996315018790405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46264783177328420025053873 34698587382996315018790405)
        ·
          refine ⟨6505985134311809066023201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34698587382996315018790405 6505985134311809066023201)
          ·
            refine ⟨4879488850733856799517401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6505985134311809066023201 4879488850733856799517401)
            ·
              refine ⟨3659616638050392599638051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4879488850733856799517401 3659616638050392599638051)
              ·
                refine ⟨5489424957075588899457077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659616638050392599638051 5489424957075588899457077)
                ·
                  refine ⟨514633589725836459324101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5489424957075588899457077 514633589725836459324101)
                  ·
                    refine ⟨96493798073594336123269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 514633589725836459324101 96493798073594336123269)
                    ·
                      rfl

theorem cell23_563763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 5, 4].length) (baseStart_563763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563763 prefixEnd_563763 := by exact prefixLift 563763
  have htrace : WordTrace (prefixWord ++ tailWord_563763) baseStart_563763 baseEnd_563763 := by
    simpa [prefixWord, tailWord_563763, baseEnd_563763] using wordTrace_append hprefix tailTrace_563763
  have hstable : (prefixWord ++ tailWord_563763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563763).length < 2 ^ (prefixWord ++ tailWord_563763).sum := by decide
  have hdescent : baseEnd_563763 < baseStart_563763 := by decide
  rcases family_descends (prefixWord ++ tailWord_563763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563770 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_563770 : Nat := 118140960795 + 563770 * 2 ^ 59
def prefixEnd_563770 : Nat := 4983230072969 + 3 ^ 40 * 563770 * 2
def baseEnd_563770 : Nat := 289484988585364480982275

theorem tailTrace_563770 : CollatzResearch.WordTrace tailWord_563770 prefixEnd_563770 289484988585364480982275 := by
  unfold tailWord_563770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5140595291891262273882191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13708254111710032730352509 5140595291891262273882191)
  ·
    refine ⟨7710892937836893410823287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5140595291891262273882191 7710892937836893410823287)
    ·
      refine ⟨11566339406755340116234931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7710892937836893410823287 11566339406755340116234931)
      ·
        refine ⟨17349509110133010174352397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11566339406755340116234931 17349509110133010174352397)
        ·
          refine ⟨6506065916299878815382149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17349509110133010174352397 6506065916299878815382149)
          ·
            refine ⟨1219887359306227277884153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6506065916299878815382149 1219887359306227277884153)
            ·
              refine ⟨914915519479670458413115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1219887359306227277884153 914915519479670458413115)
              ·
                refine ⟨1372373279219505687619673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 914915519479670458413115 1372373279219505687619673)
                ·
                  refine ⟨1029279959414629265714755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372373279219505687619673 1029279959414629265714755)
                  ·
                    refine ⟨1543919939121943898572133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1029279959414629265714755 1543919939121943898572133)
                    ·
                      refine ⟨289484988585364480982275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1543919939121943898572133 289484988585364480982275)
                      ·
                        rfl

theorem cell23_563770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_563770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563770 prefixEnd_563770 := by exact prefixLift 563770
  have htrace : WordTrace (prefixWord ++ tailWord_563770) baseStart_563770 baseEnd_563770 := by
    simpa [prefixWord, tailWord_563770, baseEnd_563770] using wordTrace_append hprefix tailTrace_563770
  have hstable : (prefixWord ++ tailWord_563770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563770).length < 2 ^ (prefixWord ++ tailWord_563770).sum := by decide
  have hdescent : baseEnd_563770 < baseStart_563770 := by decide
  rcases family_descends (prefixWord ++ tailWord_563770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563776 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 10]
def baseStart_563776 : Nat := 118140960795 + 563776 * 2 ^ 59
def prefixEnd_563776 : Nat := 4983230072969 + 3 ^ 40 * 563776 * 2
def baseEnd_563776 : Nat := 32165341052143495278583

theorem tailTrace_563776 : CollatzResearch.WordTrace tailWord_563776 prefixEnd_563776 32165341052143495278583 := by
  unfold tailWord_563776
  simp only [CollatzResearch.WordTrace]
  refine ⟨10281300002771656060123591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13708400003695541413498121 10281300002771656060123591)
  ·
    refine ⟨15421950004157484090185387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10281300002771656060123591 15421950004157484090185387)
    ·
      refine ⟨23132925006236226135278081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15421950004157484090185387 23132925006236226135278081)
      ·
        refine ⟨17349693754677169601458561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23132925006236226135278081 17349693754677169601458561)
        ·
          refine ⟨13012270316007877201093921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17349693754677169601458561 13012270316007877201093921)
          ·
            refine ⟨9759202737005907900820441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13012270316007877201093921 9759202737005907900820441)
            ·
              refine ⟨7319402052754430925615331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9759202737005907900820441 7319402052754430925615331)
              ·
                refine ⟨10979103079131646388422997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7319402052754430925615331 10979103079131646388422997)
                ·
                  refine ⟨32165341052143495278583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 10979103079131646388422997 32165341052143495278583)
                  ·
                    rfl

theorem cell23_563776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 10].length) (baseStart_563776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563776 prefixEnd_563776 := by exact prefixLift 563776
  have htrace : WordTrace (prefixWord ++ tailWord_563776) baseStart_563776 baseEnd_563776 := by
    simpa [prefixWord, tailWord_563776, baseEnd_563776] using wordTrace_append hprefix tailTrace_563776
  have hstable : (prefixWord ++ tailWord_563776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563776).length < 2 ^ (prefixWord ++ tailWord_563776).sum := by decide
  have hdescent : baseEnd_563776 < baseStart_563776 := by decide
  rcases family_descends (prefixWord ++ tailWord_563776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563790 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_563790 : Nat := 118140960795 + 563790 * 2 ^ 59
def prefixEnd_563790 : Nat := 4983230072969 + 3 ^ 40 * 563790 * 2
def baseEnd_563790 : Nat := 289495258198454402732183

theorem tailTrace_563790 : CollatzResearch.WordTrace tailWord_563790 prefixEnd_563790 289495258198454402732183 := by
  unfold tailWord_563790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2570388828436574063907103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13708740418328395007504549 2570388828436574063907103)
  ·
    refine ⟨3855583242654861095860655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2570388828436574063907103 3855583242654861095860655)
    ·
      refine ⟨5783374863982291643790983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3855583242654861095860655 5783374863982291643790983)
      ·
        refine ⟨8675062295973437465686475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5783374863982291643790983 8675062295973437465686475)
        ·
          refine ⟨13012593443960156198529713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8675062295973437465686475 13012593443960156198529713)
          ·
            refine ⟨9759445082970117148897285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13012593443960156198529713 9759445082970117148897285)
            ·
              refine ⟨1829895953056896965418241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9759445082970117148897285 1829895953056896965418241)
              ·
                refine ⟨1372421964792672724063681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829895953056896965418241 1372421964792672724063681)
                ·
                  refine ⟨1029316473594504543047761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372421964792672724063681 1029316473594504543047761)
                  ·
                    refine ⟨771987355195878407285821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1029316473594504543047761 771987355195878407285821)
                    ·
                      refine ⟨289495258198454402732183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 771987355195878407285821 289495258198454402732183)
                      ·
                        rfl

theorem cell23_563790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_563790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563790 prefixEnd_563790 := by exact prefixLift 563790
  have htrace : WordTrace (prefixWord ++ tailWord_563790) baseStart_563790 baseEnd_563790 := by
    simpa [prefixWord, tailWord_563790, baseEnd_563790] using wordTrace_append hprefix tailTrace_563790
  have hstable : (prefixWord ++ tailWord_563790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563790).length < 2 ^ (prefixWord ++ tailWord_563790).sum := by decide
  have hdescent : baseEnd_563790 < baseStart_563790 := by decide
  rcases family_descends (prefixWord ++ tailWord_563790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563793 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 6]
def baseStart_563793 : Nat := 118140960795 + 563793 * 2 ^ 59
def prefixEnd_563793 : Nat := 4983230072969 + 3 ^ 40 * 563793 * 2
def baseEnd_563793 : Nat := 32166310960046432332741

theorem tailTrace_563793 : CollatzResearch.WordTrace tailWord_563793 prefixEnd_563793 32166310960046432332741 := by
  unfold tailWord_563793
  simp only [CollatzResearch.WordTrace]
  refine ⟨20563220046481724023616033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13708813364321149349077355 20563220046481724023616033)
  ·
    refine ⟨15422415034861293017712025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20563220046481724023616033 15422415034861293017712025)
    ·
      refine ⟨11566811276145969763284019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15422415034861293017712025 11566811276145969763284019)
      ·
        refine ⟨17350216914218954644926029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11566811276145969763284019 17350216914218954644926029)
        ·
          refine ⟨6506331342832107991847261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17350216914218954644926029 6506331342832107991847261)
          ·
            refine ⟨2439874253562040496942723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6506331342832107991847261 2439874253562040496942723)
            ·
              refine ⟨3659811380343060745414085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2439874253562040496942723 3659811380343060745414085)
              ·
                refine ⟨686214633814323889765141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3659811380343060745414085 686214633814323889765141)
                ·
                  refine ⟨32166310960046432332741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 686214633814323889765141 32166310960046432332741)
                  ·
                    rfl

theorem cell23_563793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 6].length) (baseStart_563793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563793 prefixEnd_563793 := by exact prefixLift 563793
  have htrace : WordTrace (prefixWord ++ tailWord_563793) baseStart_563793 baseEnd_563793 := by
    simpa [prefixWord, tailWord_563793, baseEnd_563793] using wordTrace_append hprefix tailTrace_563793
  have hstable : (prefixWord ++ tailWord_563793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563793).length < 2 ^ (prefixWord ++ tailWord_563793).sum := by decide
  have hdescent : baseEnd_563793 < baseStart_563793 := by decide
  rcases family_descends (prefixWord ++ tailWord_563793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563820 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 3]
def baseStart_563820 : Nat := 118140960795 + 563820 * 2 ^ 59
def prefixEnd_563820 : Nat := 4983230072969 + 3 ^ 40 * 563820 * 2
def baseEnd_563820 : Nat := 289510662618089285357045

theorem tailTrace_563820 : CollatzResearch.WordTrace tailWord_563820 prefixEnd_563820 289510662618089285357045 := by
  unfold tailWord_563820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10282102408691953817424457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13709469878255938423232609 10282102408691953817424457)
  ·
    refine ⟨7711576806518965363068343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10282102408691953817424457 7711576806518965363068343)
    ·
      refine ⟨11567365209778448044602515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7711576806518965363068343 11567365209778448044602515)
      ·
        refine ⟨17351047814667672066903773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11567365209778448044602515 17351047814667672066903773)
        ·
          refine ⟨6506642930500377025088915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17351047814667672066903773 6506642930500377025088915)
          ·
            refine ⟨9759964395750565537633373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6506642930500377025088915 9759964395750565537633373)
            ·
              refine ⟨3659986648406462076612515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9759964395750565537633373 3659986648406462076612515)
              ·
                refine ⟨5489979972609693114918773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659986648406462076612515 5489979972609693114918773)
                ·
                  refine ⟨514685622432158729523635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5489979972609693114918773 514685622432158729523635)
                  ·
                    refine ⟨772028433648238094285453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 514685622432158729523635 772028433648238094285453)
                    ·
                      refine ⟨289510662618089285357045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 772028433648238094285453 289510662618089285357045)
                      ·
                        rfl

theorem cell23_563820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_563820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563820 prefixEnd_563820 := by exact prefixLift 563820
  have htrace : WordTrace (prefixWord ++ tailWord_563820) baseStart_563820 baseEnd_563820 := by
    simpa [prefixWord, tailWord_563820, baseEnd_563820] using wordTrace_append hprefix tailTrace_563820
  have hstable : (prefixWord ++ tailWord_563820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563820).length < 2 ^ (prefixWord ++ tailWord_563820).sum := by decide
  have hdescent : baseEnd_563820 < baseStart_563820 := by decide
  rcases family_descends (prefixWord ++ tailWord_563820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563823 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 3, 5]
def baseStart_563823 : Nat := 118140960795 + 563823 * 2 ^ 59
def prefixEnd_563823 : Nat := 4983230072969 + 3 ^ 40 * 563823 * 2
def baseEnd_563823 : Nat := 96504067686684257873177

theorem tailTrace_563823 : CollatzResearch.WordTrace tailWord_563823 prefixEnd_563823 96504067686684257873177 := by
  unfold tailWord_563823
  simp only [CollatzResearch.WordTrace]
  refine ⟨20564314236373039147208123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13709542824248692764805415 20564314236373039147208123)
  ·
    refine ⟨30846471354559558720812185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20564314236373039147208123 30846471354559558720812185)
    ·
      refine ⟨23134853515919669040609139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30846471354559558720812185 23134853515919669040609139)
      ·
        refine ⟨34702280273879503560913709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23134853515919669040609139 34702280273879503560913709)
        ·
          refine ⟨13013355102704813835342641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34702280273879503560913709 13013355102704813835342641)
          ·
            refine ⟨9760016327028610376506981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13013355102704813835342641 9760016327028610376506981)
            ·
              refine ⟨1830003061317864445595059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9760016327028610376506981 1830003061317864445595059)
              ·
                refine ⟨2745004591976796668392589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830003061317864445595059 2745004591976796668392589)
                ·
                  refine ⟨1029376721991298750647221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2745004591976796668392589 1029376721991298750647221)
                  ·
                    refine ⟨96504067686684257873177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1029376721991298750647221 96504067686684257873177)
                    ·
                      rfl

theorem cell23_563823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_563823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563823 prefixEnd_563823 := by exact prefixLift 563823
  have htrace : WordTrace (prefixWord ++ tailWord_563823) baseStart_563823 baseEnd_563823 := by
    simpa [prefixWord, tailWord_563823, baseEnd_563823] using wordTrace_append hprefix tailTrace_563823
  have hstable : (prefixWord ++ tailWord_563823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563823).length < 2 ^ (prefixWord ++ tailWord_563823).sum := by decide
  have hdescent : baseEnd_563823 < baseStart_563823 := by decide
  rcases family_descends (prefixWord ++ tailWord_563823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563824 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 2, 2, 3]
def baseStart_563824 : Nat := 118140960795 + 563824 * 2 ^ 59
def prefixEnd_563824 : Nat := 4983230072969 + 3 ^ 40 * 563824 * 2
def baseEnd_563824 : Nat := 289512716540707269707027

theorem tailTrace_563824 : CollatzResearch.WordTrace tailWord_563824 prefixEnd_563824 289512716540707269707027 := by
  unfold tailWord_563824
  simp only [CollatzResearch.WordTrace]
  refine ⟨10282175354684708158997263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13709567139579610878663017 10282175354684708158997263)
  ·
    refine ⟨15423263032027062238495895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10282175354684708158997263 15423263032027062238495895)
    ·
      refine ⟨23134894548040593357743843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15423263032027062238495895 23134894548040593357743843)
      ·
        refine ⟨34702341822060890036615765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23134894548040593357743843 34702341822060890036615765)
        ·
          refine ⟨406668068227276055116591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 34702341822060890036615765 406668068227276055116591)
          ·
            refine ⟨610002102340914082674887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406668068227276055116591 610002102340914082674887)
            ·
              refine ⟨915003153511371124012331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610002102340914082674887 915003153511371124012331)
              ·
                refine ⟨1372504730267056686018497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915003153511371124012331 1372504730267056686018497)
                ·
                  refine ⟨1029378547700292514513873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1372504730267056686018497 1029378547700292514513873)
                  ·
                    refine ⟨772033910775219385885405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1029378547700292514513873 772033910775219385885405)
                    ·
                      refine ⟨289512716540707269707027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 772033910775219385885405 289512716540707269707027)
                      ·
                        rfl

theorem cell23_563824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 2, 2, 3].length) (baseStart_563824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563824 prefixEnd_563824 := by exact prefixLift 563824
  have htrace : WordTrace (prefixWord ++ tailWord_563824) baseStart_563824 baseEnd_563824 := by
    simpa [prefixWord, tailWord_563824, baseEnd_563824] using wordTrace_append hprefix tailTrace_563824
  have hstable : (prefixWord ++ tailWord_563824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563824).length < 2 ^ (prefixWord ++ tailWord_563824).sum := by decide
  have hdescent : baseEnd_563824 < baseStart_563824 := by decide
  rcases family_descends (prefixWord ++ tailWord_563824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563840 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 1, 5]
def baseStart_563840 : Nat := 118140960795 + 563840 * 2 ^ 59
def prefixEnd_563840 : Nat := 4983230072969 + 3 ^ 40 * 563840 * 2
def baseEnd_563840 : Nat := 96506977410393069035651

theorem tailTrace_563840 : CollatzResearch.WordTrace tailWord_563840 prefixEnd_563840 96506977410393069035651 := by
  unfold tailWord_563840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10282467138655725525288487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13709956184874300700384649 10282467138655725525288487)
  ·
    refine ⟨15423700707983588287932731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10282467138655725525288487 15423700707983588287932731)
    ·
      refine ⟨23135551061975382431899097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15423700707983588287932731 23135551061975382431899097)
      ·
        refine ⟨17351663296481536823924323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23135551061975382431899097 17351663296481536823924323)
        ·
          refine ⟨26027494944722305235886485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17351663296481536823924323 26027494944722305235886485)
          ·
            refine ⟨1220038825533858057932179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26027494944722305235886485 1220038825533858057932179)
            ·
              refine ⟨1830058238300787086898269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220038825533858057932179 1830058238300787086898269)
              ·
                refine ⟨686271839362795157586851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1830058238300787086898269 686271839362795157586851)
                ·
                  refine ⟨1029407759044192736380277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686271839362795157586851 1029407759044192736380277)
                  ·
                    refine ⟨96506977410393069035651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1029407759044192736380277 96506977410393069035651)
                    ·
                      rfl

theorem cell23_563840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 1, 5].length) (baseStart_563840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563840 prefixEnd_563840 := by exact prefixLift 563840
  have htrace : WordTrace (prefixWord ++ tailWord_563840) baseStart_563840 baseEnd_563840 := by
    simpa [prefixWord, tailWord_563840, baseEnd_563840] using wordTrace_append hprefix tailTrace_563840
  have hstable : (prefixWord ++ tailWord_563840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563840).length < 2 ^ (prefixWord ++ tailWord_563840).sum := by decide
  have hdescent : baseEnd_563840 < baseStart_563840 := by decide
  rcases family_descends (prefixWord ++ tailWord_563840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563854 : List Nat := [4, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3]
def baseStart_563854 : Nat := 118140960795 + 563854 * 2 ^ 59
def prefixEnd_563854 : Nat := 4983230072969 + 3 ^ 40 * 563854 * 2
def baseEnd_563854 : Nat := 289528120960342152331889

theorem tailTrace_563854 : CollatzResearch.WordTrace tailWord_563854 prefixEnd_563854 289528120960342152331889 := by
  unfold tailWord_563854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2570680612407591430198327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13710296599507154294391077 2570680612407591430198327)
  ·
    refine ⟨3856020918611387145297491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2570680612407591430198327 3856020918611387145297491)
    ·
      refine ⟨5784031377917080717946237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856020918611387145297491 5784031377917080717946237)
      ·
        refine ⟨2169011766718905269229839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5784031377917080717946237 2169011766718905269229839)
        ·
          refine ⟨3253517650078357903844759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169011766718905269229839 3253517650078357903844759)
          ·
            refine ⟨4880276475117536855767139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253517650078357903844759 4880276475117536855767139)
            ·
              refine ⟨7320414712676305283650709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4880276475117536855767139 7320414712676305283650709)
              ·
                refine ⟨343144439656701810171127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7320414712676305283650709 343144439656701810171127)
                ·
                  refine ⟨514716659485052715256691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343144439656701810171127 514716659485052715256691)
                  ·
                    refine ⟨772074989227579072885037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 514716659485052715256691 772074989227579072885037)
                    ·
                      refine ⟨289528120960342152331889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 772074989227579072885037 289528120960342152331889)
                      ·
                        rfl

theorem cell23_563854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_563854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563854 prefixEnd_563854 := by exact prefixLift 563854
  have htrace : WordTrace (prefixWord ++ tailWord_563854) baseStart_563854 baseEnd_563854 := by
    simpa [prefixWord, tailWord_563854, baseEnd_563854] using wordTrace_append hprefix tailTrace_563854
  have hstable : (prefixWord ++ tailWord_563854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563854).length < 2 ^ (prefixWord ++ tailWord_563854).sum := by decide
  have hdescent : baseEnd_563854 < baseStart_563854 := by decide
  rcases family_descends (prefixWord ++ tailWord_563854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563905 : List Nat := [1, 2, 6, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_563905 : Nat := 118140960795 + 563905 * 2 ^ 59
def prefixEnd_563905 : Nat := 4983230072969 + 3 ^ 40 * 563905 * 2
def baseEnd_563905 : Nat := 289554308473721452794155

theorem tailTrace_563905 : CollatzResearch.WordTrace tailWord_563905 prefixEnd_563905 289554308473721452794155 := by
  unfold tailWord_563905
  simp only [CollatzResearch.WordTrace]
  refine ⟨20567305022075967151693169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13711536681383978101128779 20567305022075967151693169)
  ·
    refine ⟨15425478766556975363769877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20567305022075967151693169 15425478766556975363769877)
    ·
      refine ⟨723069317182358220176713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15425478766556975363769877 723069317182358220176713)
      ·
        refine ⟨542301987886768665132535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 723069317182358220176713 542301987886768665132535)
        ·
          refine ⟨813452981830152997698803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542301987886768665132535 813452981830152997698803)
          ·
            refine ⟨1220179472745229496548205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813452981830152997698803 1220179472745229496548205)
            ·
              refine ⟨457567302279461061205577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1220179472745229496548205 457567302279461061205577)
              ·
                refine ⟨343175476709595795904183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457567302279461061205577 343175476709595795904183)
                ·
                  refine ⟨514763215064393693856275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343175476709595795904183 514763215064393693856275)
                  ·
                    refine ⟨772144822596590540784413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 514763215064393693856275 772144822596590540784413)
                    ·
                      refine ⟨289554308473721452794155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 772144822596590540784413 289554308473721452794155)
                      ·
                        rfl

theorem cell23_563905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_563905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563905 prefixEnd_563905 := by exact prefixLift 563905
  have htrace : WordTrace (prefixWord ++ tailWord_563905) baseStart_563905 baseEnd_563905 := by
    simpa [prefixWord, tailWord_563905, baseEnd_563905] using wordTrace_append hprefix tailTrace_563905
  have hstable : (prefixWord ++ tailWord_563905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563905).length < 2 ^ (prefixWord ++ tailWord_563905).sum := by decide
  have hdescent : baseEnd_563905 < baseStart_563905 := by decide
  rcases family_descends (prefixWord ++ tailWord_563905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_563973 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 11]
def baseStart_563973 : Nat := 118140960795 + 563973 * 2 ^ 59
def prefixEnd_563973 : Nat := 4983230072969 + 3 ^ 40 * 563973 * 2
def baseEnd_563973 : Nat := 32176580573136354082649

theorem tailTrace_563973 : CollatzResearch.WordTrace tailWord_563973 prefixEnd_563973 32176580573136354082649 := by
  unfold tailWord_563973
  simp only [CollatzResearch.WordTrace]
  refine ⟨20569785185829614765168573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13713190123886409843445715 20569785185829614765168573)
  ·
    refine ⟨7713669444686105536938215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20569785185829614765168573 7713669444686105536938215)
    ·
      refine ⟨11570504167029158305407323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7713669444686105536938215 11570504167029158305407323)
      ·
        refine ⟨17355756250543737458110985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11570504167029158305407323 17355756250543737458110985)
        ·
          refine ⟨13016817187907803093583239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17355756250543737458110985 13016817187907803093583239)
          ·
            refine ⟨19525225781861704640374859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13016817187907803093583239 19525225781861704640374859)
            ·
              refine ⟨29287838672792556960562289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19525225781861704640374859 29287838672792556960562289)
              ·
                refine ⟨21965879004594417720421717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29287838672792556960562289 21965879004594417720421717)
                ·
                  refine ⟨32176580573136354082649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 21965879004594417720421717 32176580573136354082649)
                  ·
                    rfl

theorem cell23_563973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_563973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_563973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_563973 prefixEnd_563973 := by exact prefixLift 563973
  have htrace : WordTrace (prefixWord ++ tailWord_563973) baseStart_563973 baseEnd_563973 := by
    simpa [prefixWord, tailWord_563973, baseEnd_563973] using wordTrace_append hprefix tailTrace_563973
  have hstable : (prefixWord ++ tailWord_563973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_563973).length < 2 ^ (prefixWord ++ tailWord_563973).sum := by decide
  have hdescent : baseEnd_563973 < baseStart_563973 := by decide
  rcases family_descends (prefixWord ++ tailWord_563973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564040 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_564040 : Nat := 118140960795 + 564040 * 2 ^ 59
def prefixEnd_564040 : Nat := 4983230072969 + 3 ^ 40 * 564040 * 2
def baseEnd_564040 : Nat := 289623628362078424606033

theorem tailTrace_564040 : CollatzResearch.WordTrace tailWord_564040 prefixEnd_564040 289623628362078424606033 := by
  unfold tailWord_564040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10286114438293442603928787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13714819251057923471905049 10286114438293442603928787)
  ·
    refine ⟨15429171657440163905893181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10286114438293442603928787 15429171657440163905893181)
    ·
      refine ⟨5785939371540061464709943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15429171657440163905893181 5785939371540061464709943)
      ·
        refine ⟨8678909057310092197064915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5785939371540061464709943 8678909057310092197064915)
        ·
          refine ⟨13018363585965138295597373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8678909057310092197064915 13018363585965138295597373)
          ·
            refine ⟨4881886344736926860849015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13018363585965138295597373 4881886344736926860849015)
            ·
              refine ⟨7322829517105390291273523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881886344736926860849015 7322829517105390291273523)
              ·
                refine ⟨10984244275658085436910285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7322829517105390291273523 10984244275658085436910285)
                ·
                  refine ⟨4119091603371782038841357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10984244275658085436910285 4119091603371782038841357)
                  ·
                    refine ⟨1544659351264418264565509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4119091603371782038841357 1544659351264418264565509)
                    ·
                      refine ⟨289623628362078424606033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1544659351264418264565509 289623628362078424606033)
                      ·
                        rfl

theorem cell23_564040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_564040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564040 prefixEnd_564040 := by exact prefixLift 564040
  have htrace : WordTrace (prefixWord ++ tailWord_564040) baseStart_564040 baseEnd_564040 := by
    simpa [prefixWord, tailWord_564040, baseEnd_564040] using wordTrace_append hprefix tailTrace_564040
  have hstable : (prefixWord ++ tailWord_564040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564040).length < 2 ^ (prefixWord ++ tailWord_564040).sum := by decide
  have hdescent : baseEnd_564040 < baseStart_564040 := by decide
  rcases family_descends (prefixWord ++ tailWord_564040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564050 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_564050 : Nat := 118140960795 + 564050 * 2 ^ 59
def prefixEnd_564050 : Nat := 4983230072969 + 3 ^ 40 * 564050 * 2
def baseEnd_564050 : Nat := 96542921056207795160329

theorem tailTrace_564050 : CollatzResearch.WordTrace tailWord_564050 prefixEnd_564050 96542921056207795160329 := by
  unfold tailWord_564050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5143148401637664228930401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13715062404367104610481069 5143148401637664228930401)
  ·
    refine ⟨3857361301228248171697801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5143148401637664228930401 3857361301228248171697801)
    ·
      refine ⟨2893020975921186128773351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3857361301228248171697801 2893020975921186128773351)
      ·
        refine ⟨4339531463881779193160027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2893020975921186128773351 4339531463881779193160027)
        ·
          refine ⟨6509297195822668789740041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4339531463881779193160027 6509297195822668789740041)
          ·
            refine ⟨4881972896867001592305031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6509297195822668789740041 4881972896867001592305031)
            ·
              refine ⟨7322959345300502388457547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4881972896867001592305031 7322959345300502388457547)
              ·
                refine ⟨10984439017950753582686321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7322959345300502388457547 10984439017950753582686321)
                ·
                  refine ⟨8238329263463065187014741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10984439017950753582686321 8238329263463065187014741)
                  ·
                    refine ⟨96542921056207795160329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8238329263463065187014741 96542921056207795160329)
                    ·
                      rfl

theorem cell23_564050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_564050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564050 prefixEnd_564050 := by exact prefixLift 564050
  have htrace : WordTrace (prefixWord ++ tailWord_564050) baseStart_564050 baseEnd_564050 := by
    simpa [prefixWord, tailWord_564050, baseEnd_564050] using wordTrace_append hprefix tailTrace_564050
  have hstable : (prefixWord ++ tailWord_564050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564050).length < 2 ^ (prefixWord ++ tailWord_564050).sum := by decide
  have hdescent : baseEnd_564050 < baseStart_564050 := by decide
  rcases family_descends (prefixWord ++ tailWord_564050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564080 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 8]
def baseStart_564080 : Nat := 118140960795 + 564080 * 2 ^ 59
def prefixEnd_564080 : Nat := 4983230072969 + 3 ^ 40 * 564080 * 2
def baseEnd_564080 : Nat := 32182685287584252011761

theorem tailTrace_564080 : CollatzResearch.WordTrace tailWord_564080 prefixEnd_564080 32182685287584252011761 := by
  unfold tailWord_564080
  simp only [CollatzResearch.WordTrace]
  refine ⟨10286843898220986019656847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13715791864294648026209129 10286843898220986019656847)
  ·
    refine ⟨15430265847331479029485271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10286843898220986019656847 15430265847331479029485271)
    ·
      refine ⟨23145398770997218544227907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15430265847331479029485271 23145398770997218544227907)
      ·
        refine ⟨34718098156495827816341861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23145398770997218544227907 34718098156495827816341861)
        ·
          refine ⟨6509643404342967715564099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34718098156495827816341861 6509643404342967715564099)
          ·
            refine ⟨9764465106514451573346149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509643404342967715564099 9764465106514451573346149)
            ·
              refine ⟨1830837207471459670002403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9764465106514451573346149 1830837207471459670002403)
              ·
                refine ⟨2746255811207189505003605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830837207471459670002403 2746255811207189505003605)
                ·
                  refine ⟨32182685287584252011761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2746255811207189505003605 32182685287584252011761)
                  ·
                    rfl

theorem cell23_564080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 8].length) (baseStart_564080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564080 prefixEnd_564080 := by exact prefixLift 564080
  have htrace : WordTrace (prefixWord ++ tailWord_564080) baseStart_564080 baseEnd_564080 := by
    simpa [prefixWord, tailWord_564080, baseEnd_564080] using wordTrace_append hprefix tailTrace_564080
  have hstable : (prefixWord ++ tailWord_564080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564080).length < 2 ^ (prefixWord ++ tailWord_564080).sum := by decide
  have hdescent : baseEnd_564080 < baseStart_564080 := by decide
  rcases family_descends (prefixWord ++ tailWord_564080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564135 : List Nat := [1, 1, 6, 1, 3, 2, 2, 2, 1, 4]
def baseStart_564135 : Nat := 118140960795 + 564135 * 2 ^ 59
def prefixEnd_564135 : Nat := 4983230072969 + 3 ^ 40 * 564135 * 2
def baseEnd_564135 : Nat := 96557469674751850972699

theorem tailTrace_564135 : CollatzResearch.WordTrace tailWord_564135 prefixEnd_564135 96557469674751850972699 := by
  unfold tailWord_564135
  simp only [CollatzResearch.WordTrace]
  refine ⟨20575693811242716432565859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13717129207495144288377239 20575693811242716432565859)
  ·
    refine ⟨30863540716864074648848789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20575693811242716432565859 30863540716864074648848789)
    ·
      refine ⟨1446728471103003499164787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30863540716864074648848789 1446728471103003499164787)
      ·
        refine ⟨2170092706654505248747181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446728471103003499164787 2170092706654505248747181)
        ·
          refine ⟨813784764995439468280193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2170092706654505248747181 813784764995439468280193)
          ·
            refine ⟨610338573746579601210145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 813784764995439468280193 610338573746579601210145)
            ·
              refine ⟨457753930309934700907609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610338573746579601210145 457753930309934700907609)
              ·
                refine ⟨343315447732451025680707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 457753930309934700907609 343315447732451025680707)
                ·
                  refine ⟨514973171598676538521061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343315447732451025680707 514973171598676538521061)
                  ·
                    refine ⟨96557469674751850972699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 514973171598676538521061 96557469674751850972699)
                    ·
                      rfl

theorem cell23_564135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_564135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564135 prefixEnd_564135 := by exact prefixLift 564135
  have htrace : WordTrace (prefixWord ++ tailWord_564135) baseStart_564135 baseEnd_564135 := by
    simpa [prefixWord, tailWord_564135, baseEnd_564135] using wordTrace_append hprefix tailTrace_564135
  have hstable : (prefixWord ++ tailWord_564135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564135).length < 2 ^ (prefixWord ++ tailWord_564135).sum := by decide
  have hdescent : baseEnd_564135 < baseStart_564135 := by decide
  rcases family_descends (prefixWord ++ tailWord_564135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564168 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_564168 : Nat := 118140960795 + 564168 * 2 ^ 59
def prefixEnd_564168 : Nat := 4983230072969 + 3 ^ 40 * 564168 * 2
def baseEnd_564168 : Nat := 289689353885853923805445

theorem tailTrace_564168 : CollatzResearch.WordTrace tailWord_564168 prefixEnd_564168 289689353885853923805445 := by
  unfold tailWord_564168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10288448710061581534258579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13717931613415442045678105 10288448710061581534258579)
  ·
    refine ⟨15432673065092372301387869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10288448710061581534258579 15432673065092372301387869)
    ·
      refine ⟨5787252399409639613020451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15432673065092372301387869 5787252399409639613020451)
      ·
        refine ⟨8680878599114459419530677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5787252399409639613020451 8680878599114459419530677)
        ·
          refine ⟨813832368666980570581001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8680878599114459419530677 813832368666980570581001)
          ·
            refine ⟨610374276500235427935751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 813832368666980570581001 610374276500235427935751)
            ·
              refine ⟨915561414750353141903627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610374276500235427935751 915561414750353141903627)
              ·
                refine ⟨1373342122125529712855441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915561414750353141903627 1373342122125529712855441)
                ·
                  refine ⟨1030006591594147284641581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1373342122125529712855441 1030006591594147284641581)
                  ·
                    refine ⟨386252471847805231740593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1030006591594147284641581 386252471847805231740593)
                    ·
                      refine ⟨289689353885853923805445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 386252471847805231740593 289689353885853923805445)
                      ·
                        rfl

theorem cell23_564168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_564168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564168 prefixEnd_564168 := by exact prefixLift 564168
  have htrace : WordTrace (prefixWord ++ tailWord_564168) baseStart_564168 baseEnd_564168 := by
    simpa [prefixWord, tailWord_564168, baseEnd_564168] using wordTrace_append hprefix tailTrace_564168
  have hstable : (prefixWord ++ tailWord_564168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564168).length < 2 ^ (prefixWord ++ tailWord_564168).sum := by decide
  have hdescent : baseEnd_564168 < baseStart_564168 := by decide
  rcases family_descends (prefixWord ++ tailWord_564168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564177 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_564177 : Nat := 118140960795 + 564177 * 2 ^ 59
def prefixEnd_564177 : Nat := 4983230072969 + 3 ^ 40 * 564177 * 2
def baseEnd_564177 : Nat := 289693975211744388592903

theorem tailTrace_564177 : CollatzResearch.WordTrace tailWord_564177 prefixEnd_564177 289693975211744388592903 := by
  unfold tailWord_564177
  simp only [CollatzResearch.WordTrace]
  refine ⟨20577225677090557605594785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13718150451393705070396523 20577225677090557605594785)
  ·
    refine ⟨15432919257817918204196089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20577225677090557605594785 15432919257817918204196089)
    ·
      refine ⟨11574689443363438653147067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15432919257817918204196089 11574689443363438653147067)
      ·
        refine ⟨17362034165045157979720601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11574689443363438653147067 17362034165045157979720601)
        ·
          refine ⟨13021525623783868484790451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17362034165045157979720601 13021525623783868484790451)
          ·
            refine ⟨19532288435675802727185677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13021525623783868484790451 19532288435675802727185677)
            ·
              refine ⟨7324608163378426022694629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19532288435675802727185677 7324608163378426022694629)
              ·
                refine ⟨1373364030633454879255243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7324608163378426022694629 1373364030633454879255243)
                ·
                  refine ⟨2060046045950182318882865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1373364030633454879255243 2060046045950182318882865)
                  ·
                    refine ⟨1545034534462636739162149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2060046045950182318882865 1545034534462636739162149)
                    ·
                      refine ⟨289693975211744388592903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1545034534462636739162149 289693975211744388592903)
                      ·
                        rfl

theorem cell23_564177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_564177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564177 prefixEnd_564177 := by exact prefixLift 564177
  have htrace : WordTrace (prefixWord ++ tailWord_564177) baseStart_564177 baseEnd_564177 := by
    simpa [prefixWord, tailWord_564177, baseEnd_564177] using wordTrace_append hprefix tailTrace_564177
  have hstable : (prefixWord ++ tailWord_564177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564177).length < 2 ^ (prefixWord ++ tailWord_564177).sum := by decide
  have hdescent : baseEnd_564177 < baseStart_564177 := by decide
  rcases family_descends (prefixWord ++ tailWord_564177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564178 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_564178 : Nat := 118140960795 + 564178 * 2 ^ 59
def prefixEnd_564178 : Nat := 4983230072969 + 3 ^ 40 * 564178 * 2
def baseEnd_564178 : Nat := 96564829564132961560133

theorem tailTrace_564178 : CollatzResearch.WordTrace tailWord_564178 prefixEnd_564178 96564829564132961560133 := by
  unfold tailWord_564178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5144315537521733694095297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13718174766724623184254125 5144315537521733694095297)
  ·
    refine ⟨3858236653141300270571473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5144315537521733694095297 3858236653141300270571473)
    ·
      refine ⟨2893677489855975202928605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3858236653141300270571473 2893677489855975202928605)
      ·
        refine ⟨1085129058695990701098227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2893677489855975202928605 1085129058695990701098227)
        ·
          refine ⟨1627693588043986051647341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085129058695990701098227 1627693588043986051647341)
          ·
            refine ⟨610385095516494769367753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1627693588043986051647341 610385095516494769367753)
            ·
              refine ⟨457788821637371077025815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 610385095516494769367753 457788821637371077025815)
              ·
                refine ⟨686683232456056615538723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457788821637371077025815 686683232456056615538723)
                ·
                  refine ⟨1030024848684084923308085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686683232456056615538723 1030024848684084923308085)
                  ·
                    refine ⟨96564829564132961560133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1030024848684084923308085 96564829564132961560133)
                    ·
                      rfl

theorem cell23_564178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_564178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564178 prefixEnd_564178 := by exact prefixLift 564178
  have htrace : WordTrace (prefixWord ++ tailWord_564178) baseStart_564178 baseEnd_564178 := by
    simpa [prefixWord, tailWord_564178, baseEnd_564178] using wordTrace_append hprefix tailTrace_564178
  have hstable : (prefixWord ++ tailWord_564178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564178).length < 2 ^ (prefixWord ++ tailWord_564178).sum := by decide
  have hdescent : baseEnd_564178 < baseStart_564178 := by decide
  rcases family_descends (prefixWord ++ tailWord_564178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564181 : List Nat := [1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_564181 : Nat := 118140960795 + 564181 * 2 ^ 59
def prefixEnd_564181 : Nat := 4983230072969 + 3 ^ 40 * 564181 * 2
def baseEnd_564181 : Nat := 289696029134362372942885

theorem tailTrace_564181 : CollatzResearch.WordTrace tailWord_564181 prefixEnd_564181 289696029134362372942885 := by
  unfold tailWord_564181
  simp only [CollatzResearch.WordTrace]
  refine ⟨20577371569076066288740397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13718247712717377525826931 20577371569076066288740397)
  ·
    refine ⟨7716514338403524858277649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20577371569076066288740397 7716514338403524858277649)
    ·
      refine ⟨5787385753802643643708237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7716514338403524858277649 5787385753802643643708237)
      ·
        refine ⟨2170269657675991366390589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5787385753802643643708237 2170269657675991366390589)
        ·
          refine ⟨813851121628496762396471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2170269657675991366390589 813851121628496762396471)
          ·
            refine ⟨1220776682442745143594707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813851121628496762396471 1220776682442745143594707)
            ·
              refine ⟨1831165023664117715392061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220776682442745143594707 1831165023664117715392061)
              ·
                refine ⟨686686883874044143272023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1831165023664117715392061 686686883874044143272023)
                ·
                  refine ⟨1030030325811066214908035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686686883874044143272023 1030030325811066214908035)
                  ·
                    refine ⟨1545045488716599322362053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1030030325811066214908035 1545045488716599322362053)
                    ·
                      refine ⟨289696029134362372942885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1545045488716599322362053 289696029134362372942885)
                      ·
                        rfl

theorem cell23_564181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_564181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564181 prefixEnd_564181 := by exact prefixLift 564181
  have htrace : WordTrace (prefixWord ++ tailWord_564181) baseStart_564181 baseEnd_564181 := by
    simpa [prefixWord, tailWord_564181, baseEnd_564181] using wordTrace_append hprefix tailTrace_564181
  have hstable : (prefixWord ++ tailWord_564181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564181).length < 2 ^ (prefixWord ++ tailWord_564181).sum := by decide
  have hdescent : baseEnd_564181 < baseStart_564181 := by decide
  rcases family_descends (prefixWord ++ tailWord_564181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564212 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_564212 : Nat := 118140960795 + 564212 * 2 ^ 59
def prefixEnd_564212 : Nat := 4983230072969 + 3 ^ 40 * 564212 * 2
def baseEnd_564212 : Nat := 96570649011550583885081

theorem tailTrace_564212 : CollatzResearch.WordTrace tailWord_564212 prefixEnd_564212 96570649011550583885081 := by
  unfold tailWord_564212
  simp only [CollatzResearch.WordTrace]
  refine ⟨10289251115981879291559445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13719001487975839055412593 10289251115981879291559445)
  ·
    refine ⟨482308646061650591791849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10289251115981879291559445 482308646061650591791849)
    ·
      refine ⟨361731484546237943843887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 482308646061650591791849 361731484546237943843887)
      ·
        refine ⟨542597226819356915765831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361731484546237943843887 542597226819356915765831)
        ·
          refine ⟨813895840229035373648747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542597226819356915765831 813895840229035373648747)
          ·
            refine ⟨1220843760343553060473121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813895840229035373648747 1220843760343553060473121)
            ·
              refine ⟨915632820257664795354841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1220843760343553060473121 915632820257664795354841)
              ·
                refine ⟨686724615193248596516131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 915632820257664795354841 686724615193248596516131)
                ·
                  refine ⟨1030086922789872894774197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 686724615193248596516131 1030086922789872894774197)
                  ·
                    refine ⟨96570649011550583885081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1030086922789872894774197 96570649011550583885081)
                    ·
                      rfl

theorem cell23_564212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_564212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564212 prefixEnd_564212 := by exact prefixLift 564212
  have htrace : WordTrace (prefixWord ++ tailWord_564212) baseStart_564212 baseEnd_564212 := by
    simpa [prefixWord, tailWord_564212, baseEnd_564212] using wordTrace_append hprefix tailTrace_564212
  have hstable : (prefixWord ++ tailWord_564212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564212).length < 2 ^ (prefixWord ++ tailWord_564212).sum := by decide
  have hdescent : baseEnd_564212 < baseStart_564212 := by decide
  rcases family_descends (prefixWord ++ tailWord_564212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564224 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 7, 3, 2]
def baseStart_564224 : Nat := 118140960795 + 564224 * 2 ^ 59
def prefixEnd_564224 : Nat := 4983230072969 + 3 ^ 40 * 564224 * 2
def baseEnd_564224 : Nat := 289718108802505704705187

theorem tailTrace_564224 : CollatzResearch.WordTrace tailWord_564224 prefixEnd_564224 289718108802505704705187 := by
  unfold tailWord_564224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10289469953960142316277863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13719293271946856421703817 10289469953960142316277863)
  ·
    refine ⟨15434204930940213474416795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10289469953960142316277863 15434204930940213474416795)
    ·
      refine ⟨23151307396410320211625193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15434204930940213474416795 23151307396410320211625193)
      ·
        refine ⟨17363480547307740158718895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23151307396410320211625193 17363480547307740158718895)
        ·
          refine ⟨26045220820961610238078343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17363480547307740158718895 26045220820961610238078343)
          ·
            refine ⟨39067831231442415357117515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26045220820961610238078343 39067831231442415357117515)
            ·
              refine ⟨58601746847163623035676273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39067831231442415357117515 58601746847163623035676273)
              ·
                refine ⟨43951310135372717276757205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58601746847163623035676273 43951310135372717276757205)
                ·
                  refine ⟨1030108831297798061173997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 43951310135372717276757205 1030108831297798061173997)
                  ·
                    refine ⟨386290811736674272940249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1030108831297798061173997 386290811736674272940249)
                    ·
                      refine ⟨289718108802505704705187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 386290811736674272940249 289718108802505704705187)
                      ·
                        rfl

theorem cell23_564224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_564224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564224 prefixEnd_564224 := by exact prefixLift 564224
  have htrace : WordTrace (prefixWord ++ tailWord_564224) baseStart_564224 baseEnd_564224 := by
    simpa [prefixWord, tailWord_564224, baseEnd_564224] using wordTrace_append hprefix tailTrace_564224
  have hstable : (prefixWord ++ tailWord_564224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564224).length < 2 ^ (prefixWord ++ tailWord_564224).sum := by decide
  have hdescent : baseEnd_564224 < baseStart_564224 := by decide
  rcases family_descends (prefixWord ++ tailWord_564224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564267 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 4]
def baseStart_564267 : Nat := 118140960795 + 564267 * 2 ^ 59
def prefixEnd_564267 : Nat := 4983230072969 + 3 ^ 40 * 564267 * 2
def baseEnd_564267 : Nat := 289740188470649036467489

theorem tailTrace_564267 : CollatzResearch.WordTrace tailWord_564267 prefixEnd_564267 289740188470649036467489 := by
  unfold tailWord_564267
  simp only [CollatzResearch.WordTrace]
  refine ⟨20580508246764502976371055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13720338831176335317580703 20580508246764502976371055)
  ·
    refine ⟨30870762370146754464556583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20580508246764502976371055 30870762370146754464556583)
    ·
      refine ⟨46306143555220131696834875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30870762370146754464556583 46306143555220131696834875)
      ·
        refine ⟨69459215332830197545252313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46306143555220131696834875 69459215332830197545252313)
        ·
          refine ⟨52094411499622648158939235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69459215332830197545252313 52094411499622648158939235)
          ·
            refine ⟨78141617249433972238408853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52094411499622648158939235 78141617249433972238408853)
            ·
              refine ⟨3662888308567217448675415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78141617249433972238408853 3662888308567217448675415)
              ·
                refine ⟨5494332462850826173013123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3662888308567217448675415 5494332462850826173013123)
                ·
                  refine ⟨8241498694276239259519685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5494332462850826173013123 8241498694276239259519685)
                  ·
                    refine ⟨1545281005176794861159941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8241498694276239259519685 1545281005176794861159941)
                    ·
                      refine ⟨289740188470649036467489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1545281005176794861159941 289740188470649036467489)
                      ·
                        rfl

theorem cell23_564267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 4, 4].length) (baseStart_564267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564267 prefixEnd_564267 := by exact prefixLift 564267
  have htrace : WordTrace (prefixWord ++ tailWord_564267) baseStart_564267 baseEnd_564267 := by
    simpa [prefixWord, tailWord_564267, baseEnd_564267] using wordTrace_append hprefix tailTrace_564267
  have hstable : (prefixWord ++ tailWord_564267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564267).length < 2 ^ (prefixWord ++ tailWord_564267).sum := by decide
  have hdescent : baseEnd_564267 < baseStart_564267 := by decide
  rcases family_descends (prefixWord ++ tailWord_564267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564277 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 9]
def baseStart_564277 : Nat := 118140960795 + 564277 * 2 ^ 59
def prefixEnd_564277 : Nat := 4983230072969 + 3 ^ 40 * 564277 * 2
def baseEnd_564277 : Nat := 32193924808577110815827

theorem tailTrace_564277 : CollatzResearch.WordTrace tailWord_564277 prefixEnd_564277 32193924808577110815827 := by
  unfold tailWord_564277
  simp only [CollatzResearch.WordTrace]
  refine ⟨20580872976728274684235085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13720581984485516456156723 20580872976728274684235085)
  ·
    refine ⟨7717827366273103006588157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20580872976728274684235085 7717827366273103006588157)
    ·
      refine ⟨2894185262352413627470559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7717827366273103006588157 2894185262352413627470559)
      ·
        refine ⟨4341277893528620441205839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894185262352413627470559 4341277893528620441205839)
        ·
          refine ⟨6511916840292930661808759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4341277893528620441205839 6511916840292930661808759)
          ·
            refine ⟨9767875260439395992713139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6511916840292930661808759 9767875260439395992713139)
            ·
              refine ⟨14651812890659093989069709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9767875260439395992713139 14651812890659093989069709)
              ·
                refine ⟨5494429833997160245901141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14651812890659093989069709 5494429833997160245901141)
                ·
                  refine ⟨32193924808577110815827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5494429833997160245901141 32193924808577110815827)
                  ·
                    rfl

theorem cell23_564277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_564277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564277 prefixEnd_564277 := by exact prefixLift 564277
  have htrace : WordTrace (prefixWord ++ tailWord_564277) baseStart_564277 baseEnd_564277 := by
    simpa [prefixWord, tailWord_564277, baseEnd_564277] using wordTrace_append hprefix tailTrace_564277
  have hstable : (prefixWord ++ tailWord_564277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564277).length < 2 ^ (prefixWord ++ tailWord_564277).sum := by decide
  have hdescent : baseEnd_564277 < baseStart_564277 := by decide
  rcases family_descends (prefixWord ++ tailWord_564277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564318 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_564318 : Nat := 118140960795 + 564318 * 2 ^ 59
def prefixEnd_564318 : Nat := 4983230072969 + 3 ^ 40 * 564318 * 2
def baseEnd_564318 : Nat := 289766375984028336929755

theorem tailTrace_564318 : CollatzResearch.WordTrace tailWord_564318 prefixEnd_564318 289766375984028336929755 := by
  unfold tailWord_564318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2572796046197467335809701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13721578913053159124318405 2572796046197467335809701)
  ·
    refine ⟨482399258662025125464319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2572796046197467335809701 482399258662025125464319)
    ·
      refine ⟨723598887993037688196479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 482399258662025125464319 723598887993037688196479)
      ·
        refine ⟨1085398331989556532294719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723598887993037688196479 1085398331989556532294719)
        ·
          refine ⟨1628097497984334798442079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085398331989556532294719 1628097497984334798442079)
          ·
            refine ⟨2442146246976502197663119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628097497984334798442079 2442146246976502197663119)
            ·
              refine ⟨3663219370464753296494679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442146246976502197663119 3663219370464753296494679)
              ·
                refine ⟨5494829055697129944742019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3663219370464753296494679 5494829055697129944742019)
                ·
                  refine ⟨8242243583545694917113029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5494829055697129944742019 8242243583545694917113029)
                  ·
                    refine ⟨1545420671914817796958693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8242243583545694917113029 1545420671914817796958693)
                    ·
                      refine ⟨289766375984028336929755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1545420671914817796958693 289766375984028336929755)
                      ·
                        rfl

theorem cell23_564318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_564318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564318 prefixEnd_564318 := by exact prefixLift 564318
  have htrace : WordTrace (prefixWord ++ tailWord_564318) baseStart_564318 baseEnd_564318 := by
    simpa [prefixWord, tailWord_564318, baseEnd_564318] using wordTrace_append hprefix tailTrace_564318
  have hstable : (prefixWord ++ tailWord_564318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564318).length < 2 ^ (prefixWord ++ tailWord_564318).sum := by decide
  have hdescent : baseEnd_564318 < baseStart_564318 := by decide
  rcases family_descends (prefixWord ++ tailWord_564318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564337 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 1, 10]
def baseStart_564337 : Nat := 118140960795 + 564337 * 2 ^ 59
def prefixEnd_564337 : Nat := 4983230072969 + 3 ^ 40 * 564337 * 2
def baseEnd_564337 : Nat := 96592044038821254197389

theorem tailTrace_564337 : CollatzResearch.WordTrace tailWord_564337 prefixEnd_564337 96592044038821254197389 := by
  unfold tailWord_564337
  simp only [CollatzResearch.WordTrace]
  refine ⟨20583061356510904931419265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13722040904340603287612843 20583061356510904931419265)
  ·
    refine ⟨15437296017383178698564449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20583061356510904931419265 15437296017383178698564449)
    ·
      refine ⟨11577972013037384023923337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15437296017383178698564449 11577972013037384023923337)
      ·
        refine ⟨8683479009778038017942503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11577972013037384023923337 8683479009778038017942503)
        ·
          refine ⟨13025218514667057026913755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8683479009778038017942503 13025218514667057026913755)
          ·
            refine ⟨19537827772000585540370633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13025218514667057026913755 19537827772000585540370633)
            ·
              refine ⟨14653370829000439155277975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19537827772000585540370633 14653370829000439155277975)
              ·
                refine ⟨21980056243500658732916963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14653370829000439155277975 21980056243500658732916963)
                ·
                  refine ⟨32970084365250988099375445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21980056243500658732916963 32970084365250988099375445)
                  ·
                    refine ⟨96592044038821254197389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 32970084365250988099375445 96592044038821254197389)
                    ·
                      rfl

theorem cell23_564337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_564337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564337 prefixEnd_564337 := by exact prefixLift 564337
  have htrace : WordTrace (prefixWord ++ tailWord_564337) baseStart_564337 baseEnd_564337 := by
    simpa [prefixWord, tailWord_564337, baseEnd_564337] using wordTrace_append hprefix tailTrace_564337
  have hstable : (prefixWord ++ tailWord_564337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564337).length < 2 ^ (prefixWord ++ tailWord_564337).sum := by decide
  have hdescent : baseEnd_564337 < baseStart_564337 := by decide
  rcases family_descends (prefixWord ++ tailWord_564337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564361 : List Nat := [1, 2, 1, 1, 4, 3, 1, 2, 2, 4, 2]
def baseStart_564361 : Nat := 118140960795 + 564361 * 2 ^ 59
def prefixEnd_564361 : Nat := 4983230072969 + 3 ^ 40 * 564361 * 2
def baseEnd_564361 : Nat := 289788455652171668692057

theorem tailTrace_564361 : CollatzResearch.WordTrace tailWord_564361 prefixEnd_564361 289788455652171668692057 := by
  unfold tailWord_564361
  simp only [CollatzResearch.WordTrace]
  refine ⟨20583936708423957030292937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13722624472282638020195291 20583936708423957030292937)
  ·
    refine ⟨15437952531317967772719703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20583936708423957030292937 15437952531317967772719703)
    ·
      refine ⟨23156928796976951659079555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15437952531317967772719703 23156928796976951659079555)
      ·
        refine ⟨34735393195465427488619333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23156928796976951659079555 34735393195465427488619333)
        ·
          refine ⟨6512886224149767654116125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34735393195465427488619333 6512886224149767654116125)
          ·
            refine ⟨2442332334056162870293547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6512886224149767654116125 2442332334056162870293547)
            ·
              refine ⟨3663498501084244305440321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442332334056162870293547 3663498501084244305440321)
              ·
                refine ⟨2747623875813183229080241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3663498501084244305440321 2747623875813183229080241)
                ·
                  refine ⟨2060717906859887421810181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2747623875813183229080241 2060717906859887421810181)
                  ·
                    refine ⟨386384607536228891589409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2060717906859887421810181 386384607536228891589409)
                    ·
                      refine ⟨289788455652171668692057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 386384607536228891589409 289788455652171668692057)
                      ·
                        rfl

theorem cell23_564361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 4, 2].length) (baseStart_564361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564361 prefixEnd_564361 := by exact prefixLift 564361
  have htrace : WordTrace (prefixWord ++ tailWord_564361) baseStart_564361 baseEnd_564361 := by
    simpa [prefixWord, tailWord_564361, baseEnd_564361] using wordTrace_append hprefix tailTrace_564361
  have hstable : (prefixWord ++ tailWord_564361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564361).length < 2 ^ (prefixWord ++ tailWord_564361).sum := by decide
  have hdescent : baseEnd_564361 < baseStart_564361 := by decide
  rcases family_descends (prefixWord ++ tailWord_564361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564378 : List Nat := [3, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2]
def baseStart_564378 : Nat := 118140960795 + 564378 * 2 ^ 59
def prefixEnd_564378 : Nat := 4983230072969 + 3 ^ 40 * 564378 * 2
def baseEnd_564378 : Nat := 289797184823298102179479

theorem tailTrace_564378 : CollatzResearch.WordTrace tailWord_564378 prefixEnd_564378 289797184823298102179479 := by
  unfold tailWord_564378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5146139187340592233415447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13723037832908245955774525 5146139187340592233415447)
  ·
    refine ⟨7719208781010888350123171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5146139187340592233415447 7719208781010888350123171)
    ·
      refine ⟨11578813171516332525184757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7719208781010888350123171 11578813171516332525184757)
      ·
        refine ⟨1085513734829656174236071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11578813171516332525184757 1085513734829656174236071)
        ·
          refine ⟨1628270602244484261354107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085513734829656174236071 1628270602244484261354107)
          ·
            refine ⟨2442405903366726392031161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628270602244484261354107 2442405903366726392031161)
            ·
              refine ⟨1831804427525044794023371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2442405903366726392031161 1831804427525044794023371)
              ·
                refine ⟨2747706641287567191035057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1831804427525044794023371 2747706641287567191035057)
                ·
                  refine ⟨2060779980965675393276293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2747706641287567191035057 2060779980965675393276293)
                  ·
                    refine ⟨386396246431064136239305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2060779980965675393276293 386396246431064136239305)
                    ·
                      refine ⟨289797184823298102179479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 386396246431064136239305 289797184823298102179479)
                      ·
                        rfl

theorem cell23_564378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_564378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564378 prefixEnd_564378 := by exact prefixLift 564378
  have htrace : WordTrace (prefixWord ++ tailWord_564378) baseStart_564378 baseEnd_564378 := by
    simpa [prefixWord, tailWord_564378, baseEnd_564378] using wordTrace_append hprefix tailTrace_564378
  have hstable : (prefixWord ++ tailWord_564378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564378).length < 2 ^ (prefixWord ++ tailWord_564378).sum := by decide
  have hdescent : baseEnd_564378 < baseStart_564378 := by decide
  rcases family_descends (prefixWord ++ tailWord_564378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564448 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 1, 5]
def baseStart_564448 : Nat := 118140960795 + 564448 * 2 ^ 59
def prefixEnd_564448 : Nat := 4983230072969 + 3 ^ 40 * 564448 * 2
def baseEnd_564448 : Nat := 96611042823037609434719

theorem tailTrace_564448 : CollatzResearch.WordTrace tailWord_564448 prefixEnd_564448 96611042823037609434719 := by
  unfold tailWord_564448
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293554929554385444354999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13724739906072513925806665 10293554929554385444354999)
  ·
    refine ⟨15440332394331578166532499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10293554929554385444354999 15440332394331578166532499)
    ·
      refine ⟨23160498591497367249798749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15440332394331578166532499 23160498591497367249798749)
      ·
        refine ⟨8685186971811512718674531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23160498591497367249798749 8685186971811512718674531)
        ·
          refine ⟨13027780457717269078011797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8685186971811512718674531 13027780457717269078011797)
          ·
            refine ⟨610677208955496988031803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13027780457717269078011797 610677208955496988031803)
            ·
              refine ⟨916015813433245482047705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610677208955496988031803 916015813433245482047705)
              ·
                refine ⟨687011860074934111535779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916015813433245482047705 687011860074934111535779)
                ·
                  refine ⟨1030517790112401167303669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687011860074934111535779 1030517790112401167303669)
                  ·
                    refine ⟨96611042823037609434719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1030517790112401167303669 96611042823037609434719)
                    ·
                      rfl

theorem cell23_564448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 5].length) (baseStart_564448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564448 prefixEnd_564448 := by exact prefixLift 564448
  have htrace : WordTrace (prefixWord ++ tailWord_564448) baseStart_564448 baseEnd_564448 := by
    simpa [prefixWord, tailWord_564448, baseEnd_564448] using wordTrace_append hprefix tailTrace_564448
  have hstable : (prefixWord ++ tailWord_564448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564448).length < 2 ^ (prefixWord ++ tailWord_564448).sum := by decide
  have hdescent : baseEnd_564448 < baseStart_564448 := by decide
  rcases family_descends (prefixWord ++ tailWord_564448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564461 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_564461 : Nat := 118140960795 + 564461 * 2 ^ 59
def prefixEnd_564461 : Nat := 4983230072969 + 3 ^ 40 * 564461 * 2
def baseEnd_564461 : Nat := 96613267905873759147199

theorem tailTrace_564461 : CollatzResearch.WordTrace tailWord_564461 prefixEnd_564461 96613267905873759147199 := by
  unfold tailWord_564461
  simp only [CollatzResearch.WordTrace]
  refine ⟨20587584008061674108933237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13725056005374449405955491 20587584008061674108933237)
  ·
    refine ⟨1930086000755781947712491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20587584008061674108933237 1930086000755781947712491)
    ·
      refine ⟨2895129001133672921568737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1930086000755781947712491 2895129001133672921568737)
      ·
        refine ⟨2171346750850254691176553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2895129001133672921568737 2171346750850254691176553)
        ·
          refine ⟨1628510063137691018382415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2171346750850254691176553 1628510063137691018382415)
          ·
            refine ⟨2442765094706536527573623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628510063137691018382415 2442765094706536527573623)
            ·
              refine ⟨3664147642059804791360435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442765094706536527573623 3664147642059804791360435)
              ·
                refine ⟨5496221463089707187040653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664147642059804791360435 5496221463089707187040653)
                ·
                  refine ⟨2061083048658640195140245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5496221463089707187040653 2061083048658640195140245)
                  ·
                    refine ⟨96613267905873759147199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2061083048658640195140245 96613267905873759147199)
                    ·
                      rfl

theorem cell23_564461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_564461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564461 prefixEnd_564461 := by exact prefixLift 564461
  have htrace : WordTrace (prefixWord ++ tailWord_564461) baseStart_564461 baseEnd_564461 := by
    simpa [prefixWord, tailWord_564461, baseEnd_564461] using wordTrace_append hprefix tailTrace_564461
  have hstable : (prefixWord ++ tailWord_564461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564461).length < 2 ^ (prefixWord ++ tailWord_564461).sum := by decide
  have hdescent : baseEnd_564461 < baseStart_564461 := by decide
  rcases family_descends (prefixWord ++ tailWord_564461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564491 : List Nat := [1, 1, 1, 1, 5, 5, 1, 8]
def baseStart_564491 : Nat := 118140960795 + 564491 * 2 ^ 59
def prefixEnd_564491 : Nat := 4983230072969 + 3 ^ 40 * 564491 * 2
def baseEnd_564491 : Nat := 10735378079157635558017

theorem tailTrace_564491 : CollatzResearch.WordTrace tailWord_564491 prefixEnd_564491 10735378079157635558017 := by
  unfold tailWord_564491
  simp only [CollatzResearch.WordTrace]
  refine ⟨20588678197952989232525327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13725785465301992821683551 20588678197952989232525327)
  ·
    refine ⟨30883017296929483848787991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20588678197952989232525327 30883017296929483848787991)
    ·
      refine ⟨46324525945394225773181987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30883017296929483848787991 46324525945394225773181987)
      ·
        refine ⟨69486788918091338659772981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46324525945394225773181987 69486788918091338659772981)
        ·
          refine ⟨6514386461071062999353717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69486788918091338659772981 6514386461071062999353717)
          ·
            refine ⟨610723730725412156189411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6514386461071062999353717 610723730725412156189411)
            ·
              refine ⟨916085596088118234284117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610723730725412156189411 916085596088118234284117)
              ·
                refine ⟨10735378079157635558017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 916085596088118234284117 10735378079157635558017)
                ·
                  rfl

theorem cell23_564491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 8].length) (baseStart_564491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564491 prefixEnd_564491 := by exact prefixLift 564491
  have htrace : WordTrace (prefixWord ++ tailWord_564491) baseStart_564491 baseEnd_564491 := by
    simpa [prefixWord, tailWord_564491, baseEnd_564491] using wordTrace_append hprefix tailTrace_564491
  have hstable : (prefixWord ++ tailWord_564491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564491).length < 2 ^ (prefixWord ++ tailWord_564491).sum := by decide
  have hdescent : baseEnd_564491 < baseStart_564491 := by decide
  rcases family_descends (prefixWord ++ tailWord_564491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564522 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_564522 : Nat := 118140960795 + 564522 * 2 ^ 59
def prefixEnd_564522 : Nat := 4983230072969 + 3 ^ 40 * 564522 * 2
def baseEnd_564522 : Nat := 289871126037545538778817

theorem tailTrace_564522 : CollatzResearch.WordTrace tailWord_564522 prefixEnd_564522 289871126037545538778817 := by
  unfold tailWord_564522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5147452215210170381725955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13726539240560454351269213 5147452215210170381725955)
  ·
    refine ⟨7721178322815255572588933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5147452215210170381725955 7721178322815255572588933)
    ·
      refine ⟨1447720935527860419860425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7721178322815255572588933 1447720935527860419860425)
      ·
        refine ⟨1085790701645895314895319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1447720935527860419860425 1085790701645895314895319)
        ·
          refine ⟨1628686052468842972342979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085790701645895314895319 1628686052468842972342979)
          ·
            refine ⟨2443029078703264458514469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628686052468842972342979 2443029078703264458514469)
            ·
              refine ⟨458067952256862085971463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2443029078703264458514469 458067952256862085971463)
              ·
                refine ⟨687101928385293128957195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458067952256862085971463 687101928385293128957195)
                ·
                  refine ⟨1030652892577939693435793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687101928385293128957195 1030652892577939693435793)
                  ·
                    refine ⟨772989669433454770076845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1030652892577939693435793 772989669433454770076845)
                    ·
                      refine ⟨289871126037545538778817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 772989669433454770076845 289871126037545538778817)
                      ·
                        rfl

theorem cell23_564522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_564522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564522 prefixEnd_564522 := by exact prefixLift 564522
  have htrace : WordTrace (prefixWord ++ tailWord_564522) baseStart_564522 baseEnd_564522 := by
    simpa [prefixWord, tailWord_564522, baseEnd_564522] using wordTrace_append hprefix tailTrace_564522
  have hstable : (prefixWord ++ tailWord_564522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564522).length < 2 ^ (prefixWord ++ tailWord_564522).sum := by decide
  have hdescent : baseEnd_564522 < baseStart_564522 := by decide
  rcases family_descends (prefixWord ++ tailWord_564522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564551 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 2, 6]
def baseStart_564551 : Nat := 118140960795 + 564551 * 2 ^ 59
def prefixEnd_564551 : Nat := 4983230072969 + 3 ^ 40 * 564551 * 2
def baseEnd_564551 : Nat := 96628672325508641772061

theorem tailTrace_564551 : CollatzResearch.WordTrace tailWord_564551 prefixEnd_564551 96628672325508641772061 := by
  unfold tailWord_564551
  simp only [CollatzResearch.WordTrace]
  refine ⟨20590866577735619479709507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13727244385157079653139671 20590866577735619479709507)
  ·
    refine ⟨30886299866603429219564261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20590866577735619479709507 30886299866603429219564261)
    ·
      refine ⟨5791181224988142978668299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30886299866603429219564261 5791181224988142978668299)
      ·
        refine ⟨8686771837482214468002449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5791181224988142978668299 8686771837482214468002449)
        ·
          refine ⟨6515078878111660851001837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8686771837482214468002449 6515078878111660851001837)
          ·
            refine ⟨2443154579291872819125689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6515078878111660851001837 2443154579291872819125689)
            ·
              refine ⟨1832365934468904614344267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2443154579291872819125689 1832365934468904614344267)
              ·
                refine ⟨2748548901703356921516401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832365934468904614344267 2748548901703356921516401)
                ·
                  refine ⟨2061411676277517691137301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2748548901703356921516401 2061411676277517691137301)
                  ·
                    refine ⟨96628672325508641772061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2061411676277517691137301 96628672325508641772061)
                    ·
                      rfl

theorem cell23_564551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_564551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564551 prefixEnd_564551 := by exact prefixLift 564551
  have htrace : WordTrace (prefixWord ++ tailWord_564551) baseStart_564551 baseEnd_564551 := by
    simpa [prefixWord, tailWord_564551, baseEnd_564551] using wordTrace_append hprefix tailTrace_564551
  have hstable : (prefixWord ++ tailWord_564551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564551).length < 2 ^ (prefixWord ++ tailWord_564551).sum := by decide
  have hdescent : baseEnd_564551 < baseStart_564551 := by decide
  rcases family_descends (prefixWord ++ tailWord_564551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564561 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_564561 : Nat := 118140960795 + 564561 * 2 ^ 59
def prefixEnd_564561 : Nat := 4983230072969 + 3 ^ 40 * 564561 * 2
def baseEnd_564561 : Nat := 289891151783070886191137

theorem tailTrace_564561 : CollatzResearch.WordTrace tailWord_564561 prefixEnd_564561 289891151783070886191137 := by
  unfold tailWord_564561
  simp only [CollatzResearch.WordTrace]
  refine ⟨20591231307699391187573537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13727487538466260791715691 20591231307699391187573537)
  ·
    refine ⟨15443423480774543390680153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20591231307699391187573537 15443423480774543390680153)
    ·
      refine ⟨11582567610580907543010115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15443423480774543390680153 11582567610580907543010115)
      ·
        refine ⟨17373851415871361314515173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11582567610580907543010115 17373851415871361314515173)
        ·
          refine ⟨3257597140475880246471595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17373851415871361314515173 3257597140475880246471595)
          ·
            refine ⟨4886395710713820369707393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3257597140475880246471595 4886395710713820369707393)
            ·
              refine ⟨3664796783035365277280545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4886395710713820369707393 3664796783035365277280545)
              ·
                refine ⟨2748597587276523957960409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3664796783035365277280545 2748597587276523957960409)
                ·
                  refine ⟨2061448190457392968470307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2748597587276523957960409 2061448190457392968470307)
                  ·
                    refine ⟨3092172285686089452705461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2061448190457392968470307 3092172285686089452705461)
                    ·
                      refine ⟨289891151783070886191137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3092172285686089452705461 289891151783070886191137)
                      ·
                        rfl

theorem cell23_564561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_564561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564561 prefixEnd_564561 := by exact prefixLift 564561
  have htrace : WordTrace (prefixWord ++ tailWord_564561) baseStart_564561 baseEnd_564561 := by
    simpa [prefixWord, tailWord_564561, baseEnd_564561] using wordTrace_append hprefix tailTrace_564561
  have hstable : (prefixWord ++ tailWord_564561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564561).length < 2 ^ (prefixWord ++ tailWord_564561).sum := by decide
  have hdescent : baseEnd_564561 < baseStart_564561 := by decide
  rcases family_descends (prefixWord ++ tailWord_564561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564578 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_564578 : Nat := 118140960795 + 564578 * 2 ^ 59
def prefixEnd_564578 : Nat := 4983230072969 + 3 ^ 40 * 564578 * 2
def baseEnd_564578 : Nat := 289899880954197319678559

theorem tailTrace_564578 : CollatzResearch.WordTrace tailWord_564578 prefixEnd_564578 289899880954197319678559 := by
  unfold tailWord_564578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5147962837159450772735597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13727900899091868727294925 5147962837159450772735597)
  ·
    refine ⟨1930486063934794039775849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5147962837159450772735597 1930486063934794039775849)
    ·
      refine ⟨1447864547951095529831887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1930486063934794039775849 1447864547951095529831887)
      ·
        refine ⟨2171796821926643294747831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1447864547951095529831887 2171796821926643294747831)
        ·
          refine ⟨3257695232889964942121747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2171796821926643294747831 3257695232889964942121747)
          ·
            refine ⟨4886542849334947413182621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3257695232889964942121747 4886542849334947413182621)
            ·
              refine ⟨1832453568500605279943483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4886542849334947413182621 1832453568500605279943483)
              ·
                refine ⟨2748680352750907919915225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832453568500605279943483 2748680352750907919915225)
                ·
                  refine ⟨2061510264563180939936419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2748680352750907919915225 2061510264563180939936419)
                  ·
                    refine ⟨3092265396844771409904629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2061510264563180939936419 3092265396844771409904629)
                    ·
                      refine ⟨289899880954197319678559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3092265396844771409904629 289899880954197319678559)
                      ·
                        rfl

theorem cell23_564578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_564578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564578 prefixEnd_564578 := by exact prefixLift 564578
  have htrace : WordTrace (prefixWord ++ tailWord_564578) baseStart_564578 baseEnd_564578 := by
    simpa [prefixWord, tailWord_564578, baseEnd_564578] using wordTrace_append hprefix tailTrace_564578
  have hstable : (prefixWord ++ tailWord_564578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564578).length < 2 ^ (prefixWord ++ tailWord_564578).sum := by decide
  have hdescent : baseEnd_564578 < baseStart_564578 := by decide
  rcases family_descends (prefixWord ++ tailWord_564578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564609 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_564609 : Nat := 118140960795 + 564609 * 2 ^ 59
def prefixEnd_564609 : Nat := 4983230072969 + 3 ^ 40 * 564609 * 2
def baseEnd_564609 : Nat := 289915798854486698390917

theorem tailTrace_564609 : CollatzResearch.WordTrace tailWord_564609 prefixEnd_564609 289915798854486698390917 := by
  unfold tailWord_564609
  simp only [CollatzResearch.WordTrace]
  refine ⟨20592982011525495385320881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13728654674350330256880587 20592982011525495385320881)
  ·
    refine ⟨15444736508644121538990661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20592982011525495385320881 15444736508644121538990661)
    ·
      refine ⟨2895888095370772788560749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15444736508644121538990661 2895888095370772788560749)
      ·
        refine ⟨1085958035764039795710281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2895888095370772788560749 1085958035764039795710281)
        ·
          refine ⟨814468526823029846782711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1085958035764039795710281 814468526823029846782711)
          ·
            refine ⟨1221702790234544770174067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814468526823029846782711 1221702790234544770174067)
            ·
              refine ⟨1832554185351817155261101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221702790234544770174067 1832554185351817155261101)
              ·
                refine ⟨687207819506931433222913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1832554185351817155261101 687207819506931433222913)
                ·
                  refine ⟨515405864630198574917185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 687207819506931433222913 515405864630198574917185)
                  ·
                    refine ⟨386554398472648931187889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 515405864630198574917185 386554398472648931187889)
                    ·
                      refine ⟨289915798854486698390917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 386554398472648931187889 289915798854486698390917)
                      ·
                        rfl

theorem cell23_564609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_564609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564609 prefixEnd_564609 := by exact prefixLift 564609
  have htrace : WordTrace (prefixWord ++ tailWord_564609) baseStart_564609 baseEnd_564609 := by
    simpa [prefixWord, tailWord_564609, baseEnd_564609] using wordTrace_append hprefix tailTrace_564609
  have hstable : (prefixWord ++ tailWord_564609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564609).length < 2 ^ (prefixWord ++ tailWord_564609).sum := by decide
  have hdescent : baseEnd_564609 < baseStart_564609 := by decide
  rcases family_descends (prefixWord ++ tailWord_564609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564705 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 6]
def baseStart_564705 : Nat := 118140960795 + 564705 * 2 ^ 59
def prefixEnd_564705 : Nat := 4983230072969 + 3 ^ 40 * 564705 * 2
def baseEnd_564705 : Nat := 32218343666368702532275

theorem tailTrace_564705 : CollatzResearch.WordTrace tailWord_564705 prefixEnd_564705 32218343666368702532275 := by
  unfold tailWord_564705
  simp only [CollatzResearch.WordTrace]
  refine ⟨20596483419177703780815569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13730988946118469187210379 20596483419177703780815569)
  ·
    refine ⟨15447362564383277835611677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20596483419177703780815569 15447362564383277835611677)
    ·
      refine ⟨5792760961643729188354379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15447362564383277835611677 5792760961643729188354379)
      ·
        refine ⟨8689141442465593782531569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5792760961643729188354379 8689141442465593782531569)
        ·
          refine ⟨6516856081849195336898677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8689141442465593782531569 6516856081849195336898677)
          ·
            refine ⟨610955257673362062834251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6516856081849195336898677 610955257673362062834251)
            ·
              refine ⟨916432886510043094251377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610955257673362062834251 916432886510043094251377)
              ·
                refine ⟨687324664882532320688533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916432886510043094251377 687324664882532320688533)
                ·
                  refine ⟨32218343666368702532275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 687324664882532320688533 32218343666368702532275)
                  ·
                    rfl

theorem cell23_564705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 6].length) (baseStart_564705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564705 prefixEnd_564705 := by exact prefixLift 564705
  have htrace : WordTrace (prefixWord ++ tailWord_564705) baseStart_564705 baseEnd_564705 := by
    simpa [prefixWord, tailWord_564705, baseEnd_564705] using wordTrace_append hprefix tailTrace_564705
  have hstable : (prefixWord ++ tailWord_564705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564705).length < 2 ^ (prefixWord ++ tailWord_564705).sum := by decide
  have hdescent : baseEnd_564705 < baseStart_564705 := by decide
  rcases family_descends (prefixWord ++ tailWord_564705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564722 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 6]
def baseStart_564722 : Nat := 118140960795 + 564722 * 2 ^ 59
def prefixEnd_564722 : Nat := 4983230072969 + 3 ^ 40 * 564722 * 2
def baseEnd_564722 : Nat := 32219313574271639586433

theorem tailTrace_564722 : CollatzResearch.WordTrace tailWord_564722 prefixEnd_564722 32219313574271639586433 := by
  unfold tailWord_564722
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149275865029028921046105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13731402306744077122789613 5149275865029028921046105)
  ·
    refine ⟨3861956898771771690784579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5149275865029028921046105 3861956898771771690784579)
    ·
      refine ⟨5792935348157657536176869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3861956898771771690784579 5792935348157657536176869)
      ·
        refine ⟨1086175377779560788033163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5792935348157657536176869 1086175377779560788033163)
        ·
          refine ⟨1629263066669341182049745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086175377779560788033163 1629263066669341182049745)
          ·
            refine ⟨1221947300002005886537309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1629263066669341182049745 1221947300002005886537309)
            ·
              refine ⟨458230237500752207451491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1221947300002005886537309 458230237500752207451491)
              ·
                refine ⟨687345356251128311177237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458230237500752207451491 687345356251128311177237)
                ·
                  refine ⟨32219313574271639586433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 687345356251128311177237 32219313574271639586433)
                  ·
                    rfl

theorem cell23_564722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_564722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564722 prefixEnd_564722 := by exact prefixLift 564722
  have htrace : WordTrace (prefixWord ++ tailWord_564722) baseStart_564722 baseEnd_564722 := by
    simpa [prefixWord, tailWord_564722, baseEnd_564722] using wordTrace_append hprefix tailTrace_564722
  have hstable : (prefixWord ++ tailWord_564722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564722).length < 2 ^ (prefixWord ++ tailWord_564722).sum := by decide
  have hdescent : baseEnd_564722 < baseStart_564722 := by decide
  rcases family_descends (prefixWord ++ tailWord_564722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564755 : List Nat := [1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 4]
def baseStart_564755 : Nat := 118140960795 + 564755 * 2 ^ 59
def prefixEnd_564755 : Nat := 4983230072969 + 3 ^ 40 * 564755 * 2
def baseEnd_564755 : Nat := 289990767030043127165245

theorem tailTrace_564755 : CollatzResearch.WordTrace tailWord_564755 prefixEnd_564755 289990767030043127165245 := by
  unfold tailWord_564755
  simp only [CollatzResearch.WordTrace]
  refine ⟨20598307068996562320135719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13732204712664374880090479 20598307068996562320135719)
  ·
    refine ⟨30897460603494843480203579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20598307068996562320135719 30897460603494843480203579)
    ·
      refine ⟨46346190905242265220305369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30897460603494843480203579 46346190905242265220305369)
      ·
        refine ⟨34759643178931698915229027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46346190905242265220305369 34759643178931698915229027)
        ·
          refine ⟨52139464768397548372843541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34759643178931698915229027 52139464768397548372843541)
          ·
            refine ⟨2444037411018635079977041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52139464768397548372843541 2444037411018635079977041)
            ·
              refine ⟨1833028058263976309982781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2444037411018635079977041 1833028058263976309982781)
              ·
                refine ⟨687385521848991116243543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1833028058263976309982781 687385521848991116243543)
                ·
                  refine ⟨1031078282773486674365315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687385521848991116243543 1031078282773486674365315)
                  ·
                    refine ⟨1546617424160230011547973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1031078282773486674365315 1546617424160230011547973)
                    ·
                      refine ⟨289990767030043127165245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1546617424160230011547973 289990767030043127165245)
                      ·
                        rfl

theorem cell23_564755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 4].length) (baseStart_564755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564755 prefixEnd_564755 := by exact prefixLift 564755
  have htrace : WordTrace (prefixWord ++ tailWord_564755) baseStart_564755 baseEnd_564755 := by
    simpa [prefixWord, tailWord_564755, baseEnd_564755] using wordTrace_append hprefix tailTrace_564755
  have hstable : (prefixWord ++ tailWord_564755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564755).length < 2 ^ (prefixWord ++ tailWord_564755).sum := by decide
  have hdescent : baseEnd_564755 < baseStart_564755 := by decide
  rcases family_descends (prefixWord ++ tailWord_564755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564765 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_564765 : Nat := 118140960795 + 564765 * 2 ^ 59
def prefixEnd_564765 : Nat := 4983230072969 + 3 ^ 40 * 564765 * 2
def baseEnd_564765 : Nat := 96665300612196029346733

theorem tailTrace_564765 : CollatzResearch.WordTrace tailWord_564765 prefixEnd_564765 96665300612196029346733 := by
  unfold tailWord_564765
  simp only [CollatzResearch.WordTrace]
  refine ⟨20598671798960334027999749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13732447865973556018666499 20598671798960334027999749)
  ·
    refine ⟨3862250962305062630249953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20598671798960334027999749 3862250962305062630249953)
    ·
      refine ⟨2896688221728796972687465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3862250962305062630249953 2896688221728796972687465)
      ·
        refine ⟨2172516166296597729515599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2896688221728796972687465 2172516166296597729515599)
        ·
          refine ⟨3258774249444896594273399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172516166296597729515599 3258774249444896594273399)
          ·
            refine ⟨4888161374167344891410099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258774249444896594273399 4888161374167344891410099)
            ·
              refine ⟨7332242061251017337115149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4888161374167344891410099 7332242061251017337115149)
              ·
                refine ⟨2749590772969131501418181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7332242061251017337115149 2749590772969131501418181)
                ·
                  refine ⟨515548269931712156515909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2749590772969131501418181 515548269931712156515909)
                  ·
                    refine ⟨96665300612196029346733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 515548269931712156515909 96665300612196029346733)
                    ·
                      rfl

theorem cell23_564765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_564765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564765 prefixEnd_564765 := by exact prefixLift 564765
  have htrace : WordTrace (prefixWord ++ tailWord_564765) baseStart_564765 baseEnd_564765 := by
    simpa [prefixWord, tailWord_564765, baseEnd_564765] using wordTrace_append hprefix tailTrace_564765
  have hstable : (prefixWord ++ tailWord_564765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564765).length < 2 ^ (prefixWord ++ tailWord_564765).sum := by decide
  have hdescent : baseEnd_564765 < baseStart_564765 := by decide
  rcases family_descends (prefixWord ++ tailWord_564765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564792 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 1, 2, 3]
def baseStart_564792 : Nat := 118140960795 + 564792 * 2 ^ 59
def prefixEnd_564792 : Nat := 4983230072969 + 3 ^ 40 * 564792 * 2
def baseEnd_564792 : Nat := 290009765814259482402575

theorem tailTrace_564792 : CollatzResearch.WordTrace tailWord_564792 prefixEnd_564792 290009765814259482402575 := by
  unfold tailWord_564792
  simp only [CollatzResearch.WordTrace]
  refine ⟨10299828284931258819616315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13733104379908345092821753 10299828284931258819616315)
  ·
    refine ⟨15449742427396888229424473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10299828284931258819616315 15449742427396888229424473)
    ·
      refine ⟨11587306820547666172068355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15449742427396888229424473 11587306820547666172068355)
      ·
        refine ⟨17380960230821499258102533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11587306820547666172068355 17380960230821499258102533)
        ·
          refine ⟨3258930043279031110894225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17380960230821499258102533 3258930043279031110894225)
          ·
            refine ⟨2444197532459273333170669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3258930043279031110894225 2444197532459273333170669)
            ·
              refine ⟨916574074672227499939001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2444197532459273333170669 916574074672227499939001)
              ·
                refine ⟨687430556004170624954251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916574074672227499939001 687430556004170624954251)
                ·
                  refine ⟨1031145834006255937431377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687430556004170624954251 1031145834006255937431377)
                  ·
                    refine ⟨773359375504691953073533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1031145834006255937431377 773359375504691953073533)
                    ·
                      refine ⟨290009765814259482402575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 773359375504691953073533 290009765814259482402575)
                      ·
                        rfl

theorem cell23_564792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 1, 2, 3].length) (baseStart_564792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564792 prefixEnd_564792 := by exact prefixLift 564792
  have htrace : WordTrace (prefixWord ++ tailWord_564792) baseStart_564792 baseEnd_564792 := by
    simpa [prefixWord, tailWord_564792, baseEnd_564792] using wordTrace_append hprefix tailTrace_564792
  have hstable : (prefixWord ++ tailWord_564792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564792).length < 2 ^ (prefixWord ++ tailWord_564792).sum := by decide
  have hdescent : baseEnd_564792 < baseStart_564792 := by decide
  rcases family_descends (prefixWord ++ tailWord_564792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564805 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_564805 : Nat := 118140960795 + 564805 * 2 ^ 59
def prefixEnd_564805 : Nat := 4983230072969 + 3 ^ 40 * 564805 * 2
def baseEnd_564805 : Nat := 290016441062767931540015

theorem tailTrace_564805 : CollatzResearch.WordTrace tailWord_564805 prefixEnd_564805 290016441062767931540015 := by
  unfold tailWord_564805
  simp only [CollatzResearch.WordTrace]
  refine ⟨20600130718815420859455869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13733420479210280572970579 20600130718815420859455869)
  ·
    refine ⟨7725049019555782822295951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20600130718815420859455869 7725049019555782822295951)
    ·
      refine ⟨11587573529333674233443927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7725049019555782822295951 11587573529333674233443927)
      ·
        refine ⟨17381360294000511350165891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11587573529333674233443927 17381360294000511350165891)
        ·
          refine ⟨26072040441000767025248837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17381360294000511350165891 26072040441000767025248837)
          ·
            refine ⟨4888507582687643817234157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26072040441000767025248837 4888507582687643817234157)
            ·
              refine ⟨1833190343507866431462809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4888507582687643817234157 1833190343507866431462809)
              ·
                refine ⟨1374892757630899823597107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833190343507866431462809 1374892757630899823597107)
                ·
                  refine ⟨2062339136446349735395661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1374892757630899823597107 2062339136446349735395661)
                  ·
                    refine ⟨773377176167381150773373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2062339136446349735395661 773377176167381150773373)
                    ·
                      refine ⟨290016441062767931540015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 773377176167381150773373 290016441062767931540015)
                      ·
                        rfl

theorem cell23_564805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_564805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564805 prefixEnd_564805 := by exact prefixLift 564805
  have htrace : WordTrace (prefixWord ++ tailWord_564805) baseStart_564805 baseEnd_564805 := by
    simpa [prefixWord, tailWord_564805, baseEnd_564805] using wordTrace_append hprefix tailTrace_564805
  have hstable : (prefixWord ++ tailWord_564805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564805).length < 2 ^ (prefixWord ++ tailWord_564805).sum := by decide
  have hdescent : baseEnd_564805 < baseStart_564805 := by decide
  rcases family_descends (prefixWord ++ tailWord_564805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564823 : List Nat := [1, 1, 3, 2, 2, 5, 2, 2, 1, 2, 2]
def baseStart_564823 : Nat := 118140960795 + 564823 * 2 ^ 59
def prefixEnd_564823 : Nat := 4983230072969 + 3 ^ 40 * 564823 * 2
def baseEnd_564823 : Nat := 290025683714548861114933

theorem tailTrace_564823 : CollatzResearch.WordTrace tailWord_564823 prefixEnd_564823 290025683714548861114933 := by
  unfold tailWord_564823
  simp only [CollatzResearch.WordTrace]
  refine ⟨20600787232750209933611123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13733858155166806622407415 20600787232750209933611123)
  ·
    refine ⟨30901180849125314900416685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20600787232750209933611123 30901180849125314900416685)
    ·
      refine ⟨11587942818421993087656257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30901180849125314900416685 11587942818421993087656257)
      ·
        refine ⟨8690957113816494815742193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11587942818421993087656257 8690957113816494815742193)
        ·
          refine ⟨6518217835362371111806645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8690957113816494815742193 6518217835362371111806645)
          ·
            refine ⟨611082922065222291731873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6518217835362371111806645 611082922065222291731873)
            ·
              refine ⟨458312191548916718798905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611082922065222291731873 458312191548916718798905)
              ·
                refine ⟨343734143661687539099179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458312191548916718798905 343734143661687539099179)
                ·
                  refine ⟨515601215492531308648769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343734143661687539099179 515601215492531308648769)
                  ·
                    refine ⟨386700911619398481486577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 515601215492531308648769 386700911619398481486577)
                    ·
                      refine ⟨290025683714548861114933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 386700911619398481486577 290025683714548861114933)
                      ·
                        rfl

theorem cell23_564823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_564823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564823 prefixEnd_564823 := by exact prefixLift 564823
  have htrace : WordTrace (prefixWord ++ tailWord_564823) baseStart_564823 baseEnd_564823 := by
    simpa [prefixWord, tailWord_564823, baseEnd_564823] using wordTrace_append hprefix tailTrace_564823
  have hstable : (prefixWord ++ tailWord_564823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564823).length < 2 ^ (prefixWord ++ tailWord_564823).sum := by decide
  have hdescent : baseEnd_564823 < baseStart_564823 := by decide
  rcases family_descends (prefixWord ++ tailWord_564823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564829 : List Nat := [1, 4, 4, 2, 1, 2, 1, 8]
def baseStart_564829 : Nat := 118140960795 + 564829 * 2 ^ 59
def prefixEnd_564829 : Nat := 4983230072969 + 3 ^ 40 * 564829 * 2
def baseEnd_564829 : Nat := 10741806096239845838515

theorem tailTrace_564829 : CollatzResearch.WordTrace tailWord_564829 prefixEnd_564829 10741806096239845838515 := by
  unfold tailWord_564829
  simp only [CollatzResearch.WordTrace]
  refine ⟨20601006070728472958329541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13734004047152315305553027 20601006070728472958329541)
  ·
    refine ⟨3862688638261588679686789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20601006070728472958329541 3862688638261588679686789)
    ·
      refine ⟨724254119674047877441273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3862688638261588679686789 724254119674047877441273)
      ·
        refine ⟨543190589755535908080955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 724254119674047877441273 543190589755535908080955)
        ·
          refine ⟨814785884633303862121433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543190589755535908080955 814785884633303862121433)
          ·
            refine ⟨611089413474977896591075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 814785884633303862121433 611089413474977896591075)
            ·
              refine ⟨916634120212466844886613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611089413474977896591075 916634120212466844886613)
              ·
                refine ⟨10741806096239845838515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 916634120212466844886613 10741806096239845838515)
                ·
                  rfl

theorem cell23_564829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 8].length) (baseStart_564829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564829 prefixEnd_564829 := by exact prefixLift 564829
  have htrace : WordTrace (prefixWord ++ tailWord_564829) baseStart_564829 baseEnd_564829 := by
    simpa [prefixWord, tailWord_564829, baseEnd_564829] using wordTrace_append hprefix tailTrace_564829
  have hstable : (prefixWord ++ tailWord_564829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564829).length < 2 ^ (prefixWord ++ tailWord_564829).sum := by decide
  have hdescent : baseEnd_564829 < baseStart_564829 := by decide
  rcases family_descends (prefixWord ++ tailWord_564829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564915 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 2, 5]
def baseStart_564915 : Nat := 118140960795 + 564915 * 2 ^ 59
def prefixEnd_564915 : Nat := 4983230072969 + 3 ^ 40 * 564915 * 2
def baseEnd_564915 : Nat := 96690974644920833721503

theorem tailTrace_564915 : CollatzResearch.WordTrace tailWord_564915 prefixEnd_564915 96690974644920833721503 := by
  unfold tailWord_564915
  simp only [CollatzResearch.WordTrace]
  refine ⟨20604142748416909645960199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13736095165611273097306799 20604142748416909645960199)
  ·
    refine ⟨30906214122625364468940299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20604142748416909645960199 30906214122625364468940299)
    ·
      refine ⟨46359321183938046703410449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30906214122625364468940299 46359321183938046703410449)
      ·
        refine ⟨34769490887953535027557837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46359321183938046703410449 34769490887953535027557837)
        ·
          refine ⟨13038559082982575635334189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34769490887953535027557837 13038559082982575635334189)
          ·
            refine ⟨4889459656118465863250321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13038559082982575635334189 4889459656118465863250321)
            ·
              refine ⟨3667094742088849397437741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4889459656118465863250321 3667094742088849397437741)
              ·
                refine ⟨1375160528283318524039153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3667094742088849397437741 1375160528283318524039153)
                ·
                  refine ⟨1031370396212488893029365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1375160528283318524039153 1031370396212488893029365)
                  ·
                    refine ⟨96690974644920833721503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1031370396212488893029365 96690974644920833721503)
                    ·
                      rfl

theorem cell23_564915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 5].length) (baseStart_564915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564915 prefixEnd_564915 := by exact prefixLift 564915
  have htrace : WordTrace (prefixWord ++ tailWord_564915) baseStart_564915 baseEnd_564915 := by
    simpa [prefixWord, tailWord_564915, baseEnd_564915] using wordTrace_append hprefix tailTrace_564915
  have hstable : (prefixWord ++ tailWord_564915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564915).length < 2 ^ (prefixWord ++ tailWord_564915).sum := by decide
  have hdescent : baseEnd_564915 < baseStart_564915 := by decide
  rcases family_descends (prefixWord ++ tailWord_564915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564919 : List Nat := [1, 1, 3, 1, 5, 3, 1, 3, 5]
def baseStart_564919 : Nat := 118140960795 + 564919 * 2 ^ 59
def prefixEnd_564919 : Nat := 4983230072969 + 3 ^ 40 * 564919 * 2
def baseEnd_564919 : Nat := 32230553095264498390499

theorem tailTrace_564919 : CollatzResearch.WordTrace tailWord_564919 prefixEnd_564919 32230553095264498390499 := by
  unfold tailWord_564919
  simp only [CollatzResearch.WordTrace]
  refine ⟨20604288640402418329105811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13736192426934945552737207 20604288640402418329105811)
  ·
    refine ⟨30906432960603627493658717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20604288640402418329105811 30906432960603627493658717)
    ·
      refine ⟨11589912360226360310122019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30906432960603627493658717 11589912360226360310122019)
      ·
        refine ⟨17384868540339540465183029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11589912360226360310122019 17384868540339540465183029)
        ·
          refine ⟨1629831425656831918610909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17384868540339540465183029 1629831425656831918610909)
          ·
            refine ⟨611186784621311969479091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1629831425656831918610909 611186784621311969479091)
            ·
              refine ⟨916780176931967954218637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611186784621311969479091 916780176931967954218637)
              ·
                refine ⟨343792566349487982831989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 916780176931967954218637 343792566349487982831989)
                ·
                  refine ⟨32230553095264498390499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 343792566349487982831989 32230553095264498390499)
                  ·
                    rfl

theorem cell23_564919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 3, 5].length) (baseStart_564919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564919 prefixEnd_564919 := by exact prefixLift 564919
  have htrace : WordTrace (prefixWord ++ tailWord_564919) baseStart_564919 baseEnd_564919 := by
    simpa [prefixWord, tailWord_564919, baseEnd_564919] using wordTrace_append hprefix tailTrace_564919
  have hstable : (prefixWord ++ tailWord_564919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564919).length < 2 ^ (prefixWord ++ tailWord_564919).sum := by decide
  have hdescent : baseEnd_564919 < baseStart_564919 := by decide
  rcases family_descends (prefixWord ++ tailWord_564919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564925 : List Nat := [1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_564925 : Nat := 118140960795 + 564925 * 2 ^ 59
def prefixEnd_564925 : Nat := 4983230072969 + 3 ^ 40 * 564925 * 2
def baseEnd_564925 : Nat := 290078058741307462039463

theorem tailTrace_564925 : CollatzResearch.WordTrace tailWord_564925 prefixEnd_564925 290078058741307462039463 := by
  unfold tailWord_564925
  simp only [CollatzResearch.WordTrace]
  refine ⟨20604507478380681353824229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13736338318920454235882819 20604507478380681353824229)
  ·
    refine ⟨3863345152196377753842043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20604507478380681353824229 3863345152196377753842043)
    ·
      refine ⟨5795017728294566630763065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3863345152196377753842043 5795017728294566630763065)
      ·
        refine ⟨4346263296220924973072299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5795017728294566630763065 4346263296220924973072299)
        ·
          refine ⟨6519394944331387459608449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346263296220924973072299 6519394944331387459608449)
          ·
            refine ⟨4889546208248540594706337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6519394944331387459608449 4889546208248540594706337)
            ·
              refine ⟨3667159656186405446029753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4889546208248540594706337 3667159656186405446029753)
              ·
                refine ⟨2750369742139804084522315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3667159656186405446029753 2750369742139804084522315)
                ·
                  refine ⟨4125554613209706126783473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750369742139804084522315 4125554613209706126783473)
                  ·
                    refine ⟨3094165959907279595087605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4125554613209706126783473 3094165959907279595087605)
                    ·
                      refine ⟨290078058741307462039463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3094165959907279595087605 290078058741307462039463)
                      ·
                        rfl

theorem cell23_564925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_564925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564925 prefixEnd_564925 := by exact prefixLift 564925
  have htrace : WordTrace (prefixWord ++ tailWord_564925) baseStart_564925 baseEnd_564925 := by
    simpa [prefixWord, tailWord_564925, baseEnd_564925] using wordTrace_append hprefix tailTrace_564925
  have hstable : (prefixWord ++ tailWord_564925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564925).length < 2 ^ (prefixWord ++ tailWord_564925).sum := by decide
  have hdescent : baseEnd_564925 < baseStart_564925 := by decide
  rcases family_descends (prefixWord ++ tailWord_564925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564932 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 2, 5]
def baseStart_564932 : Nat := 118140960795 + 564932 * 2 ^ 59
def prefixEnd_564932 : Nat := 4983230072969 + 3 ^ 40 * 564932 * 2
def baseEnd_564932 : Nat := 96693884368629644883977

theorem tailTrace_564932 : CollatzResearch.WordTrace tailWord_564932 prefixEnd_564932 96693884368629644883977 := by
  unfold tailWord_564932
  simp only [CollatzResearch.WordTrace]
  refine ⟨10302381394677660774664525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13736508526236881032886033 10302381394677660774664525)
  ·
    refine ⟨3863393023004122790499197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10302381394677660774664525 3863393023004122790499197)
    ·
      refine ⟨1448772383626546046437199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3863393023004122790499197 1448772383626546046437199)
      ·
        refine ⟨2173158575439819069655799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448772383626546046437199 2173158575439819069655799)
        ·
          refine ⟨3259737863159728604483699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173158575439819069655799 3259737863159728604483699)
          ·
            refine ⟨4889606794739592906725549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259737863159728604483699 4889606794739592906725549)
            ·
              refine ⟨1833602548027347340022081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4889606794739592906725549 1833602548027347340022081)
              ·
                refine ⟨1375201911020510505016561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833602548027347340022081 1375201911020510505016561)
                ·
                  refine ⟨1031401433265382878762421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1375201911020510505016561 1031401433265382878762421)
                  ·
                    refine ⟨96693884368629644883977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1031401433265382878762421 96693884368629644883977)
                    ·
                      rfl

theorem cell23_564932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_564932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564932 prefixEnd_564932 := by exact prefixLift 564932
  have htrace : WordTrace (prefixWord ++ tailWord_564932) baseStart_564932 baseEnd_564932 := by
    simpa [prefixWord, tailWord_564932, baseEnd_564932] using wordTrace_append hprefix tailTrace_564932
  have hstable : (prefixWord ++ tailWord_564932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564932).length < 2 ^ (prefixWord ++ tailWord_564932).sum := by decide
  have hdescent : baseEnd_564932 < baseStart_564932 := by decide
  rcases family_descends (prefixWord ++ tailWord_564932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564952 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 1, 6, 2]
def baseStart_564952 : Nat := 118140960795 + 564952 * 2 ^ 59
def prefixEnd_564952 : Nat := 4983230072969 + 3 ^ 40 * 564952 * 2
def baseEnd_564952 : Nat := 290091922718978856401839

theorem tailTrace_564952 : CollatzResearch.WordTrace tailWord_564952 prefixEnd_564952 290091922718978856401839 := by
  unfold tailWord_564952
  simp only [CollatzResearch.WordTrace]
  refine ⟨10302746124641432482528555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13736994832855243310038073 10302746124641432482528555)
  ·
    refine ⟨15454119186962148723792833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10302746124641432482528555 15454119186962148723792833)
    ·
      refine ⟨11590589390221611542844625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15454119186962148723792833 11590589390221611542844625)
      ·
        refine ⟨8692942042666208657133469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11590589390221611542844625 8692942042666208657133469)
        ·
          refine ⟨3259853265999828246425051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8692942042666208657133469 3259853265999828246425051)
          ·
            refine ⟨4889779898999742369637577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259853265999828246425051 4889779898999742369637577)
            ·
              refine ⟨3667334924249806777228183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4889779898999742369637577 3667334924249806777228183)
              ·
                refine ⟨5501002386374710165842275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3667334924249806777228183 5501002386374710165842275)
                ·
                  refine ⟨8251503579562065248763413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5501002386374710165842275 8251503579562065248763413)
                  ·
                    refine ⟨386789230291971808535785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8251503579562065248763413 386789230291971808535785)
                    ·
                      refine ⟨290091922718978856401839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 386789230291971808535785 290091922718978856401839)
                      ·
                        rfl

theorem cell23_564952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_564952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564952 prefixEnd_564952 := by exact prefixLift 564952
  have htrace : WordTrace (prefixWord ++ tailWord_564952) baseStart_564952 baseEnd_564952 := by
    simpa [prefixWord, tailWord_564952, baseEnd_564952] using wordTrace_append hprefix tailTrace_564952
  have hstable : (prefixWord ++ tailWord_564952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564952).length < 2 ^ (prefixWord ++ tailWord_564952).sum := by decide
  have hdescent : baseEnd_564952 < baseStart_564952 := by decide
  rcases family_descends (prefixWord ++ tailWord_564952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564972 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_564972 : Nat := 118140960795 + 564972 * 2 ^ 59
def prefixEnd_564972 : Nat := 4983230072969 + 3 ^ 40 * 564972 * 2
def baseEnd_564972 : Nat := 290102192332068778151747

theorem tailTrace_564972 : CollatzResearch.WordTrace tailWord_564972 prefixEnd_564972 290102192332068778151747 := by
  unfold tailWord_564972
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303110854605204190392585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13737481139473605587190113 10303110854605204190392585)
  ·
    refine ⟨7727333140953903142794439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10303110854605204190392585 7727333140953903142794439)
    ·
      refine ⟨11590999711430854714191659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7727333140953903142794439 11590999711430854714191659)
      ·
        refine ⟨17386499567146282071287489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11590999711430854714191659 17386499567146282071287489)
        ·
          refine ⟨13039874675359711553465617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17386499567146282071287489 13039874675359711553465617)
          ·
            refine ⟨9779906006519783665099213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13039874675359711553465617 9779906006519783665099213)
            ·
              refine ⟨3667464752444918874412205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9779906006519783665099213 3667464752444918874412205)
              ·
                refine ⟨1375299282166844577904577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3667464752444918874412205 1375299282166844577904577)
                ·
                  refine ⟨1031474461625133433428433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1375299282166844577904577 1031474461625133433428433)
                  ·
                    refine ⟨773605846218850075071325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1031474461625133433428433 773605846218850075071325)
                    ·
                      refine ⟨290102192332068778151747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 773605846218850075071325 290102192332068778151747)
                      ·
                        rfl

theorem cell23_564972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_564972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564972 prefixEnd_564972 := by exact prefixLift 564972
  have htrace : WordTrace (prefixWord ++ tailWord_564972) baseStart_564972 baseEnd_564972 := by
    simpa [prefixWord, tailWord_564972, baseEnd_564972] using wordTrace_append hprefix tailTrace_564972
  have hstable : (prefixWord ++ tailWord_564972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564972).length < 2 ^ (prefixWord ++ tailWord_564972).sum := by decide
  have hdescent : baseEnd_564972 < baseStart_564972 := by decide
  rcases family_descends (prefixWord ++ tailWord_564972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_564996 : List Nat := [2, 3, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_564996 : Nat := 118140960795 + 564996 * 2 ^ 59
def prefixEnd_564996 : Nat := 4983230072969 + 3 ^ 40 * 564996 * 2
def baseEnd_564996 : Nat := 96704838622592228083879

theorem tailTrace_564996 : CollatzResearch.WordTrace tailWord_564996 prefixEnd_564996 96704838622592228083879 := by
  unfold tailWord_564996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10303548530561730239829421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13738064707415640319772561 10303548530561730239829421)
  ·
    refine ⟨3863830698960648839936033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10303548530561730239829421 3863830698960648839936033)
    ·
      refine ⟨2897873024220486629952025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3863830698960648839936033 2897873024220486629952025)
      ·
        refine ⟨2173404768165364972464019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2897873024220486629952025 2173404768165364972464019)
        ·
          refine ⟨3260107152248047458696029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2173404768165364972464019 3260107152248047458696029)
          ·
            refine ⟨1222540182093017797011011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3260107152248047458696029 1222540182093017797011011)
            ·
              refine ⟨1833810273139526695516517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222540182093017797011011 1833810273139526695516517)
              ·
                refine ⟨343839426213661255409347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1833810273139526695516517 343839426213661255409347)
                ·
                  refine ⟨515759139320491883114021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343839426213661255409347 515759139320491883114021)
                  ·
                    refine ⟨96704838622592228083879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 515759139320491883114021 96704838622592228083879)
                    ·
                      rfl

theorem cell23_564996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_564996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_564996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_564996 prefixEnd_564996 := by exact prefixLift 564996
  have htrace : WordTrace (prefixWord ++ tailWord_564996) baseStart_564996 baseEnd_564996 := by
    simpa [prefixWord, tailWord_564996, baseEnd_564996] using wordTrace_append hprefix tailTrace_564996
  have hstable : (prefixWord ++ tailWord_564996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_564996).length < 2 ^ (prefixWord ++ tailWord_564996).sum := by decide
  have hdescent : baseEnd_564996 < baseStart_564996 := by decide
  rcases family_descends (prefixWord ++ tailWord_564996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565029 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 1, 5, 2]
def baseStart_565029 : Nat := 118140960795 + 565029 * 2 ^ 59
def prefixEnd_565029 : Nat := 4983230072969 + 3 ^ 40 * 565029 * 2
def baseEnd_565029 : Nat := 290131460729375055138985

theorem tailTrace_565029 : CollatzResearch.WordTrace tailWord_565029 prefixEnd_565029 290131460729375055138985 := by
  unfold tailWord_565029
  simp only [CollatzResearch.WordTrace]
  refine ⟨20608300670003907115610141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13738867113335938077073427 20608300670003907115610141)
  ·
    refine ⟨7728112751251465168353803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20608300670003907115610141 7728112751251465168353803)
    ·
      refine ⟨11592169126877197752530705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7728112751251465168353803 11592169126877197752530705)
      ·
        refine ⟨8694126845157898314398029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11592169126877197752530705 8694126845157898314398029)
        ·
          refine ⟨3260297566934211867899261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8694126845157898314398029 3260297566934211867899261)
          ·
            refine ⟨1222611587600329450462223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3260297566934211867899261 1222611587600329450462223)
            ·
              refine ⟨1833917381400494175693335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222611587600329450462223 1833917381400494175693335)
              ·
                refine ⟨2750876072100741263540003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1833917381400494175693335 2750876072100741263540003)
                ·
                  refine ⟨4126314108151111895310005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2750876072100741263540003 4126314108151111895310005)
                  ·
                    refine ⟨386841947639166740185313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4126314108151111895310005 386841947639166740185313)
                    ·
                      refine ⟨290131460729375055138985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 386841947639166740185313 290131460729375055138985)
                      ·
                        rfl

theorem cell23_565029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_565029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565029 prefixEnd_565029 := by exact prefixLift 565029
  have htrace : WordTrace (prefixWord ++ tailWord_565029) baseStart_565029 baseEnd_565029 := by
    simpa [prefixWord, tailWord_565029, baseEnd_565029] using wordTrace_append hprefix tailTrace_565029
  have hstable : (prefixWord ++ tailWord_565029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565029).length < 2 ^ (prefixWord ++ tailWord_565029).sum := by decide
  have hdescent : baseEnd_565029 < baseStart_565029 := by decide
  rcases family_descends (prefixWord ++ tailWord_565029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565036 : List Nat := [2, 2, 1, 1, 1, 5, 1, 5, 1, 1, 3]
def baseStart_565036 : Nat := 118140960795 + 565036 * 2 ^ 59
def prefixEnd_565036 : Nat := 4983230072969 + 3 ^ 40 * 565036 * 2
def baseEnd_565036 : Nat := 290135055093956527751453

theorem tailTrace_565036 : CollatzResearch.WordTrace tailWord_565036 prefixEnd_565036 290135055093956527751453 := by
  unfold tailWord_565036
  simp only [CollatzResearch.WordTrace]
  refine ⟨10304277990489273655557481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13739037320652364874076641 10304277990489273655557481)
  ·
    refine ⟨7728208492866955241668111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10304277990489273655557481 7728208492866955241668111)
    ·
      refine ⟨11592312739300432862502167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7728208492866955241668111 11592312739300432862502167)
      ·
        refine ⟨17388469108950649293753251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11592312739300432862502167 17388469108950649293753251)
        ·
          refine ⟨26082703663425973940629877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17388469108950649293753251 26082703663425973940629877)
          ·
            refine ⟨2445253468446185056934051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26082703663425973940629877 2445253468446185056934051)
            ·
              refine ⟨3667880202669277585401077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445253468446185056934051 3667880202669277585401077)
              ·
                refine ⟨343863769000244773631351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3667880202669277585401077 343863769000244773631351)
                ·
                  refine ⟨515795653500367160447027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343863769000244773631351 515795653500367160447027)
                  ·
                    refine ⟨773693480250550740670541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 515795653500367160447027 773693480250550740670541)
                    ·
                      refine ⟨290135055093956527751453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 773693480250550740670541 290135055093956527751453)
                      ·
                        rfl

theorem cell23_565036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 1, 1, 3].length) (baseStart_565036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565036 prefixEnd_565036 := by exact prefixLift 565036
  have htrace : WordTrace (prefixWord ++ tailWord_565036) baseStart_565036 baseEnd_565036 := by
    simpa [prefixWord, tailWord_565036, baseEnd_565036] using wordTrace_append hprefix tailTrace_565036
  have hstable : (prefixWord ++ tailWord_565036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565036).length < 2 ^ (prefixWord ++ tailWord_565036).sum := by decide
  have hdescent : baseEnd_565036 < baseStart_565036 := by decide
  rcases family_descends (prefixWord ++ tailWord_565036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565053 : List Nat := [1, 4, 1, 4, 1, 1, 2, 4, 1, 1, 3]
def baseStart_565053 : Nat := 118140960795 + 565053 * 2 ^ 59
def prefixEnd_565053 : Nat := 4983230072969 + 3 ^ 40 * 565053 * 2
def baseEnd_565053 : Nat := 290143784265082961238875

theorem tailTrace_565053 : CollatzResearch.WordTrace tailWord_565053 prefixEnd_565053 290143784265082961238875 := by
  unfold tailWord_565053
  simp only [CollatzResearch.WordTrace]
  refine ⟨20609176021916959214483813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13739450681277972809655875 20609176021916959214483813)
  ·
    refine ⟨3864220504109429852715715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20609176021916959214483813 3864220504109429852715715)
    ·
      refine ⟨5796330756164144779073573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3864220504109429852715715 5796330756164144779073573)
      ·
        refine ⟨1086812016780777146076295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5796330756164144779073573 1086812016780777146076295)
        ·
          refine ⟨1630218025171165719114443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086812016780777146076295 1630218025171165719114443)
          ·
            refine ⟨2445327037756748578671665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630218025171165719114443 2445327037756748578671665)
            ·
              refine ⟨1833995278317561434003749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2445327037756748578671665 1833995278317561434003749)
              ·
                refine ⟨343874114684542768875703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1833995278317561434003749 343874114684542768875703)
                ·
                  refine ⟨515811172026814153313555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343874114684542768875703 515811172026814153313555)
                  ·
                    refine ⟨773716758040221229970333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 515811172026814153313555 773716758040221229970333)
                    ·
                      refine ⟨290143784265082961238875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 773716758040221229970333 290143784265082961238875)
                      ·
                        rfl

theorem cell23_565053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_565053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565053 prefixEnd_565053 := by exact prefixLift 565053
  have htrace : WordTrace (prefixWord ++ tailWord_565053) baseStart_565053 baseEnd_565053 := by
    simpa [prefixWord, tailWord_565053, baseEnd_565053] using wordTrace_append hprefix tailTrace_565053
  have hstable : (prefixWord ++ tailWord_565053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565053).length < 2 ^ (prefixWord ++ tailWord_565053).sum := by decide
  have hdescent : baseEnd_565053 < baseStart_565053 := by decide
  rcases family_descends (prefixWord ++ tailWord_565053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565065 : List Nat := [1, 2, 1, 1, 2, 4, 2, 10]
def baseStart_565065 : Nat := 118140960795 + 565065 * 2 ^ 59
def prefixEnd_565065 : Nat := 4983230072969 + 3 ^ 40 * 565065 * 2
def baseEnd_565065 : Nat := 10746294297516182010697

theorem tailTrace_565065 : CollatzResearch.WordTrace tailWord_565065 prefixEnd_565065 10746294297516182010697 := by
  unfold tailWord_565065
  simp only [CollatzResearch.WordTrace]
  refine ⟨20609613697873485263920649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13739742465248990175947099 20609613697873485263920649)
  ·
    refine ⟨15457210273405113947940487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20609613697873485263920649 15457210273405113947940487)
    ·
      refine ⟨23185815410107670921910731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15457210273405113947940487 23185815410107670921910731)
      ·
        refine ⟨34778723115161506382866097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23185815410107670921910731 34778723115161506382866097)
        ·
          refine ⟨26084042336371129787149573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34778723115161506382866097 26084042336371129787149573)
          ·
            refine ⟨4890757938069586835090545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26084042336371129787149573 4890757938069586835090545)
            ·
              refine ⟨3668068453552190126317909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4890757938069586835090545 3668068453552190126317909)
              ·
                refine ⟨10746294297516182010697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3668068453552190126317909 10746294297516182010697)
                ·
                  rfl

theorem cell23_565065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 10].length) (baseStart_565065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565065 prefixEnd_565065 := by exact prefixLift 565065
  have htrace : WordTrace (prefixWord ++ tailWord_565065) baseStart_565065 baseEnd_565065 := by
    simpa [prefixWord, tailWord_565065, baseEnd_565065] using wordTrace_append hprefix tailTrace_565065
  have hstable : (prefixWord ++ tailWord_565065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565065).length < 2 ^ (prefixWord ++ tailWord_565065).sum := by decide
  have hdescent : baseEnd_565065 < baseStart_565065 := by decide
  rcases family_descends (prefixWord ++ tailWord_565065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565076 : List Nat := [2, 4, 1, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_565076 : Nat := 118140960795 + 565076 * 2 ^ 59
def prefixEnd_565076 : Nat := 4983230072969 + 3 ^ 40 * 565076 * 2
def baseEnd_565076 : Nat := 290155594320136371251269

theorem tailTrace_565076 : CollatzResearch.WordTrace tailWord_565076 prefixEnd_565076 290155594320136371251269 := by
  unfold tailWord_565076
  simp only [CollatzResearch.WordTrace]
  refine ⟨10305007450416817071285541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13740009933889089428380721 10305007450416817071285541)
  ·
    refine ⟨1932188896953153200866039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10305007450416817071285541 1932188896953153200866039)
    ·
      refine ⟨2898283345429729801299059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1932188896953153200866039 2898283345429729801299059)
      ·
        refine ⟨4347425018144594701948589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2898283345429729801299059 4347425018144594701948589)
        ·
          refine ⟨1630284381804223013230721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4347425018144594701948589 1630284381804223013230721)
          ·
            refine ⟨1222713286353167259923041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1630284381804223013230721 1222713286353167259923041)
            ·
              refine ⟨917034964764875444942281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1222713286353167259923041 917034964764875444942281)
              ·
                refine ⟨687776223573656583706711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917034964764875444942281 687776223573656583706711)
                ·
                  refine ⟨1031664335360484875560067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687776223573656583706711 1031664335360484875560067)
                  ·
                    refine ⟨1547496503040727313340101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1031664335360484875560067 1547496503040727313340101)
                    ·
                      refine ⟨290155594320136371251269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1547496503040727313340101 290155594320136371251269)
                      ·
                        rfl

theorem cell23_565076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_565076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565076 prefixEnd_565076 := by exact prefixLift 565076
  have htrace : WordTrace (prefixWord ++ tailWord_565076) baseStart_565076 baseEnd_565076 := by
    simpa [prefixWord, tailWord_565076, baseEnd_565076] using wordTrace_append hprefix tailTrace_565076
  have hstable : (prefixWord ++ tailWord_565076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565076).length < 2 ^ (prefixWord ++ tailWord_565076).sum := by decide
  have hdescent : baseEnd_565076 < baseStart_565076 := by decide
  rcases family_descends (prefixWord ++ tailWord_565076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565119 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 3, 3, 2]
def baseStart_565119 : Nat := 118140960795 + 565119 * 2 ^ 59
def prefixEnd_565119 : Nat := 4983230072969 + 3 ^ 40 * 565119 * 2
def baseEnd_565119 : Nat := 290177673988279703013571

theorem tailTrace_565119 : CollatzResearch.WordTrace tailWord_565119 prefixEnd_565119 290177673988279703013571 := by
  unfold tailWord_565119
  simp only [CollatzResearch.WordTrace]
  refine ⟨20611583239677852486386411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13741055493118568324257607 20611583239677852486386411)
  ·
    refine ⟨30917374859516778729579617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20611583239677852486386411 30917374859516778729579617)
    ·
      refine ⟨23188031144637584047184713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30917374859516778729579617 23188031144637584047184713)
      ·
        refine ⟨17391023358478188035388535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23188031144637584047184713 17391023358478188035388535)
        ·
          refine ⟨26086535037717282053082803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17391023358478188035388535 26086535037717282053082803)
          ·
            refine ⟨39129802556575923079624205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26086535037717282053082803 39129802556575923079624205)
            ·
              refine ⟨14673675958715971154859077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39129802556575923079624205 14673675958715971154859077)
              ·
                refine ⟨2751314242259244591536077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14673675958715971154859077 2751314242259244591536077)
                ·
                  refine ⟨1031742840847216721826029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2751314242259244591536077 1031742840847216721826029)
                  ·
                    refine ⟨386903565317706270684761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1031742840847216721826029 386903565317706270684761)
                    ·
                      refine ⟨290177673988279703013571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 386903565317706270684761 290177673988279703013571)
                      ·
                        rfl

theorem cell23_565119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_565119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565119 prefixEnd_565119 := by exact prefixLift 565119
  have htrace : WordTrace (prefixWord ++ tailWord_565119) baseStart_565119 baseEnd_565119 := by
    simpa [prefixWord, tailWord_565119, baseEnd_565119] using wordTrace_append hprefix tailTrace_565119
  have hstable : (prefixWord ++ tailWord_565119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565119).length < 2 ^ (prefixWord ++ tailWord_565119).sum := by decide
  have hdescent : baseEnd_565119 < baseStart_565119 := by decide
  rcases family_descends (prefixWord ++ tailWord_565119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565130 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_565130 : Nat := 118140960795 + 565130 * 2 ^ 59
def prefixEnd_565130 : Nat := 4983230072969 + 3 ^ 40 * 565130 * 2
def baseEnd_565130 : Nat := 290183322275479159976021

theorem tailTrace_565130 : CollatzResearch.WordTrace tailWord_565130 prefixEnd_565130 290183322275479159976021 := by
  unfold tailWord_565130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152996110659500341259211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13741322961758667576691229 5152996110659500341259211)
  ·
    refine ⟨7729494165989250511888817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5152996110659500341259211 7729494165989250511888817)
    ·
      refine ⟨5797120624491937883916613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7729494165989250511888817 5797120624491937883916613)
      ·
        refine ⟨1086960117092238353234365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5797120624491937883916613 1086960117092238353234365)
        ·
          refine ⟨407610043909589382462887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1086960117092238353234365 407610043909589382462887)
          ·
            refine ⟨611415065864384073694331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407610043909589382462887 611415065864384073694331)
            ·
              refine ⟨917122598796576110541497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611415065864384073694331 917122598796576110541497)
              ·
                refine ⟨687841949097432082906123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917122598796576110541497 687841949097432082906123)
                ·
                  refine ⟨1031762923646148124359185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 687841949097432082906123 1031762923646148124359185)
                  ·
                    refine ⟨773822192734611093269389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1031762923646148124359185 773822192734611093269389)
                    ·
                      refine ⟨290183322275479159976021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 773822192734611093269389 290183322275479159976021)
                      ·
                        rfl

theorem cell23_565130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_565130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565130 prefixEnd_565130 := by exact prefixLift 565130
  have htrace : WordTrace (prefixWord ++ tailWord_565130) baseStart_565130 baseEnd_565130 := by
    simpa [prefixWord, tailWord_565130, baseEnd_565130] using wordTrace_append hprefix tailTrace_565130
  have hstable : (prefixWord ++ tailWord_565130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565130).length < 2 ^ (prefixWord ++ tailWord_565130).sum := by decide
  have hdescent : baseEnd_565130 < baseStart_565130 := by decide
  rcases family_descends (prefixWord ++ tailWord_565130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565169 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_565169 : Nat := 118140960795 + 565169 * 2 ^ 59
def prefixEnd_565169 : Nat := 4983230072969 + 3 ^ 40 * 565169 * 2
def baseEnd_565169 : Nat := 290203348021004507388341

theorem tailTrace_565169 : CollatzResearch.WordTrace tailWord_565169 prefixEnd_565169 290203348021004507388341 := by
  unfold tailWord_565169
  simp only [CollatzResearch.WordTrace]
  refine ⟨20613406889496711025706561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13742271259664474017137707 20613406889496711025706561)
  ·
    refine ⟨15460055167122533269279921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20613406889496711025706561 15460055167122533269279921)
    ·
      refine ⟨11595041375341899951959941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15460055167122533269279921 11595041375341899951959941)
      ·
        refine ⟨2174070257876606240992489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11595041375341899951959941 2174070257876606240992489)
        ·
          refine ⟨1630552693407454680744367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2174070257876606240992489 1630552693407454680744367)
          ·
            refine ⟨2445829040111182021116551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630552693407454680744367 2445829040111182021116551)
            ·
              refine ⟨3668743560166773031674827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445829040111182021116551 3668743560166773031674827)
              ·
                refine ⟨5503115340250159547512241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3668743560166773031674827 5503115340250159547512241)
                ·
                  refine ⟨4127336505187619660634181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5503115340250159547512241 4127336505187619660634181)
                  ·
                    refine ⟨773875594722678686368909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4127336505187619660634181 773875594722678686368909)
                    ·
                      refine ⟨290203348021004507388341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 773875594722678686368909 290203348021004507388341)
                      ·
                        rfl

theorem cell23_565169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_565169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565169 prefixEnd_565169 := by exact prefixLift 565169
  have htrace : WordTrace (prefixWord ++ tailWord_565169) baseStart_565169 baseEnd_565169 := by
    simpa [prefixWord, tailWord_565169, baseEnd_565169] using wordTrace_append hprefix tailTrace_565169
  have hstable : (prefixWord ++ tailWord_565169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565169).length < 2 ^ (prefixWord ++ tailWord_565169).sum := by decide
  have hdescent : baseEnd_565169 < baseStart_565169 := by decide
  rcases family_descends (prefixWord ++ tailWord_565169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565259 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 3]
def baseStart_565259 : Nat := 118140960795 + 565259 * 2 ^ 59
def prefixEnd_565259 : Nat := 4983230072969 + 3 ^ 40 * 565259 * 2
def baseEnd_565259 : Nat := 290249561279909155262927

theorem tailTrace_565259 : CollatzResearch.WordTrace tailWord_565259 prefixEnd_565259 290249561279909155262927 := by
  unfold tailWord_565259
  simp only [CollatzResearch.WordTrace]
  refine ⟨20616689459170656396482831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13744459639447104264321887 20616689459170656396482831)
  ·
    refine ⟨30925034188755984594724247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20616689459170656396482831 30925034188755984594724247)
    ·
      refine ⟨46387551283133976892086371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30925034188755984594724247 46387551283133976892086371)
      ·
        refine ⟨69581326924700965338129557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46387551283133976892086371 69581326924700965338129557)
        ·
          refine ⟨3261624699595357750224823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69581326924700965338129557 3261624699595357750224823)
          ·
            refine ⟨4892437049393036625337235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3261624699595357750224823 4892437049393036625337235)
            ·
              refine ⟨7338655574089554938005853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4892437049393036625337235 7338655574089554938005853)
              ·
                refine ⟨2751995840283583101752195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7338655574089554938005853 2751995840283583101752195)
                ·
                  refine ⟨4127993760425374652628293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2751995840283583101752195 4127993760425374652628293)
                  ·
                    refine ⟨773998830079757747367805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4127993760425374652628293 773998830079757747367805)
                    ·
                      refine ⟨290249561279909155262927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 773998830079757747367805 290249561279909155262927)
                      ·
                        rfl

theorem cell23_565259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 3].length) (baseStart_565259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565259 prefixEnd_565259 := by exact prefixLift 565259
  have htrace : WordTrace (prefixWord ++ tailWord_565259) baseStart_565259 baseEnd_565259 := by
    simpa [prefixWord, tailWord_565259, baseEnd_565259] using wordTrace_append hprefix tailTrace_565259
  have hstable : (prefixWord ++ tailWord_565259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565259).length < 2 ^ (prefixWord ++ tailWord_565259).sum := by decide
  have hdescent : baseEnd_565259 < baseStart_565259 := by decide
  rcases family_descends (prefixWord ++ tailWord_565259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565276 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_565276 : Nat := 118140960795 + 565276 * 2 ^ 59
def prefixEnd_565276 : Nat := 4983230072969 + 3 ^ 40 * 565276 * 2
def baseEnd_565276 : Nat := 290258290451035588750349

theorem tailTrace_565276 : CollatzResearch.WordTrace tailWord_565276 prefixEnd_565276 290258290451035588750349 := by
  unfold tailWord_565276
  simp only [CollatzResearch.WordTrace]
  refine ⟨10308654750054534149925841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13744873000072712199901121 10308654750054534149925841)
  ·
    refine ⟨7731491062540900612444381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10308654750054534149925841 7731491062540900612444381)
    ·
      refine ⟨2899309148452837729666643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7731491062540900612444381 2899309148452837729666643)
      ·
        refine ⟨4348963722679256594499965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2899309148452837729666643 4348963722679256594499965)
        ·
          refine ⟨1630861396004721222937487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4348963722679256594499965 1630861396004721222937487)
          ·
            refine ⟨2446292094007081834406231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630861396004721222937487 2446292094007081834406231)
            ·
              refine ⟨3669438141010622751609347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446292094007081834406231 3669438141010622751609347)
              ·
                refine ⟨5504157211515934127414021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3669438141010622751609347 5504157211515934127414021)
                ·
                  refine ⟨1032029477159237648890129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5504157211515934127414021 1032029477159237648890129)
                  ·
                    refine ⟨774022107869428236667597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1032029477159237648890129 774022107869428236667597)
                    ·
                      refine ⟨290258290451035588750349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 774022107869428236667597 290258290451035588750349)
                      ·
                        rfl

theorem cell23_565276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_565276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565276 prefixEnd_565276 := by exact prefixLift 565276
  have htrace : WordTrace (prefixWord ++ tailWord_565276) baseStart_565276 baseEnd_565276 := by
    simpa [prefixWord, tailWord_565276, baseEnd_565276] using wordTrace_append hprefix tailTrace_565276
  have hstable : (prefixWord ++ tailWord_565276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565276).length < 2 ^ (prefixWord ++ tailWord_565276).sum := by decide
  have hdescent : baseEnd_565276 < baseStart_565276 := by decide
  rcases family_descends (prefixWord ++ tailWord_565276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565279 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 6]
def baseStart_565279 : Nat := 118140960795 + 565279 * 2 ^ 59
def prefixEnd_565279 : Nat := 4983230072969 + 3 ^ 40 * 565279 * 2
def baseEnd_565279 : Nat := 32251092321444341890315

theorem tailTrace_565279 : CollatzResearch.WordTrace tailWord_565279 prefixEnd_565279 32251092321444341890315 := by
  unfold tailWord_565279
  simp only [CollatzResearch.WordTrace]
  refine ⟨20617418919098199812210891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13744945946065466541473927 20617418919098199812210891)
  ·
    refine ⟨30926128378647299718316337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20617418919098199812210891 30926128378647299718316337)
    ·
      refine ⟨23194596283985474788737253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30926128378647299718316337 23194596283985474788737253)
      ·
        refine ⟨4348986803247276522888235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23194596283985474788737253 4348986803247276522888235)
        ·
          refine ⟨6523480204870914784332353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4348986803247276522888235 6523480204870914784332353)
          ·
            refine ⟨4892610153653186088249265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6523480204870914784332353 4892610153653186088249265)
            ·
              refine ⟨3669457615239889566186949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4892610153653186088249265 3669457615239889566186949)
              ·
                refine ⟨688023302857479293660053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3669457615239889566186949 688023302857479293660053)
                ·
                  refine ⟨32251092321444341890315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 688023302857479293660053 32251092321444341890315)
                  ·
                    rfl

theorem cell23_565279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 6].length) (baseStart_565279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565279 prefixEnd_565279 := by exact prefixLift 565279
  have htrace : WordTrace (prefixWord ++ tailWord_565279) baseStart_565279 baseEnd_565279 := by
    simpa [prefixWord, tailWord_565279, baseEnd_565279] using wordTrace_append hprefix tailTrace_565279
  have hstable : (prefixWord ++ tailWord_565279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565279).length < 2 ^ (prefixWord ++ tailWord_565279).sum := by decide
  have hdescent : baseEnd_565279 < baseStart_565279 := by decide
  rcases family_descends (prefixWord ++ tailWord_565279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565296 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 6]
def baseStart_565296 : Nat := 118140960795 + 565296 * 2 ^ 59
def prefixEnd_565296 : Nat := 4983230072969 + 3 ^ 40 * 565296 * 2
def baseEnd_565296 : Nat := 32252062229347278944473

theorem tailTrace_565296 : CollatzResearch.WordTrace tailWord_565296 prefixEnd_565296 32252062229347278944473 := by
  unfold tailWord_565296
  simp only [CollatzResearch.WordTrace]
  refine ⟨10309019480018305857789871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13745359306691074477053161 10309019480018305857789871)
  ·
    refine ⟨15463529220027458786684807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10309019480018305857789871 15463529220027458786684807)
    ·
      refine ⟨23195293830041188180027211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15463529220027458786684807 23195293830041188180027211)
      ·
        refine ⟨34792940745061782270040817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23195293830041188180027211 34792940745061782270040817)
        ·
          refine ⟨26094705558796336702530613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34792940745061782270040817 26094705558796336702530613)
          ·
            refine ⟨2446378646137156565862245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26094705558796336702530613 2446378646137156565862245)
            ·
              refine ⟨458695996150716856099171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2446378646137156565862245 458695996150716856099171)
              ·
                refine ⟨688043994226075284148757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458695996150716856099171 688043994226075284148757)
                ·
                  refine ⟨32252062229347278944473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 688043994226075284148757 32252062229347278944473)
                  ·
                    rfl

theorem cell23_565296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 6].length) (baseStart_565296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565296 prefixEnd_565296 := by exact prefixLift 565296
  have htrace : WordTrace (prefixWord ++ tailWord_565296) baseStart_565296 baseEnd_565296 := by
    simpa [prefixWord, tailWord_565296, baseEnd_565296] using wordTrace_append hprefix tailTrace_565296
  have hstable : (prefixWord ++ tailWord_565296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565296).length < 2 ^ (prefixWord ++ tailWord_565296).sum := by decide
  have hdescent : baseEnd_565296 < baseStart_565296 := by decide
  rcases family_descends (prefixWord ++ tailWord_565296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565306 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3]
def baseStart_565306 : Nat := 118140960795 + 565306 * 2 ^ 59
def prefixEnd_565306 : Nat := 4983230072969 + 3 ^ 40 * 565306 * 2
def baseEnd_565306 : Nat := 290273694870670471375211

theorem tailTrace_565306 : CollatzResearch.WordTrace tailWord_565306 prefixEnd_565306 290273694870670471375211 := by
  unfold tailWord_565306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5154600922500095855860943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13745602460000255615629181 5154600922500095855860943)
  ·
    refine ⟨7731901383750143783791415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5154600922500095855860943 7731901383750143783791415)
    ·
      refine ⟨11597852075625215675687123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7731901383750143783791415 11597852075625215675687123)
      ·
        refine ⟨17396778113437823513530685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11597852075625215675687123 17396778113437823513530685)
        ·
          refine ⟨6523791792539183817574007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17396778113437823513530685 6523791792539183817574007)
          ·
            refine ⟨9785687688808775726361011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6523791792539183817574007 9785687688808775726361011)
            ·
              refine ⟨14678531533213163589541517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9785687688808775726361011 14678531533213163589541517)
              ·
                refine ⟨5504449324954936346078069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14678531533213163589541517 5504449324954936346078069)
                ·
                  refine ⟨516042124214525282444819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5504449324954936346078069 516042124214525282444819)
                  ·
                    refine ⟨774063186321787923667229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 516042124214525282444819 774063186321787923667229)
                    ·
                      refine ⟨290273694870670471375211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 774063186321787923667229 290273694870670471375211)
                      ·
                        rfl

theorem cell23_565306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_565306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565306 prefixEnd_565306 := by exact prefixLift 565306
  have htrace : WordTrace (prefixWord ++ tailWord_565306) baseStart_565306 baseEnd_565306 := by
    simpa [prefixWord, tailWord_565306, baseEnd_565306] using wordTrace_append hprefix tailTrace_565306
  have hstable : (prefixWord ++ tailWord_565306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565306).length < 2 ^ (prefixWord ++ tailWord_565306).sum := by decide
  have hdescent : baseEnd_565306 < baseStart_565306 := by decide
  rcases family_descends (prefixWord ++ tailWord_565306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565310 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_565310 : Nat := 118140960795 + 565310 * 2 ^ 59
def prefixEnd_565310 : Nat := 4983230072969 + 3 ^ 40 * 565310 * 2
def baseEnd_565310 : Nat := 290275748793288455725193

theorem tailTrace_565310 : CollatzResearch.WordTrace tailWord_565310 prefixEnd_565310 290275748793288455725193 := by
  unfold tailWord_565310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577318697748236513323673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13745699721323928071059589 2577318697748236513323673)
  ·
    refine ⟨1932989023311177384992755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2577318697748236513323673 1932989023311177384992755)
    ·
      refine ⟨2899483534966766077489133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1932989023311177384992755 2899483534966766077489133)
      ·
        refine ⟨1087306325612537279058425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2899483534966766077489133 1087306325612537279058425)
        ·
          refine ⟨815479744209402959293819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1087306325612537279058425 815479744209402959293819)
          ·
            refine ⟨1223219616314104438940729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815479744209402959293819 1223219616314104438940729)
            ·
              refine ⟨917414712235578329205547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223219616314104438940729 917414712235578329205547)
              ·
                refine ⟨1376122068353367493808321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917414712235578329205547 1376122068353367493808321)
                ·
                  refine ⟨1032091551265025620356241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1376122068353367493808321 1032091551265025620356241)
                  ·
                    refine ⟨774068663448769215267181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1032091551265025620356241 774068663448769215267181)
                    ·
                      refine ⟨290275748793288455725193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 774068663448769215267181 290275748793288455725193)
                      ·
                        rfl

theorem cell23_565310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_565310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565310 prefixEnd_565310 := by exact prefixLift 565310
  have htrace : WordTrace (prefixWord ++ tailWord_565310) baseStart_565310 baseEnd_565310 := by
    simpa [prefixWord, tailWord_565310, baseEnd_565310] using wordTrace_append hprefix tailTrace_565310
  have hstable : (prefixWord ++ tailWord_565310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565310).length < 2 ^ (prefixWord ++ tailWord_565310).sum := by decide
  have hdescent : baseEnd_565310 < baseStart_565310 := by decide
  rcases family_descends (prefixWord ++ tailWord_565310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565333 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_565333 : Nat := 118140960795 + 565333 * 2 ^ 59
def prefixEnd_565333 : Nat := 4983230072969 + 3 ^ 40 * 565333 * 2
def baseEnd_565333 : Nat := 290287558848341865737587

theorem tailTrace_565333 : CollatzResearch.WordTrace tailWord_565333 prefixEnd_565333 290287558848341865737587 := by
  unfold tailWord_565333
  simp only [CollatzResearch.WordTrace]
  refine ⟨20619388460902567034676653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13746258973935044689784435 20619388460902567034676653)
  ·
    refine ⟨7732270672838462638003745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20619388460902567034676653 7732270672838462638003745)
    ·
      refine ⟨5799203004628846978502809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7732270672838462638003745 5799203004628846978502809)
      ·
        refine ⟨4349402253471635233877107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5799203004628846978502809 4349402253471635233877107)
        ·
          refine ⟨6524103380207452850815661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4349402253471635233877107 6524103380207452850815661)
          ·
            refine ⟨2446538767577794819055873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6524103380207452850815661 2446538767577794819055873)
            ·
              refine ⟨1834904075683346114291905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2446538767577794819055873 1834904075683346114291905)
              ·
                refine ⟨1376178056762509585718929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834904075683346114291905 1376178056762509585718929)
                ·
                  refine ⟨1032133542571882189289197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1376178056762509585718929 1032133542571882189289197)
                  ·
                    refine ⟨387050078464455820983449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032133542571882189289197 387050078464455820983449)
                    ·
                      refine ⟨290287558848341865737587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387050078464455820983449 290287558848341865737587)
                      ·
                        rfl

theorem cell23_565333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_565333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565333 prefixEnd_565333 := by exact prefixLift 565333
  have htrace : WordTrace (prefixWord ++ tailWord_565333) baseStart_565333 baseEnd_565333 := by
    simpa [prefixWord, tailWord_565333, baseEnd_565333] using wordTrace_append hprefix tailTrace_565333
  have hstable : (prefixWord ++ tailWord_565333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565333).length < 2 ^ (prefixWord ++ tailWord_565333).sum := by decide
  have hdescent : baseEnd_565333 < baseStart_565333 := by decide
  rcases family_descends (prefixWord ++ tailWord_565333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565334 : List Nat := [5, 2, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_565334 : Nat := 118140960795 + 565334 * 2 ^ 59
def prefixEnd_565334 : Nat := 4983230072969 + 3 ^ 40 * 565334 * 2
def baseEnd_565334 : Nat := 96762690776332120608361

theorem tailTrace_565334 : CollatzResearch.WordTrace tailWord_565334 prefixEnd_565334 96762690776332120608361 := by
  unfold tailWord_565334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288714058368684012841441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13746283289265962803642037 1288714058368684012841441)
  ·
    refine ⟨966535543776513009631081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1288714058368684012841441 966535543776513009631081)
    ·
      refine ⟨724901657832384757223311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 966535543776513009631081 724901657832384757223311)
      ·
        refine ⟨1087352486748577135834967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724901657832384757223311 1087352486748577135834967)
        ·
          refine ⟨1631028730122865703752451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087352486748577135834967 1631028730122865703752451)
          ·
            refine ⟨2446543095184298555628677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631028730122865703752451 2446543095184298555628677)
            ·
              refine ⟨458726830347055979180377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2446543095184298555628677 458726830347055979180377)
              ·
                refine ⟨344045122760291984385283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458726830347055979180377 344045122760291984385283)
                ·
                  refine ⟨516067684140437976577925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344045122760291984385283 516067684140437976577925)
                  ·
                    refine ⟨96762690776332120608361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516067684140437976577925 96762690776332120608361)
                    ·
                      rfl

theorem cell23_565334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_565334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565334 prefixEnd_565334 := by exact prefixLift 565334
  have htrace : WordTrace (prefixWord ++ tailWord_565334) baseStart_565334 baseEnd_565334 := by
    simpa [prefixWord, tailWord_565334, baseEnd_565334] using wordTrace_append hprefix tailTrace_565334
  have hstable : (prefixWord ++ tailWord_565334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565334).length < 2 ^ (prefixWord ++ tailWord_565334).sum := by decide
  have hdescent : baseEnd_565334 < baseStart_565334 := by decide
  rcases family_descends (prefixWord ++ tailWord_565334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565356 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_565356 : Nat := 118140960795 + 565356 * 2 ^ 59
def prefixEnd_565356 : Nat := 4983230072969 + 3 ^ 40 * 565356 * 2
def baseEnd_565356 : Nat := 96766456301131758583327

theorem tailTrace_565356 : CollatzResearch.WordTrace tailWord_565356 prefixEnd_565356 96766456301131758583327 := by
  unfold tailWord_565356
  simp only [CollatzResearch.WordTrace]
  refine ⟨10310113669909620981381961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13746818226546161308509281 10310113669909620981381961)
  ·
    refine ⟨7732585252432215736036471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10310113669909620981381961 7732585252432215736036471)
    ·
      refine ⟨11598877878648323604054707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7732585252432215736036471 11598877878648323604054707)
      ·
        refine ⟨17398316817972485406082061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11598877878648323604054707 17398316817972485406082061)
        ·
          refine ⟨6524368806739682027280773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17398316817972485406082061 6524368806739682027280773)
          ·
            refine ⟨1223319151263690380115145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6524368806739682027280773 1223319151263690380115145)
            ·
              refine ⟨917489363447767785086359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1223319151263690380115145 917489363447767785086359)
              ·
                refine ⟨1376234045171651677629539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917489363447767785086359 1376234045171651677629539)
                ·
                  refine ⟨2064351067757477516444309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376234045171651677629539 2064351067757477516444309)
                  ·
                    refine ⟨96766456301131758583327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2064351067757477516444309 96766456301131758583327)
                    ·
                      rfl

theorem cell23_565356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_565356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565356 prefixEnd_565356 := by exact prefixLift 565356
  have htrace : WordTrace (prefixWord ++ tailWord_565356) baseStart_565356 baseEnd_565356 := by
    simpa [prefixWord, tailWord_565356, baseEnd_565356] using wordTrace_append hprefix tailTrace_565356
  have hstable : (prefixWord ++ tailWord_565356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565356).length < 2 ^ (prefixWord ++ tailWord_565356).sum := by decide
  have hdescent : baseEnd_565356 < baseStart_565356 := by decide
  rcases family_descends (prefixWord ++ tailWord_565356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565377 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 1, 5]
def baseStart_565377 : Nat := 118140960795 + 565377 * 2 ^ 59
def prefixEnd_565377 : Nat := 4983230072969 + 3 ^ 40 * 565377 * 2
def baseEnd_565377 : Nat := 96770050665713231195795

theorem tailTrace_565377 : CollatzResearch.WordTrace tailWord_565377 prefixEnd_565377 96770050665713231195795 := by
  unfold tailWord_565377
  simp only [CollatzResearch.WordTrace]
  refine ⟨20620993272743162549278385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13747328848495441699518923 20620993272743162549278385)
  ·
    refine ⟨15465744954557371911958789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20620993272743162549278385 15465744954557371911958789)
    ·
      refine ⟨2899827178979507233492273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15465744954557371911958789 2899827178979507233492273)
      ·
        refine ⟨2174870384234630425119205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2899827178979507233492273 2174870384234630425119205)
        ·
          refine ⟨407788197043993204709851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2174870384234630425119205 407788197043993204709851)
          ·
            refine ⟨611682295565989807064777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407788197043993204709851 611682295565989807064777)
            ·
              refine ⟨458761721674492355298583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611682295565989807064777 458761721674492355298583)
              ·
                refine ⟨688142582511738532947875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458761721674492355298583 688142582511738532947875)
                ·
                  refine ⟨1032213873767607799421813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688142582511738532947875 1032213873767607799421813)
                  ·
                    refine ⟨96770050665713231195795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1032213873767607799421813 96770050665713231195795)
                    ·
                      rfl

theorem cell23_565377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_565377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565377 prefixEnd_565377 := by exact prefixLift 565377
  have htrace : WordTrace (prefixWord ++ tailWord_565377) baseStart_565377 baseEnd_565377 := by
    simpa [prefixWord, tailWord_565377, baseEnd_565377] using wordTrace_append hprefix tailTrace_565377
  have hstable : (prefixWord ++ tailWord_565377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565377).length < 2 ^ (prefixWord ++ tailWord_565377).sum := by decide
  have hdescent : baseEnd_565377 < baseStart_565377 := by decide
  rcases family_descends (prefixWord ++ tailWord_565377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565410 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_565410 : Nat := 118140960795 + 565410 * 2 ^ 59
def prefixEnd_565410 : Nat := 4983230072969 + 3 ^ 40 * 565410 * 2
def baseEnd_565410 : Nat := 290327096858738064474733

theorem tailTrace_565410 : CollatzResearch.WordTrace tailWord_565410 prefixEnd_565410 290327096858738064474733 := by
  unfold tailWord_565410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5155549220405902296307421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13748131254415739456819789 5155549220405902296307421)
  ·
    refine ⟨1933330957652213361115283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5155549220405902296307421 1933330957652213361115283)
    ·
      refine ⟨2899996436478320041672925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1933330957652213361115283 2899996436478320041672925)
      ·
        refine ⟨1087498663679370015627347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2899996436478320041672925 1087498663679370015627347)
        ·
          refine ⟨1631247995519055023441021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087498663679370015627347 1631247995519055023441021)
          ·
            refine ⟨611717998319645633790383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1631247995519055023441021 611717998319645633790383)
            ·
              refine ⟨917576997479468450685575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611717998319645633790383 917576997479468450685575)
              ·
                refine ⟨1376365496219202676028363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917576997479468450685575 1376365496219202676028363)
                ·
                  refine ⟨2064548244328804014042545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1376365496219202676028363 2064548244328804014042545)
                  ·
                    refine ⟨1548411183246603010531909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2064548244328804014042545 1548411183246603010531909)
                    ·
                      refine ⟨290327096858738064474733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1548411183246603010531909 290327096858738064474733)
                      ·
                        rfl

theorem cell23_565410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_565410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565410 prefixEnd_565410 := by exact prefixLift 565410
  have htrace : WordTrace (prefixWord ++ tailWord_565410) baseStart_565410 baseEnd_565410 := by
    simpa [prefixWord, tailWord_565410, baseEnd_565410] using wordTrace_append hprefix tailTrace_565410
  have hstable : (prefixWord ++ tailWord_565410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565410).length < 2 ^ (prefixWord ++ tailWord_565410).sum := by decide
  have hdescent : baseEnd_565410 < baseStart_565410 := by decide
  rcases family_descends (prefixWord ++ tailWord_565410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565419 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 4]
def baseStart_565419 : Nat := 118140960795 + 565419 * 2 ^ 59
def prefixEnd_565419 : Nat := 4983230072969 + 3 ^ 40 * 565419 * 2
def baseEnd_565419 : Nat := 290331718184628529262191

theorem tailTrace_565419 : CollatzResearch.WordTrace tailWord_565419 prefixEnd_565419 290331718184628529262191 := by
  unfold tailWord_565419
  simp only [CollatzResearch.WordTrace]
  refine ⟨20622525138591003722307311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13748350092394002481538207 20622525138591003722307311)
  ·
    refine ⟨30933787707886505583460967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20622525138591003722307311 30933787707886505583460967)
    ·
      refine ⟨46400681561829758375191451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30933787707886505583460967 46400681561829758375191451)
      ·
        refine ⟨69601022342744637562787177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46400681561829758375191451 69601022342744637562787177)
        ·
          refine ⟨52200766757058478172090383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69601022342744637562787177 52200766757058478172090383)
          ·
            refine ⟨78301150135587717258135575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52200766757058478172090383 78301150135587717258135575)
            ·
              refine ⟨117451725203381575887203363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78301150135587717258135575 117451725203381575887203363)
              ·
                refine ⟨176177587805072363830805045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117451725203381575887203363 176177587805072363830805045)
                ·
                  refine ⟨16516648856725534109137973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176177587805072363830805045 16516648856725534109137973)
                  ·
                    refine ⟨1548435830318018822731685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16516648856725534109137973 1548435830318018822731685)
                    ·
                      refine ⟨290331718184628529262191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1548435830318018822731685 290331718184628529262191)
                      ·
                        rfl

theorem cell23_565419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 4].length) (baseStart_565419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565419 prefixEnd_565419 := by exact prefixLift 565419
  have htrace : WordTrace (prefixWord ++ tailWord_565419) baseStart_565419 baseEnd_565419 := by
    simpa [prefixWord, tailWord_565419, baseEnd_565419] using wordTrace_append hprefix tailTrace_565419
  have hstable : (prefixWord ++ tailWord_565419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565419).length < 2 ^ (prefixWord ++ tailWord_565419).sum := by decide
  have hdescent : baseEnd_565419 < baseStart_565419 := by decide
  rcases family_descends (prefixWord ++ tailWord_565419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565440 : List Nat := [2, 1, 1, 2, 5, 1, 2, 3, 1, 3, 2]
def baseStart_565440 : Nat := 118140960795 + 565440 * 2 ^ 59
def prefixEnd_565440 : Nat := 4983230072969 + 3 ^ 40 * 565440 * 2
def baseEnd_565440 : Nat := 290342501278372947099595

theorem tailTrace_565440 : CollatzResearch.WordTrace tailWord_565440 prefixEnd_565440 290342501278372947099595 := by
  unfold tailWord_565440
  simp only [CollatzResearch.WordTrace]
  refine ⟨10311645535757462154410887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13748860714343282872547849 10311645535757462154410887)
  ·
    refine ⟨15467468303636193231616331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10311645535757462154410887 15467468303636193231616331)
    ·
      refine ⟨23201202455454289847424497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15467468303636193231616331 23201202455454289847424497)
      ·
        refine ⟨17400901841590717385568373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23201202455454289847424497 17400901841590717385568373)
        ·
          refine ⟨1631334547649129754897035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17400901841590717385568373 1631334547649129754897035)
          ·
            refine ⟨2447001821473694632345553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631334547649129754897035 2447001821473694632345553)
            ·
              refine ⟨1835251366105270974259165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2447001821473694632345553 1835251366105270974259165)
              ·
                refine ⟨688219262289476615347187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1835251366105270974259165 688219262289476615347187)
                ·
                  refine ⟨1032328893434214923020781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688219262289476615347187 1032328893434214923020781)
                  ·
                    refine ⟨387123335037830596132793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1032328893434214923020781 387123335037830596132793)
                    ·
                      refine ⟨290342501278372947099595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387123335037830596132793 290342501278372947099595)
                      ·
                        rfl

theorem cell23_565440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_565440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565440 prefixEnd_565440 := by exact prefixLift 565440
  have htrace : WordTrace (prefixWord ++ tailWord_565440) baseStart_565440 baseEnd_565440 := by
    simpa [prefixWord, tailWord_565440, baseEnd_565440] using wordTrace_append hprefix tailTrace_565440
  have hstable : (prefixWord ++ tailWord_565440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565440).length < 2 ^ (prefixWord ++ tailWord_565440).sum := by decide
  have hdescent : baseEnd_565440 < baseStart_565440 := by decide
  rcases family_descends (prefixWord ++ tailWord_565440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565449 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_565449 : Nat := 118140960795 + 565449 * 2 ^ 59
def prefixEnd_565449 : Nat := 4983230072969 + 3 ^ 40 * 565449 * 2
def baseEnd_565449 : Nat := 290347122604263411887053

theorem tailTrace_565449 : CollatzResearch.WordTrace tailWord_565449 prefixEnd_565449 290347122604263411887053 := by
  unfold tailWord_565449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20623619328482318845899401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13749079552321545897266267 20623619328482318845899401)
  ·
    refine ⟨15467714496361739134424551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20623619328482318845899401 15467714496361739134424551)
    ·
      refine ⟨23201571744542608701636827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15467714496361739134424551 23201571744542608701636827)
      ·
        refine ⟨34802357616813913052455241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23201571744542608701636827 34802357616813913052455241)
        ·
          refine ⟨26101768212610434789341431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34802357616813913052455241 26101768212610434789341431)
          ·
            refine ⟨39152652318915652184012147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26101768212610434789341431 39152652318915652184012147)
            ·
              refine ⟨58728978478373478276018221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39152652318915652184012147 58728978478373478276018221)
              ·
                refine ⟨22023366929390054353506833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58728978478373478276018221 22023366929390054353506833)
                ·
                  refine ⟨16517525197042540765130125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22023366929390054353506833 16517525197042540765130125)
                  ·
                    refine ⟨6194071948890952786923797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16517525197042540765130125 6194071948890952786923797)
                    ·
                      refine ⟨290347122604263411887053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6194071948890952786923797 290347122604263411887053)
                      ·
                        rfl

theorem cell23_565449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_565449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565449 prefixEnd_565449 := by exact prefixLift 565449
  have htrace : WordTrace (prefixWord ++ tailWord_565449) baseStart_565449 baseEnd_565449 := by
    simpa [prefixWord, tailWord_565449, baseEnd_565449] using wordTrace_append hprefix tailTrace_565449
  have hstable : (prefixWord ++ tailWord_565449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565449).length < 2 ^ (prefixWord ++ tailWord_565449).sum := by decide
  have hdescent : baseEnd_565449 < baseStart_565449 := by decide
  rcases family_descends (prefixWord ++ tailWord_565449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565466 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_565466 : Nat := 118140960795 + 565466 * 2 ^ 59
def prefixEnd_565466 : Nat := 4983230072969 + 3 ^ 40 * 565466 * 2
def baseEnd_565466 : Nat := 290355851775389845374475

theorem tailTrace_565466 : CollatzResearch.WordTrace tailWord_565466 prefixEnd_565466 290355851775389845374475 := by
  unfold tailWord_565466
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156059842355182687317063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13749492912947153832845501 5156059842355182687317063)
  ·
    refine ⟨7734089763532774030975595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5156059842355182687317063 7734089763532774030975595)
    ·
      refine ⟨11601134645299161046463393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7734089763532774030975595 11601134645299161046463393)
      ·
        refine ⟨8700850983974370784847545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11601134645299161046463393 8700850983974370784847545)
        ·
          refine ⟨6525638237980778088635659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8700850983974370784847545 6525638237980778088635659)
          ·
            refine ⟨9788457356971167132953489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6525638237980778088635659 9788457356971167132953489)
            ·
              refine ⟨7341343017728375349715117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9788457356971167132953489 7341343017728375349715117)
              ·
                refine ⟨2753003631648140756143169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7341343017728375349715117 2753003631648140756143169)
                ·
                  refine ⟨2064752723736105567107377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2753003631648140756143169 2064752723736105567107377)
                  ·
                    refine ⟨1548564542802079175330533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2064752723736105567107377 1548564542802079175330533)
                    ·
                      refine ⟨290355851775389845374475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1548564542802079175330533 290355851775389845374475)
                      ·
                        rfl

theorem cell23_565466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_565466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565466 prefixEnd_565466 := by exact prefixLift 565466
  have htrace : WordTrace (prefixWord ++ tailWord_565466) baseStart_565466 baseEnd_565466 := by
    simpa [prefixWord, tailWord_565466, baseEnd_565466] using wordTrace_append hprefix tailTrace_565466
  have hstable : (prefixWord ++ tailWord_565466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565466).length < 2 ^ (prefixWord ++ tailWord_565466).sum := by decide
  have hdescent : baseEnd_565466 < baseStart_565466 := by decide
  rcases family_descends (prefixWord ++ tailWord_565466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565513 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 2, 5, 2]
def baseStart_565513 : Nat := 118140960795 + 565513 * 2 ^ 59
def prefixEnd_565513 : Nat := 4983230072969 + 3 ^ 40 * 565513 * 2
def baseEnd_565513 : Nat := 290379985366151161486759

theorem tailTrace_565513 : CollatzResearch.WordTrace tailWord_565513 prefixEnd_565513 290379985366151161486759 := by
  unfold tailWord_565513
  simp only [CollatzResearch.WordTrace]
  refine ⟨20625953600250457776229193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13750635733500305184152795 20625953600250457776229193)
  ·
    refine ⟨15469465200187843332171895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20625953600250457776229193 15469465200187843332171895)
    ·
      refine ⟨23204197800281764998257843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15469465200187843332171895 23204197800281764998257843)
      ·
        refine ⟨34806296700422647497386765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23204197800281764998257843 34806296700422647497386765)
        ·
          refine ⟨13052361262658492811520037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34806296700422647497386765 13052361262658492811520037)
          ·
            refine ⟨2447317736748467402160007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13052361262658492811520037 2447317736748467402160007)
            ·
              refine ⟨3670976605122701103240011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447317736748467402160007 3670976605122701103240011)
              ·
                refine ⟨5506464907684051654860017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670976605122701103240011 5506464907684051654860017)
                ·
                  refine ⟨4129848680763038741145013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5506464907684051654860017 4129848680763038741145013)
                  ·
                    refine ⟨387173313821534881982345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4129848680763038741145013 387173313821534881982345)
                    ·
                      refine ⟨290379985366151161486759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387173313821534881982345 290379985366151161486759)
                      ·
                        rfl

theorem cell23_565513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 5, 2].length) (baseStart_565513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565513 prefixEnd_565513 := by exact prefixLift 565513
  have htrace : WordTrace (prefixWord ++ tailWord_565513) baseStart_565513 baseEnd_565513 := by
    simpa [prefixWord, tailWord_565513, baseEnd_565513] using wordTrace_append hprefix tailTrace_565513
  have hstable : (prefixWord ++ tailWord_565513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565513).length < 2 ^ (prefixWord ++ tailWord_565513).sum := by decide
  have hdescent : baseEnd_565513 < baseStart_565513 := by decide
  rcases family_descends (prefixWord ++ tailWord_565513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565516 : List Nat := [2, 2, 1, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_565516 : Nat := 118140960795 + 565516 * 2 ^ 59
def prefixEnd_565516 : Nat := 4983230072969 + 3 ^ 40 * 565516 * 2
def baseEnd_565516 : Nat := 290381525808114649749245

theorem tailTrace_565516 : CollatzResearch.WordTrace tailWord_565516 prefixEnd_565516 290381525808114649749245 := by
  unfold tailWord_565516
  simp only [CollatzResearch.WordTrace]
  refine ⟨10313031509619794644294201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13750708679493059525725601 10313031509619794644294201)
  ·
    refine ⟨7734773632214845983220651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10313031509619794644294201 7734773632214845983220651)
    ·
      refine ⟨11602160448322268974830977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7734773632214845983220651 11602160448322268974830977)
      ·
        refine ⟨8701620336241701731123233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11602160448322268974830977 8701620336241701731123233)
        ·
          refine ⟨6526215252181276298342425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8701620336241701731123233 6526215252181276298342425)
          ·
            refine ⟨4894661439135957223756819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6526215252181276298342425 4894661439135957223756819)
            ·
              refine ⟨7341992158703935835635229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4894661439135957223756819 7341992158703935835635229)
              ·
                refine ⟨2753247059513975938363211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7341992158703935835635229 2753247059513975938363211)
                ·
                  refine ⟨4129870589270963907544817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2753247059513975938363211 4129870589270963907544817)
                  ·
                    refine ⟨3097402941953222930658613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4129870589270963907544817 3097402941953222930658613)
                    ·
                      refine ⟨290381525808114649749245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3097402941953222930658613 290381525808114649749245)
                      ·
                        rfl

theorem cell23_565516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_565516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565516 prefixEnd_565516 := by exact prefixLift 565516
  have htrace : WordTrace (prefixWord ++ tailWord_565516) baseStart_565516 baseEnd_565516 := by
    simpa [prefixWord, tailWord_565516, baseEnd_565516] using wordTrace_append hprefix tailTrace_565516
  have hstable : (prefixWord ++ tailWord_565516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565516).length < 2 ^ (prefixWord ++ tailWord_565516).sum := by decide
  have hdescent : baseEnd_565516 < baseStart_565516 := by decide
  rcases family_descends (prefixWord ++ tailWord_565516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565540 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_565540 : Nat := 118140960795 + 565540 * 2 ^ 59
def prefixEnd_565540 : Nat := 4983230072969 + 3 ^ 40 * 565540 * 2
def baseEnd_565540 : Nat := 96797949781274185283045

theorem tailTrace_565540 : CollatzResearch.WordTrace tailWord_565540 prefixEnd_565540 96797949781274185283045 := by
  unfold tailWord_565540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10313469185576320693731037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13751292247435094258308049 10313469185576320693731037)
  ·
    refine ⟨3867550944591120260149139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10313469185576320693731037 3867550944591120260149139)
    ·
      refine ⟨5801326416886680390223709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867550944591120260149139 5801326416886680390223709)
      ·
        refine ⟨2175497406332505146333891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5801326416886680390223709 2175497406332505146333891)
        ·
          refine ⟨3263246109498757719500837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175497406332505146333891 3263246109498757719500837)
          ·
            refine ⟨611858645531017072406407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3263246109498757719500837 611858645531017072406407)
            ·
              refine ⟨917787968296525608609611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611858645531017072406407 917787968296525608609611)
              ·
                refine ⟨1376681952444788412914417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917787968296525608609611 1376681952444788412914417)
                ·
                  refine ⟨1032511464333591309685813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1376681952444788412914417 1032511464333591309685813)
                  ·
                    refine ⟨96797949781274185283045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1032511464333591309685813 96797949781274185283045)
                    ·
                      rfl

theorem cell23_565540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_565540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565540 prefixEnd_565540 := by exact prefixLift 565540
  have htrace : WordTrace (prefixWord ++ tailWord_565540) baseStart_565540 baseEnd_565540 := by
    simpa [prefixWord, tailWord_565540, baseEnd_565540] using wordTrace_append hprefix tailTrace_565540
  have hstable : (prefixWord ++ tailWord_565540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565540).length < 2 ^ (prefixWord ++ tailWord_565540).sum := by decide
  have hdescent : baseEnd_565540 < baseStart_565540 := by decide
  rcases family_descends (prefixWord ++ tailWord_565540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565626 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_565626 : Nat := 118140960795 + 565626 * 2 ^ 59
def prefixEnd_565626 : Nat := 4983230072969 + 3 ^ 40 * 565626 * 2
def baseEnd_565626 : Nat := 96812669560036406457913

theorem tailTrace_565626 : CollatzResearch.WordTrace tailWord_565626 prefixEnd_565626 96812669560036406457913 := by
  unfold tailWord_565626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5157518762210269518773183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13753383365894052050061821 5157518762210269518773183)
  ·
    refine ⟨7736278143315404278159775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5157518762210269518773183 7736278143315404278159775)
    ·
      refine ⟨11604417214973106417239663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7736278143315404278159775 11604417214973106417239663)
      ·
        refine ⟨17406625822459659625859495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11604417214973106417239663 17406625822459659625859495)
        ·
          refine ⟨26109938733689489438789243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17406625822459659625859495 26109938733689489438789243)
          ·
            refine ⟨39164908100534234158183865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26109938733689489438789243 39164908100534234158183865)
            ·
              refine ⟨29373681075400675618637899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39164908100534234158183865 29373681075400675618637899)
              ·
                refine ⟨44060521613101013427956849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29373681075400675618637899 44060521613101013427956849)
                ·
                  refine ⟨33045391209825760070967637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44060521613101013427956849 33045391209825760070967637)
                  ·
                    refine ⟨96812669560036406457913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 33045391209825760070967637 96812669560036406457913)
                    ·
                      rfl

theorem cell23_565626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_565626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565626 prefixEnd_565626 := by exact prefixLift 565626
  have htrace : WordTrace (prefixWord ++ tailWord_565626) baseStart_565626 baseEnd_565626 := by
    simpa [prefixWord, tailWord_565626, baseEnd_565626] using wordTrace_append hprefix tailTrace_565626
  have hstable : (prefixWord ++ tailWord_565626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565626).length < 2 ^ (prefixWord ++ tailWord_565626).sum := by decide
  have hdescent : baseEnd_565626 < baseStart_565626 := by decide
  rcases family_descends (prefixWord ++ tailWord_565626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565627 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 3]
def baseStart_565627 : Nat := 118140960795 + 565627 * 2 ^ 59
def prefixEnd_565627 : Nat := 4983230072969 + 3 ^ 40 * 565627 * 2
def baseEnd_565627 : Nat := 290438522160763715461235

theorem tailTrace_565627 : CollatzResearch.WordTrace tailWord_565627 prefixEnd_565627 290438522160763715461235 := by
  unfold tailWord_565627
  simp only [CollatzResearch.WordTrace]
  refine ⟨20630111521837455245879135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13753407681224970163919423 20630111521837455245879135)
  ·
    refine ⟨30945167282756182868818703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20630111521837455245879135 30945167282756182868818703)
    ·
      refine ⟨46417750924134274303228055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30945167282756182868818703 46417750924134274303228055)
      ·
        refine ⟨69626626386201411454842083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46417750924134274303228055 69626626386201411454842083)
        ·
          refine ⟨104439939579302117182263125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69626626386201411454842083 104439939579302117182263125)
          ·
            refine ⟨611952770972473342864823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 104439939579302117182263125 611952770972473342864823)
            ·
              refine ⟨917929156458710014297235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611952770972473342864823 917929156458710014297235)
              ·
                refine ⟨1376893734688065021445853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917929156458710014297235 1376893734688065021445853)
                ·
                  refine ⟨516335150508024383042195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1376893734688065021445853 516335150508024383042195)
                  ·
                    refine ⟨774502725762036574563293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 516335150508024383042195 774502725762036574563293)
                    ·
                      refine ⟨290438522160763715461235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 774502725762036574563293 290438522160763715461235)
                      ·
                        rfl

theorem cell23_565627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 1, 3].length) (baseStart_565627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565627 prefixEnd_565627 := by exact prefixLift 565627
  have htrace : WordTrace (prefixWord ++ tailWord_565627) baseStart_565627 baseEnd_565627 := by
    simpa [prefixWord, tailWord_565627, baseEnd_565627] using wordTrace_append hprefix tailTrace_565627
  have hstable : (prefixWord ++ tailWord_565627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565627).length < 2 ^ (prefixWord ++ tailWord_565627).sum := by decide
  have hdescent : baseEnd_565627 < baseStart_565627 := by decide
  rcases family_descends (prefixWord ++ tailWord_565627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565667 : List Nat := [1, 1, 1, 4, 1, 5, 3, 1, 1, 1, 4]
def baseStart_565667 : Nat := 118140960795 + 565667 * 2 ^ 59
def prefixEnd_565667 : Nat := 4983230072969 + 3 ^ 40 * 565667 * 2
def baseEnd_565667 : Nat := 290459061386943558961051

theorem tailTrace_565667 : CollatzResearch.WordTrace tailWord_565667 prefixEnd_565667 290459061386943558961051 := by
  unfold tailWord_565667
  simp only [CollatzResearch.WordTrace]
  refine ⟨20631570441692542077335255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13754380294461694718223503 20631570441692542077335255)
  ·
    refine ⟨30947355662538813116002883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20631570441692542077335255 30947355662538813116002883)
    ·
      refine ⟨46421033493808219674004325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30947355662538813116002883 46421033493808219674004325)
      ·
        refine ⟨8703943780089041188875811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46421033493808219674004325 8703943780089041188875811)
        ·
          refine ⟨13055915670133561783313717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8703943780089041188875811 13055915670133561783313717)
          ·
            refine ⟨1223992094075021417185661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13055915670133561783313717 1223992094075021417185661)
            ·
              refine ⟨458997035278133031444623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1223992094075021417185661 458997035278133031444623)
              ·
                refine ⟨688495552917199547166935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458997035278133031444623 688495552917199547166935)
                ·
                  refine ⟨1032743329375799320750403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688495552917199547166935 1032743329375799320750403)
                  ·
                    refine ⟨1549114994063698981125605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1032743329375799320750403 1549114994063698981125605)
                    ·
                      refine ⟨290459061386943558961051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1549114994063698981125605 290459061386943558961051)
                      ·
                        rfl

theorem cell23_565667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_565667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565667 prefixEnd_565667 := by exact prefixLift 565667
  have htrace : WordTrace (prefixWord ++ tailWord_565667) baseStart_565667 baseEnd_565667 := by
    simpa [prefixWord, tailWord_565667, baseEnd_565667] using wordTrace_append hprefix tailTrace_565667
  have hstable : (prefixWord ++ tailWord_565667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565667).length < 2 ^ (prefixWord ++ tailWord_565667).sum := by decide
  have hdescent : baseEnd_565667 < baseStart_565667 := by decide
  rcases family_descends (prefixWord ++ tailWord_565667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565718 : List Nat := [5, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_565718 : Nat := 118140960795 + 565718 * 2 ^ 59
def prefixEnd_565718 : Nat := 4983230072969 + 3 ^ 40 * 565718 * 2
def baseEnd_565718 : Nat := 290485248900322859423317

theorem tailTrace_565718 : CollatzResearch.WordTrace tailWord_565718 prefixEnd_565718 290485248900322859423317 := by
  unfold tailWord_565718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289589410281736111715113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13755620376338518524961205 1289589410281736111715113)
  ·
    refine ⟨967192057711302083786335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1289589410281736111715113 967192057711302083786335)
    ·
      refine ⟨1450788086566953125679503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967192057711302083786335 1450788086566953125679503)
      ·
        refine ⟨2176182129850429688519255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450788086566953125679503 2176182129850429688519255)
        ·
          refine ⟨3264273194775644532778883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2176182129850429688519255 3264273194775644532778883)
          ·
            refine ⟨4896409792163466799168325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264273194775644532778883 4896409792163466799168325)
            ·
              refine ⟨918076836030650024844061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4896409792163466799168325 918076836030650024844061)
              ·
                refine ⟨344278813511493759316523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918076836030650024844061 344278813511493759316523)
                ·
                  refine ⟨516418220267240638974785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344278813511493759316523 516418220267240638974785)
                  ·
                    refine ⟨387313665200430479231089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 516418220267240638974785 387313665200430479231089)
                    ·
                      refine ⟨290485248900322859423317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387313665200430479231089 290485248900322859423317)
                      ·
                        rfl

theorem cell23_565718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_565718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565718 prefixEnd_565718 := by exact prefixLift 565718
  have htrace : WordTrace (prefixWord ++ tailWord_565718) baseStart_565718 baseEnd_565718 := by
    simpa [prefixWord, tailWord_565718, baseEnd_565718] using wordTrace_append hprefix tailTrace_565718
  have hstable : (prefixWord ++ tailWord_565718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565718).length < 2 ^ (prefixWord ++ tailWord_565718).sum := by decide
  have hdescent : baseEnd_565718 < baseStart_565718 := by decide
  rcases family_descends (prefixWord ++ tailWord_565718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565743 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_565743 : Nat := 118140960795 + 565743 * 2 ^ 59
def prefixEnd_565743 : Nat := 4983230072969 + 3 ^ 40 * 565743 * 2
def baseEnd_565743 : Nat := 290498085916685261610701

theorem tailTrace_565743 : CollatzResearch.WordTrace tailWord_565743 prefixEnd_565743 290498085916685261610701 := by
  unfold tailWord_565743
  simp only [CollatzResearch.WordTrace]
  refine ⟨20634342389417207057101883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13756228259611471371401255 20634342389417207057101883)
  ·
    refine ⟨30951513584125810585652825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20634342389417207057101883 30951513584125810585652825)
    ·
      refine ⟨23213635188094357939239619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30951513584125810585652825 23213635188094357939239619)
      ·
        refine ⟨34820452782141536908859429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23213635188094357939239619 34820452782141536908859429)
        ·
          refine ⟨6528834896651538170411143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34820452782141536908859429 6528834896651538170411143)
          ·
            refine ⟨9793252344977307255616715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6528834896651538170411143 9793252344977307255616715)
            ·
              refine ⟨14689878517465960883425073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9793252344977307255616715 14689878517465960883425073)
              ·
                refine ⟨11017408888099470662568805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14689878517465960883425073 11017408888099470662568805)
                ·
                  refine ⟨2065764166518650749231651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11017408888099470662568805 2065764166518650749231651)
                  ·
                    refine ⟨3098646249777976123847477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2065764166518650749231651 3098646249777976123847477)
                    ·
                      refine ⟨290498085916685261610701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3098646249777976123847477 290498085916685261610701)
                      ·
                        rfl

theorem cell23_565743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_565743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565743 prefixEnd_565743 := by exact prefixLift 565743
  have htrace : WordTrace (prefixWord ++ tailWord_565743) baseStart_565743 baseEnd_565743 := by
    simpa [prefixWord, tailWord_565743, baseEnd_565743] using wordTrace_append hprefix tailTrace_565743
  have hstable : (prefixWord ++ tailWord_565743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565743).length < 2 ^ (prefixWord ++ tailWord_565743).sum := by decide
  have hdescent : baseEnd_565743 < baseStart_565743 := by decide
  rcases family_descends (prefixWord ++ tailWord_565743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565750 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_565750 : Nat := 118140960795 + 565750 * 2 ^ 59
def prefixEnd_565750 : Nat := 4983230072969 + 3 ^ 40 * 565750 * 2
def baseEnd_565750 : Nat := 96833893427088911407723

theorem tailTrace_565750 : CollatzResearch.WordTrace tailWord_565750 prefixEnd_565750 96833893427088911407723 := by
  unfold tailWord_565750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289662356274490453287919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13756398466927898168404469 1289662356274490453287919)
  ·
    refine ⟨1934493534411735679931879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289662356274490453287919 1934493534411735679931879)
    ·
      refine ⟨2901740301617603519897819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934493534411735679931879 2901740301617603519897819)
      ·
        refine ⟨4352610452426405279846729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901740301617603519897819 4352610452426405279846729)
        ·
          refine ⟨3264457839319803959885047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4352610452426405279846729 3264457839319803959885047)
          ·
            refine ⟨4896686758979705939827571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264457839319803959885047 4896686758979705939827571)
            ·
              refine ⟨7345030138469558909741357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896686758979705939827571 7345030138469558909741357)
              ·
                refine ⟨2754386301926084591153009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7345030138469558909741357 2754386301926084591153009)
                ·
                  refine ⟨2065789726444563443364757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2754386301926084591153009 2065789726444563443364757)
                  ·
                    refine ⟨96833893427088911407723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2065789726444563443364757 96833893427088911407723)
                    ·
                      rfl

theorem cell23_565750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_565750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565750 prefixEnd_565750 := by exact prefixLift 565750
  have htrace : WordTrace (prefixWord ++ tailWord_565750) baseStart_565750 baseEnd_565750 := by
    simpa [prefixWord, tailWord_565750, baseEnd_565750] using wordTrace_append hprefix tailTrace_565750
  have hstable : (prefixWord ++ tailWord_565750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565750).length < 2 ^ (prefixWord ++ tailWord_565750).sum := by decide
  have hdescent : baseEnd_565750 < baseStart_565750 := by decide
  rcases family_descends (prefixWord ++ tailWord_565750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565763 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 7]
def baseStart_565763 : Nat := 118140960795 + 565763 * 2 ^ 59
def prefixEnd_565763 : Nat := 4983230072969 + 3 ^ 40 * 565763 * 2
def baseEnd_565763 : Nat := 32278706169975020373401

theorem tailTrace_565763 : CollatzResearch.WordTrace tailWord_565763 prefixEnd_565763 32278706169975020373401 := by
  unfold tailWord_565763
  simp only [CollatzResearch.WordTrace]
  refine ⟨20635071849344750472829943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13756714566229833648553295 20635071849344750472829943)
  ·
    refine ⟨30952607774017125709244915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20635071849344750472829943 30952607774017125709244915)
    ·
      refine ⟨46428911661025688563867373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30952607774017125709244915 46428911661025688563867373)
      ·
        refine ⟨17410841872884633211450265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46428911661025688563867373 17410841872884633211450265)
        ·
          refine ⟨13058131404663474908587699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17410841872884633211450265 13058131404663474908587699)
          ·
            refine ⟨19587197106995212362881549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13058131404663474908587699 19587197106995212362881549)
            ·
              refine ⟨7345198915123204636080581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19587197106995212362881549 7345198915123204636080581)
              ·
                refine ⟨1377224796585600869265109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7345198915123204636080581 1377224796585600869265109)
                ·
                  refine ⟨32278706169975020373401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1377224796585600869265109 32278706169975020373401)
                  ·
                    rfl

theorem cell23_565763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 7].length) (baseStart_565763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565763 prefixEnd_565763 := by exact prefixLift 565763
  have htrace : WordTrace (prefixWord ++ tailWord_565763) baseStart_565763 baseEnd_565763 := by
    simpa [prefixWord, tailWord_565763, baseEnd_565763] using wordTrace_append hprefix tailTrace_565763
  have hstable : (prefixWord ++ tailWord_565763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565763).length < 2 ^ (prefixWord ++ tailWord_565763).sum := by decide
  have hdescent : baseEnd_565763 < baseStart_565763 := by decide
  rcases family_descends (prefixWord ++ tailWord_565763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565774 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_565774 : Nat := 118140960795 + 565774 * 2 ^ 59
def prefixEnd_565774 : Nat := 4983230072969 + 3 ^ 40 * 565774 * 2
def baseEnd_565774 : Nat := 290514003816974640323059

theorem tailTrace_565774 : CollatzResearch.WordTrace tailWord_565774 prefixEnd_565774 290514003816974640323059 := by
  unfold tailWord_565774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579434131538112418935047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13756982034869932900986917 2579434131538112418935047)
  ·
    refine ⟨3869151197307168628402571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2579434131538112418935047 3869151197307168628402571)
    ·
      refine ⟨5803726795960752942603857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3869151197307168628402571 5803726795960752942603857)
      ·
        refine ⟨4352795096970564706952893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5803726795960752942603857 4352795096970564706952893)
        ·
          refine ⟨1632298161363961765107335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4352795096970564706952893 1632298161363961765107335)
          ·
            refine ⟨2448447242045942647661003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632298161363961765107335 2448447242045942647661003)
            ·
              refine ⟨3672670863068913971491505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2448447242045942647661003 3672670863068913971491505)
              ·
                refine ⟨2754503147301685478618629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3672670863068913971491505 2754503147301685478618629)
                ·
                  refine ⟨516469340119066027240993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2754503147301685478618629 516469340119066027240993)
                  ·
                    refine ⟨387352005089299520430745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 516469340119066027240993 387352005089299520430745)
                    ·
                      refine ⟨290514003816974640323059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387352005089299520430745 290514003816974640323059)
                      ·
                        rfl

theorem cell23_565774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_565774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565774 prefixEnd_565774 := by exact prefixLift 565774
  have htrace : WordTrace (prefixWord ++ tailWord_565774) baseStart_565774 baseEnd_565774 := by
    simpa [prefixWord, tailWord_565774, baseEnd_565774] using wordTrace_append hprefix tailTrace_565774
  have hstable : (prefixWord ++ tailWord_565774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565774).length < 2 ^ (prefixWord ++ tailWord_565774).sum := by decide
  have hdescent : baseEnd_565774 < baseStart_565774 := by decide
  rcases family_descends (prefixWord ++ tailWord_565774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565833 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_565833 : Nat := 118140960795 + 565833 * 2 ^ 59
def prefixEnd_565833 : Nat := 4983230072969 + 3 ^ 40 * 565833 * 2
def baseEnd_565833 : Nat := 290544299175589909485287

theorem tailTrace_565833 : CollatzResearch.WordTrace tailWord_565833 prefixEnd_565833 290544299175589909485287 := by
  unfold tailWord_565833
  simp only [CollatzResearch.WordTrace]
  refine ⟨20637624959091152427878153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13758416639394101618585435 20637624959091152427878153)
  ·
    refine ⟨15478218719318364320908615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20637624959091152427878153 15478218719318364320908615)
    ·
      refine ⟨23217328078977546481362923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15478218719318364320908615 23217328078977546481362923)
      ·
        refine ⟨34825992118466319722044385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23217328078977546481362923 34825992118466319722044385)
        ·
          refine ⟨26119494088849739791533289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34825992118466319722044385 26119494088849739791533289)
          ·
            refine ⟨19589620566637304843649967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26119494088849739791533289 19589620566637304843649967)
            ·
              refine ⟨29384430849955957265474951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19589620566637304843649967 29384430849955957265474951)
              ·
                refine ⟨44076646274933935898212427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29384430849955957265474951 44076646274933935898212427)
                ·
                  refine ⟨66114969412400903847318641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44076646274933935898212427 66114969412400903847318641)
                  ·
                    refine ⟨49586227059300677885488981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66114969412400903847318641 49586227059300677885488981)
                    ·
                      refine ⟨290544299175589909485287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 49586227059300677885488981 290544299175589909485287)
                      ·
                        rfl

theorem cell23_565833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_565833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565833 prefixEnd_565833 := by exact prefixLift 565833
  have htrace : WordTrace (prefixWord ++ tailWord_565833) baseStart_565833 baseEnd_565833 := by
    simpa [prefixWord, tailWord_565833, baseEnd_565833] using wordTrace_append hprefix tailTrace_565833
  have hstable : (prefixWord ++ tailWord_565833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565833).length < 2 ^ (prefixWord ++ tailWord_565833).sum := by decide
  have hdescent : baseEnd_565833 < baseStart_565833 := by decide
  rcases family_descends (prefixWord ++ tailWord_565833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565837 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_565837 : Nat := 118140960795 + 565837 * 2 ^ 59
def prefixEnd_565837 : Nat := 4983230072969 + 3 ^ 40 * 565837 * 2
def baseEnd_565837 : Nat := 290546353098207893835269

theorem tailTrace_565837 : CollatzResearch.WordTrace tailWord_565837 prefixEnd_565837 290546353098207893835269 := by
  unfold tailWord_565837
  simp only [CollatzResearch.WordTrace]
  refine ⟨20637770851076661111023765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13758513900717774074015843 20637770851076661111023765)
  ·
    refine ⟨967395508644218489579239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20637770851076661111023765 967395508644218489579239)
    ·
      refine ⟨1451093262966327734368859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967395508644218489579239 1451093262966327734368859)
      ·
        refine ⟨2176639894449491601553289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451093262966327734368859 2176639894449491601553289)
        ·
          refine ⟨1632479920837118701164967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2176639894449491601553289 1632479920837118701164967)
          ·
            refine ⟨2448719881255678051747451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632479920837118701164967 2448719881255678051747451)
            ·
              refine ⟨3673079821883517077621177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2448719881255678051747451 3673079821883517077621177)
              ·
                refine ⟨2754809866412637808215883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3673079821883517077621177 2754809866412637808215883)
                ·
                  refine ⟨4132214799618956712323825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2754809866412637808215883 4132214799618956712323825)
                  ·
                    refine ⟨3099161099714217534242869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4132214799618956712323825 3099161099714217534242869)
                    ·
                      refine ⟨290546353098207893835269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3099161099714217534242869 290546353098207893835269)
                      ·
                        rfl

theorem cell23_565837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_565837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565837 prefixEnd_565837 := by exact prefixLift 565837
  have htrace : WordTrace (prefixWord ++ tailWord_565837) baseStart_565837 baseEnd_565837 := by
    simpa [prefixWord, tailWord_565837, baseEnd_565837] using wordTrace_append hprefix tailTrace_565837
  have hstable : (prefixWord ++ tailWord_565837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565837).length < 2 ^ (prefixWord ++ tailWord_565837).sum := by decide
  have hdescent : baseEnd_565837 < baseStart_565837 := by decide
  rcases family_descends (prefixWord ++ tailWord_565837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565840 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 7, 4]
def baseStart_565840 : Nat := 118140960795 + 565840 * 2 ^ 59
def prefixEnd_565840 : Nat := 4983230072969 + 3 ^ 40 * 565840 * 2
def baseEnd_565840 : Nat := 96849297846723794032585

theorem tailTrace_565840 : CollatzResearch.WordTrace tailWord_565840 prefixEnd_565840 96849297846723794032585 := by
  unfold tailWord_565840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10318940135032896311691487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13758586846710528415588649 10318940135032896311691487)
  ·
    refine ⟨15478410202549344467537231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10318940135032896311691487 15478410202549344467537231)
    ·
      refine ⟨23217615303824016701305847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15478410202549344467537231 23217615303824016701305847)
      ·
        refine ⟨34826422955736025051958771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23217615303824016701305847 34826422955736025051958771)
        ·
          refine ⟨52239634433604037577938157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34826422955736025051958771 52239634433604037577938157)
          ·
            refine ⟨19589862912601514091726809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52239634433604037577938157 19589862912601514091726809)
            ·
              refine ⟨14692397184451135568795107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19589862912601514091726809 14692397184451135568795107)
              ·
                refine ⟨22038595776676703353192661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14692397184451135568795107 22038595776676703353192661)
                ·
                  refine ⟨516529588515860234840453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 22038595776676703353192661 516529588515860234840453)
                  ·
                    refine ⟨96849297846723794032585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516529588515860234840453 96849297846723794032585)
                    ·
                      rfl

theorem cell23_565840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 4].length) (baseStart_565840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565840 prefixEnd_565840 := by exact prefixLift 565840
  have htrace : WordTrace (prefixWord ++ tailWord_565840) baseStart_565840 baseEnd_565840 := by
    simpa [prefixWord, tailWord_565840, baseEnd_565840] using wordTrace_append hprefix tailTrace_565840
  have hstable : (prefixWord ++ tailWord_565840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565840).length < 2 ^ (prefixWord ++ tailWord_565840).sum := by decide
  have hdescent : baseEnd_565840 < baseStart_565840 := by decide
  rcases family_descends (prefixWord ++ tailWord_565840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565847 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 2, 4, 2]
def baseStart_565847 : Nat := 118140960795 + 565847 * 2 ^ 59
def prefixEnd_565847 : Nat := 4983230072969 + 3 ^ 40 * 565847 * 2
def baseEnd_565847 : Nat := 290551487904752854710223

theorem tailTrace_565847 : CollatzResearch.WordTrace tailWord_565847 prefixEnd_565847 290551487904752854710223 := by
  unfold tailWord_565847
  simp only [CollatzResearch.WordTrace]
  refine ⟨20638135581040432818887795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13758757054026955212591863 20638135581040432818887795)
  ·
    refine ⟨30957203371560649228331693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20638135581040432818887795 30957203371560649228331693)
    ·
      refine ⟨11608951264335243460624385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30957203371560649228331693 11608951264335243460624385)
      ·
        refine ⟨8706713448251432595468289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11608951264335243460624385 8706713448251432595468289)
        ·
          refine ⟨6530035086188574446601217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8706713448251432595468289 6530035086188574446601217)
          ·
            refine ⟨4897526314641430834950913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6530035086188574446601217 4897526314641430834950913)
            ·
              refine ⟨3673144735981073126213185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4897526314641430834950913 3673144735981073126213185)
              ·
                refine ⟨2754858551985804844659889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3673144735981073126213185 2754858551985804844659889)
                ·
                  refine ⟨2066143913989353633494917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2754858551985804844659889 2066143913989353633494917)
                  ·
                    refine ⟨387401983873003806280297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2066143913989353633494917 387401983873003806280297)
                    ·
                      refine ⟨290551487904752854710223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387401983873003806280297 290551487904752854710223)
                      ·
                        rfl

theorem cell23_565847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_565847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565847 prefixEnd_565847 := by exact prefixLift 565847
  have htrace : WordTrace (prefixWord ++ tailWord_565847) baseStart_565847 baseEnd_565847 := by
    simpa [prefixWord, tailWord_565847, baseEnd_565847] using wordTrace_append hprefix tailTrace_565847
  have hstable : (prefixWord ++ tailWord_565847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565847).length < 2 ^ (prefixWord ++ tailWord_565847).sum := by decide
  have hdescent : baseEnd_565847 < baseStart_565847 := by decide
  rcases family_descends (prefixWord ++ tailWord_565847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565850 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_565850 : Nat := 118140960795 + 565850 * 2 ^ 59
def prefixEnd_565850 : Nat := 4983230072969 + 3 ^ 40 * 565850 * 2
def baseEnd_565850 : Nat := 290553028346716342972709

theorem tailTrace_565850 : CollatzResearch.WordTrace tailWord_565850 prefixEnd_565850 290553028346716342972709 := by
  unfold tailWord_565850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159561250007391082811751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13758830000019709554164669 5159561250007391082811751)
  ·
    refine ⟨7739341875011086624217627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5159561250007391082811751 7739341875011086624217627)
    ·
      refine ⟨11609012812516629936326441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7739341875011086624217627 11609012812516629936326441)
      ·
        refine ⟨8706759609387472452244831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11609012812516629936326441 8706759609387472452244831)
        ·
          refine ⟨13060139414081208678367247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8706759609387472452244831 13060139414081208678367247)
          ·
            refine ⟨19590209121121813017550871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13060139414081208678367247 19590209121121813017550871)
            ·
              refine ⟨29385313681682719526326307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19590209121121813017550871 29385313681682719526326307)
              ·
                refine ⟨44077970522524079289489461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29385313681682719526326307 44077970522524079289489461)
                ·
                  refine ⟨4132309736486632433389637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44077970522524079289489461 4132309736486632433389637)
                  ·
                    refine ⟨774808075591243581260557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4132309736486632433389637 774808075591243581260557)
                    ·
                      refine ⟨290553028346716342972709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 774808075591243581260557 290553028346716342972709)
                      ·
                        rfl

theorem cell23_565850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_565850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565850 prefixEnd_565850 := by exact prefixLift 565850
  have htrace : WordTrace (prefixWord ++ tailWord_565850) baseStart_565850 baseEnd_565850 := by
    simpa [prefixWord, tailWord_565850, baseEnd_565850] using wordTrace_append hprefix tailTrace_565850
  have hstable : (prefixWord ++ tailWord_565850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565850).length < 2 ^ (prefixWord ++ tailWord_565850).sum := by decide
  have hdescent : baseEnd_565850 < baseStart_565850 := by decide
  rcases family_descends (prefixWord ++ tailWord_565850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565874 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_565874 : Nat := 118140960795 + 565874 * 2 ^ 59
def prefixEnd_565874 : Nat := 4983230072969 + 3 ^ 40 * 565874 * 2
def baseEnd_565874 : Nat := 96855117294141416357533

theorem tailTrace_565874 : CollatzResearch.WordTrace tailWord_565874 prefixEnd_565874 96855117294141416357533 := by
  unfold tailWord_565874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159780087985654107530169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13759413567961744286747117 5159780087985654107530169)
  ·
    refine ⟨3869835065989240580647627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5159780087985654107530169 3869835065989240580647627)
    ·
      refine ⟨5804752598983860870971441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3869835065989240580647627 5804752598983860870971441)
      ·
        refine ⟨4353564449237895653228581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5804752598983860870971441 4353564449237895653228581)
        ·
          refine ⟨816293334232105434980359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4353564449237895653228581 816293334232105434980359)
          ·
            refine ⟨1224440001348158152470539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816293334232105434980359 1224440001348158152470539)
            ·
              refine ⟨1836660002022237228705809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224440001348158152470539 1836660002022237228705809)
              ·
                refine ⟨1377495001516677921529357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836660002022237228705809 1377495001516677921529357)
                ·
                  refine ⟨516560625568754220573509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1377495001516677921529357 516560625568754220573509)
                  ·
                    refine ⟨96855117294141416357533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516560625568754220573509 96855117294141416357533)
                    ·
                      rfl

theorem cell23_565874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_565874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565874 prefixEnd_565874 := by exact prefixLift 565874
  have htrace : WordTrace (prefixWord ++ tailWord_565874) baseStart_565874 baseEnd_565874 := by
    simpa [prefixWord, tailWord_565874, baseEnd_565874] using wordTrace_append hprefix tailTrace_565874
  have hstable : (prefixWord ++ tailWord_565874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565874).length < 2 ^ (prefixWord ++ tailWord_565874).sum := by decide
  have hdescent : baseEnd_565874 < baseStart_565874 := by decide
  rcases family_descends (prefixWord ++ tailWord_565874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565880 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 2, 5, 3]
def baseStart_565880 : Nat := 118140960795 + 565880 * 2 ^ 59
def prefixEnd_565880 : Nat := 4983230072969 + 3 ^ 40 * 565880 * 2
def baseEnd_565880 : Nat := 290568432766351225597571

theorem tailTrace_565880 : CollatzResearch.WordTrace tailWord_565880 prefixEnd_565880 290568432766351225597571 := by
  unfold tailWord_565880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10319669594960439727419547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13759559459947252969892729 10319669594960439727419547)
  ·
    refine ⟨15479504392440659591129321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10319669594960439727419547 15479504392440659591129321)
    ·
      refine ⟨11609628294330494693346991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15479504392440659591129321 11609628294330494693346991)
      ·
        refine ⟨17414442441495742040020487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11609628294330494693346991 17414442441495742040020487)
        ·
          refine ⟨26121663662243613060030731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17414442441495742040020487 26121663662243613060030731)
          ·
            refine ⟨39182495493365419590046097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26121663662243613060030731 39182495493365419590046097)
            ·
              refine ⟨29386871620024064692534573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39182495493365419590046097 29386871620024064692534573)
              ·
                refine ⟨11020076857509024259700465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29386871620024064692534573 11020076857509024259700465)
                ·
                  refine ⟨8265057643131768194775349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11020076857509024259700465 8265057643131768194775349)
                  ·
                    refine ⟨774849154043603268260189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8265057643131768194775349 774849154043603268260189)
                    ·
                      refine ⟨290568432766351225597571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 774849154043603268260189 290568432766351225597571)
                      ·
                        rfl

theorem cell23_565880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_565880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565880 prefixEnd_565880 := by exact prefixLift 565880
  have htrace : WordTrace (prefixWord ++ tailWord_565880) baseStart_565880 baseEnd_565880 := by
    simpa [prefixWord, tailWord_565880, baseEnd_565880] using wordTrace_append hprefix tailTrace_565880
  have hstable : (prefixWord ++ tailWord_565880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565880).length < 2 ^ (prefixWord ++ tailWord_565880).sum := by decide
  have hdescent : baseEnd_565880 < baseStart_565880 := by decide
  rcases family_descends (prefixWord ++ tailWord_565880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565897 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 3]
def baseStart_565897 : Nat := 118140960795 + 565897 * 2 ^ 59
def prefixEnd_565897 : Nat := 4983230072969 + 3 ^ 40 * 565897 * 2
def baseEnd_565897 : Nat := 290577161937477659084993

theorem tailTrace_565897 : CollatzResearch.WordTrace tailWord_565897 prefixEnd_565897 290577161937477659084993 := by
  unfold tailWord_565897
  simp only [CollatzResearch.WordTrace]
  refine ⟨20639959230859291358207945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13759972820572860905471963 20639959230859291358207945)
  ·
    refine ⟨15479969423144468518655959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20639959230859291358207945 15479969423144468518655959)
    ·
      refine ⟨23219954134716702777983939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15479969423144468518655959 23219954134716702777983939)
      ·
        refine ⟨34829931202075054166975909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23219954134716702777983939 34829931202075054166975909)
        ·
          refine ⟨6530612100389072656307983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34829931202075054166975909 6530612100389072656307983)
          ·
            refine ⟨9795918150583608984461975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6530612100389072656307983 9795918150583608984461975)
            ·
              refine ⟨14693877225875413476692963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9795918150583608984461975 14693877225875413476692963)
              ·
                refine ⟨22040815838813120215039445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14693877225875413476692963 22040815838813120215039445)
                ·
                  refine ⟨516581621222182505039987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 22040815838813120215039445 516581621222182505039987)
                  ·
                    refine ⟨774872431833273757559981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 516581621222182505039987 774872431833273757559981)
                    ·
                      refine ⟨290577161937477659084993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 774872431833273757559981 290577161937477659084993)
                      ·
                        rfl

theorem cell23_565897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 3].length) (baseStart_565897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565897 prefixEnd_565897 := by exact prefixLift 565897
  have htrace : WordTrace (prefixWord ++ tailWord_565897) baseStart_565897 baseEnd_565897 := by
    simpa [prefixWord, tailWord_565897, baseEnd_565897] using wordTrace_append hprefix tailTrace_565897
  have hstable : (prefixWord ++ tailWord_565897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565897).length < 2 ^ (prefixWord ++ tailWord_565897).sum := by decide
  have hdescent : baseEnd_565897 < baseStart_565897 := by decide
  rcases family_descends (prefixWord ++ tailWord_565897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565900 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_565900 : Nat := 118140960795 + 565900 * 2 ^ 59
def prefixEnd_565900 : Nat := 4983230072969 + 3 ^ 40 * 565900 * 2
def baseEnd_565900 : Nat := 96859567459813715782493

theorem tailTrace_565900 : CollatzResearch.WordTrace tailWord_565900 prefixEnd_565900 96859567459813715782493 := by
  unfold tailWord_565900
  simp only [CollatzResearch.WordTrace]
  refine ⟨10320034324924211435283577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13760045766565615247044769 10320034324924211435283577)
  ·
    refine ⟨7740025743693158576462683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10320034324924211435283577 7740025743693158576462683)
    ·
      refine ⟨11610038615539737864694025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7740025743693158576462683 11610038615539737864694025)
      ·
        refine ⟨8707528961654803398520519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11610038615539737864694025 8707528961654803398520519)
        ·
          refine ⟨13061293442482205097780779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8707528961654803398520519 13061293442482205097780779)
          ·
            refine ⟨19591940163723307646671169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13061293442482205097780779 19591940163723307646671169)
            ·
              refine ⟨14693955122792480735003377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19591940163723307646671169 14693955122792480735003377)
              ·
                refine ⟨11020466342094360551252533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14693955122792480735003377 11020466342094360551252533)
                ·
                  refine ⟨1033168719571346301679925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11020466342094360551252533 1033168719571346301679925)
                  ·
                    refine ⟨96859567459813715782493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1033168719571346301679925 96859567459813715782493)
                    ·
                      rfl

theorem cell23_565900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_565900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565900 prefixEnd_565900 := by exact prefixLift 565900
  have htrace : WordTrace (prefixWord ++ tailWord_565900) baseStart_565900 baseEnd_565900 := by
    simpa [prefixWord, tailWord_565900, baseEnd_565900] using wordTrace_append hprefix tailTrace_565900
  have hstable : (prefixWord ++ tailWord_565900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565900).length < 2 ^ (prefixWord ++ tailWord_565900).sum := by decide
  have hdescent : baseEnd_565900 < baseStart_565900 := by decide
  rcases family_descends (prefixWord ++ tailWord_565900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565942 : List Nat := [5, 1, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_565942 : Nat := 118140960795 + 565942 * 2 ^ 59
def prefixEnd_565942 : Nat := 4983230072969 + 3 ^ 40 * 565942 * 2
def baseEnd_565942 : Nat := 96866756188976661007429

theorem tailTrace_565942 : CollatzResearch.WordTrace tailWord_565942 prefixEnd_565942 96866756188976661007429 := by
  unfold tailWord_565942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290100032231016502724755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13761067010464176029064053 1290100032231016502724755)
  ·
    refine ⟨1935150048346524754087133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290100032231016502724755 1935150048346524754087133)
    ·
      refine ⟨725681268129946782782675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1935150048346524754087133 725681268129946782782675)
      ·
        refine ⟨1088521902194920174174013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725681268129946782782675 1088521902194920174174013)
        ·
          refine ⟨408195713323095065315255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1088521902194920174174013 408195713323095065315255)
          ·
            refine ⟨612293569984642597972883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408195713323095065315255 612293569984642597972883)
            ·
              refine ⟨918440354976963896959325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612293569984642597972883 918440354976963896959325)
              ·
                refine ⟨344415133116361461359747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918440354976963896959325 344415133116361461359747)
                ·
                  refine ⟨516622699674542192039621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344415133116361461359747 516622699674542192039621)
                  ·
                    refine ⟨96866756188976661007429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516622699674542192039621 96866756188976661007429)
                    ·
                      rfl

theorem cell23_565942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_565942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565942 prefixEnd_565942 := by exact prefixLift 565942
  have htrace : WordTrace (prefixWord ++ tailWord_565942) baseStart_565942 baseEnd_565942 := by
    simpa [prefixWord, tailWord_565942, baseEnd_565942] using wordTrace_append hprefix tailTrace_565942
  have hstable : (prefixWord ++ tailWord_565942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565942).length < 2 ^ (prefixWord ++ tailWord_565942).sum := by decide
  have hdescent : baseEnd_565942 < baseStart_565942 := by decide
  rcases family_descends (prefixWord ++ tailWord_565942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565960 : List Nat := [2, 1, 3, 1, 2, 3, 11]
def baseStart_565960 : Nat := 118140960795 + 565960 * 2 ^ 59
def prefixEnd_565960 : Nat := 4983230072969 + 3 ^ 40 * 565960 * 2
def baseEnd_565960 : Nat := 3587771743440875464163

theorem tailTrace_565960 : CollatzResearch.WordTrace tailWord_565960 prefixEnd_565960 3587771743440875464163 := by
  unfold tailWord_565960
  simp only [CollatzResearch.WordTrace]
  refine ⟨10321128514815526558875667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13761504686420702078500889 10321128514815526558875667)
  ·
    refine ⟨15481692772223289838313501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10321128514815526558875667 15481692772223289838313501)
    ·
      refine ⟨5805634789583733689367563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15481692772223289838313501 5805634789583733689367563)
      ·
        refine ⟨8708452184375600534051345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5805634789583733689367563 8708452184375600534051345)
        ·
          refine ⟨6531339138281700400538509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8708452184375600534051345 6531339138281700400538509)
          ·
            refine ⟨2449252176855637650201941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6531339138281700400538509 2449252176855637650201941)
            ·
              refine ⟨3587771743440875464163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2449252176855637650201941 3587771743440875464163)
              ·
                rfl

theorem cell23_565960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 11].length) (baseStart_565960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565960 prefixEnd_565960 := by exact prefixLift 565960
  have htrace : WordTrace (prefixWord ++ tailWord_565960) baseStart_565960 baseEnd_565960 := by
    simpa [prefixWord, tailWord_565960, baseEnd_565960] using wordTrace_append hprefix tailTrace_565960
  have hstable : (prefixWord ++ tailWord_565960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565960).length < 2 ^ (prefixWord ++ tailWord_565960).sum := by decide
  have hdescent : baseEnd_565960 < baseStart_565960 := by decide
  rcases family_descends (prefixWord ++ tailWord_565960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565964 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_565964 : Nat := 118140960795 + 565964 * 2 ^ 59
def prefixEnd_565964 : Nat := 4983230072969 + 3 ^ 40 * 565964 * 2
def baseEnd_565964 : Nat := 96870521713776298982395

theorem tailTrace_565964 : CollatzResearch.WordTrace tailWord_565964 prefixEnd_565964 96870521713776298982395 := by
  unfold tailWord_565964
  simp only [CollatzResearch.WordTrace]
  refine ⟨10321201460808280900448473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13761601947744374533931297 10321201460808280900448473)
  ·
    refine ⟨7740901095606210675336355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10321201460808280900448473 7740901095606210675336355)
    ·
      refine ⟨11611351643409316013004533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7740901095606210675336355 11611351643409316013004533)
      ·
        refine ⟨1088564216569623376219175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11611351643409316013004533 1088564216569623376219175)
        ·
          refine ⟨1632846324854435064328763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088564216569623376219175 1632846324854435064328763)
          ·
            refine ⟨2449269487281652596493145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632846324854435064328763 2449269487281652596493145)
            ·
              refine ⟨1836952115461239447369859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449269487281652596493145 1836952115461239447369859)
              ·
                refine ⟨2755428173191859171054789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1836952115461239447369859 2755428173191859171054789)
                ·
                  refine ⟨516642782473473594572773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2755428173191859171054789 516642782473473594572773)
                  ·
                    refine ⟨96870521713776298982395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516642782473473594572773 96870521713776298982395)
                    ·
                      rfl

theorem cell23_565964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_565964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565964 prefixEnd_565964 := by exact prefixLift 565964
  have htrace : WordTrace (prefixWord ++ tailWord_565964) baseStart_565964 baseEnd_565964 := by
    simpa [prefixWord, tailWord_565964, baseEnd_565964] using wordTrace_append hprefix tailTrace_565964
  have hstable : (prefixWord ++ tailWord_565964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565964).length < 2 ^ (prefixWord ++ tailWord_565964).sum := by decide
  have hdescent : baseEnd_565964 < baseStart_565964 := by decide
  rcases family_descends (prefixWord ++ tailWord_565964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_565965 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_565965 : Nat := 118140960795 + 565965 * 2 ^ 59
def prefixEnd_565965 : Nat := 4983230072969 + 3 ^ 40 * 565965 * 2
def baseEnd_565965 : Nat := 290612078621983393034681

theorem tailTrace_565965 : CollatzResearch.WordTrace tailWord_565965 prefixEnd_565965 290612078621983393034681 := by
  unfold tailWord_565965
  simp only [CollatzResearch.WordTrace]
  refine ⟨20642439394612938971683349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13761626263075292647788899 20642439394612938971683349)
  ·
    refine ⟨967614346622481514297657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20642439394612938971683349 967614346622481514297657)
    ·
      refine ⟨725710759966861135723243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 967614346622481514297657 725710759966861135723243)
      ·
        refine ⟨1088566139950291703584865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725710759966861135723243 1088566139950291703584865)
        ·
          refine ⟨816424604962718777688649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088566139950291703584865 816424604962718777688649)
          ·
            refine ⟨612318453722039083266487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816424604962718777688649 612318453722039083266487)
            ·
              refine ⟨918477680583058624899731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612318453722039083266487 918477680583058624899731)
              ·
                refine ⟨1377716520874587937349597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918477680583058624899731 1377716520874587937349597)
                ·
                  refine ⟨516643695327970476506099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1377716520874587937349597 516643695327970476506099)
                  ·
                    refine ⟨774965542991955714759149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 516643695327970476506099 774965542991955714759149)
                    ·
                      refine ⟨290612078621983393034681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 774965542991955714759149 290612078621983393034681)
                      ·
                        rfl

theorem cell23_565965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_565965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_565965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_565965 prefixEnd_565965 := by exact prefixLift 565965
  have htrace : WordTrace (prefixWord ++ tailWord_565965) baseStart_565965 baseEnd_565965 := by
    simpa [prefixWord, tailWord_565965, baseEnd_565965] using wordTrace_append hprefix tailTrace_565965
  have hstable : (prefixWord ++ tailWord_565965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_565965).length < 2 ^ (prefixWord ++ tailWord_565965).sum := by decide
  have hdescent : baseEnd_565965 < baseStart_565965 := by decide
  rcases family_descends (prefixWord ++ tailWord_565965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566037 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_566037 : Nat := 118140960795 + 566037 * 2 ^ 59
def prefixEnd_566037 : Nat := 4983230072969 + 3 ^ 40 * 566037 * 2
def baseEnd_566037 : Nat := 96883016409702370444783

theorem tailTrace_566037 : CollatzResearch.WordTrace tailWord_566037 prefixEnd_566037 96883016409702370444783 := by
  unfold tailWord_566037
  simp only [CollatzResearch.WordTrace]
  refine ⟨20645065450352095268304365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13763376966901396845536243 20645065450352095268304365)
  ·
    refine ⟨7741899543882035725614137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20645065450352095268304365 7741899543882035725614137)
    ·
      refine ⟨5806424657911526794210603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7741899543882035725614137 5806424657911526794210603)
      ·
        refine ⟨8709636986867290191315905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5806424657911526794210603 8709636986867290191315905)
        ·
          refine ⟨6532227740150467643486929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8709636986867290191315905 6532227740150467643486929)
          ·
            refine ⟨4899170805112850732615197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6532227740150467643486929 4899170805112850732615197)
            ·
              refine ⟨1837189051917319024730699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4899170805112850732615197 1837189051917319024730699)
              ·
                refine ⟨2755783577875978537096049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837189051917319024730699 2755783577875978537096049)
                ·
                  refine ⟨2066837683406983902822037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2755783577875978537096049 2066837683406983902822037)
                  ·
                    refine ⟨96883016409702370444783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2066837683406983902822037 96883016409702370444783)
                    ·
                      rfl

theorem cell23_566037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_566037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566037 prefixEnd_566037 := by exact prefixLift 566037
  have htrace : WordTrace (prefixWord ++ tailWord_566037) baseStart_566037 baseEnd_566037 := by
    simpa [prefixWord, tailWord_566037, baseEnd_566037] using wordTrace_append hprefix tailTrace_566037
  have hstable : (prefixWord ++ tailWord_566037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566037).length < 2 ^ (prefixWord ++ tailWord_566037).sum := by decide
  have hdescent : baseEnd_566037 < baseStart_566037 := by decide
  rcases family_descends (prefixWord ++ tailWord_566037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566104 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 2, 5, 2]
def baseStart_566104 : Nat := 118140960795 + 566104 * 2 ^ 59
def prefixEnd_566104 : Nat := 4983230072969 + 3 ^ 40 * 566104 * 2
def baseEnd_566104 : Nat := 290683452432958349196541

theorem tailTrace_566104 : CollatzResearch.WordTrace tailWord_566104 prefixEnd_566104 290683452432958349196541 := by
  unfold tailWord_566104
  simp only [CollatzResearch.WordTrace]
  refine ⟨10323754570554682855496683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13765006094072910473995577 10323754570554682855496683)
  ·
    refine ⟨15485631855832024283245025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10323754570554682855496683 15485631855832024283245025)
    ·
      refine ⟨11614223891874018212433769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15485631855832024283245025 11614223891874018212433769)
      ·
        refine ⟨8710667918905513659325327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11614223891874018212433769 8710667918905513659325327)
        ·
          refine ⟨13066001878358270488987991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8710667918905513659325327 13066001878358270488987991)
          ·
            refine ⟨19599002817537405733481987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13066001878358270488987991 19599002817537405733481987)
            ·
              refine ⟨29398504226306108600222981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19599002817537405733481987 29398504226306108600222981)
              ·
                refine ⟨5512219542432395362541809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29398504226306108600222981 5512219542432395362541809)
                ·
                  refine ⟨4134164656824296521906357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5512219542432395362541809 4134164656824296521906357)
                  ·
                    refine ⟨387577936577277798928721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4134164656824296521906357 387577936577277798928721)
                    ·
                      refine ⟨290683452432958349196541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387577936577277798928721 290683452432958349196541)
                      ·
                        rfl

theorem cell23_566104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_566104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566104 prefixEnd_566104 := by exact prefixLift 566104
  have htrace : WordTrace (prefixWord ++ tailWord_566104) baseStart_566104 baseEnd_566104 := by
    simpa [prefixWord, tailWord_566104, baseEnd_566104] using wordTrace_append hprefix tailTrace_566104
  have hstable : (prefixWord ++ tailWord_566104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566104).length < 2 ^ (prefixWord ++ tailWord_566104).sum := by decide
  have hdescent : baseEnd_566104 < baseStart_566104 := by decide
  rcases family_descends (prefixWord ++ tailWord_566104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566144 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 3, 4]
def baseStart_566144 : Nat := 118140960795 + 566144 * 2 ^ 59
def prefixEnd_566144 : Nat := 4983230072969 + 3 ^ 40 * 566144 * 2
def baseEnd_566144 : Nat := 96901330553046064232119

theorem tailTrace_566144 : CollatzResearch.WordTrace tailWord_566144 prefixEnd_566144 96901330553046064232119 := by
  unfold tailWord_566144
  simp only [CollatzResearch.WordTrace]
  refine ⟨10324484030482226271224743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13765978707309635028299657 10324484030482226271224743)
  ·
    refine ⟨15486726045723339406837115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10324484030482226271224743 15486726045723339406837115)
    ·
      refine ⟨23230089068585009110255673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15486726045723339406837115 23230089068585009110255673)
      ·
        refine ⟨17422566801438756832691755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23230089068585009110255673 17422566801438756832691755)
        ·
          refine ⟨26133850202158135249037633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17422566801438756832691755 26133850202158135249037633)
          ·
            refine ⟨19600387651618601436778225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26133850202158135249037633 19600387651618601436778225)
            ·
              refine ⟨14700290738713951077583669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19600387651618601436778225 14700290738713951077583669)
              ·
                refine ⟨1378152256754432913523469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14700290738713951077583669 1378152256754432913523469)
                ·
                  refine ⟨516807096282912342571301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1378152256754432913523469 516807096282912342571301)
                  ·
                    refine ⟨96901330553046064232119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516807096282912342571301 96901330553046064232119)
                    ·
                      rfl

theorem cell23_566144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 4].length) (baseStart_566144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566144 prefixEnd_566144 := by exact prefixLift 566144
  have htrace : WordTrace (prefixWord ++ tailWord_566144) baseStart_566144 baseEnd_566144 := by
    simpa [prefixWord, tailWord_566144, baseEnd_566144] using wordTrace_append hprefix tailTrace_566144
  have hstable : (prefixWord ++ tailWord_566144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566144).length < 2 ^ (prefixWord ++ tailWord_566144).sum := by decide
  have hdescent : baseEnd_566144 < baseStart_566144 := by decide
  rcases family_descends (prefixWord ++ tailWord_566144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566146 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_566146 : Nat := 118140960795 + 566146 * 2 ^ 59
def prefixEnd_566146 : Nat := 4983230072969 + 3 ^ 40 * 566146 * 2
def baseEnd_566146 : Nat := 290705018620447184871349

theorem tailTrace_566146 : CollatzResearch.WordTrace tailWord_566146 prefixEnd_566146 290705018620447184871349 := by
  unfold tailWord_566146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162260251739301721005573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13766027337971471256014861 5162260251739301721005573)
  ·
    refine ⟨967923797201119072688545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5162260251739301721005573 967923797201119072688545)
    ·
      refine ⟨725942847900839304516409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 967923797201119072688545 725942847900839304516409)
      ·
        refine ⟨544457135925629478387307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725942847900839304516409 544457135925629478387307)
        ·
          refine ⟨816685703888444217580961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544457135925629478387307 816685703888444217580961)
          ·
            refine ⟨612514277916333163185721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816685703888444217580961 612514277916333163185721)
            ·
              refine ⟨459385708437249872389291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612514277916333163185721 459385708437249872389291)
              ·
                refine ⟨689078562655874808583937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459385708437249872389291 689078562655874808583937)
                ·
                  refine ⟨516808921991906106437953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 689078562655874808583937 516808921991906106437953)
                  ·
                    refine ⟨387606691493929579828465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 516808921991906106437953 387606691493929579828465)
                    ·
                      refine ⟨290705018620447184871349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387606691493929579828465 290705018620447184871349)
                      ·
                        rfl

theorem cell23_566146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_566146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566146 prefixEnd_566146 := by exact prefixLift 566146
  have htrace : WordTrace (prefixWord ++ tailWord_566146) baseStart_566146 baseEnd_566146 := by
    simpa [prefixWord, tailWord_566146, baseEnd_566146] using wordTrace_append hprefix tailTrace_566146
  have hstable : (prefixWord ++ tailWord_566146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566146).length < 2 ^ (prefixWord ++ tailWord_566146).sum := by decide
  have hdescent : baseEnd_566146 < baseStart_566146 := by decide
  rcases family_descends (prefixWord ++ tailWord_566146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566228 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_566228 : Nat := 118140960795 + 566228 * 2 ^ 59
def prefixEnd_566228 : Nat := 4983230072969 + 3 ^ 40 * 566228 * 2
def baseEnd_566228 : Nat := 290747124034115864045971

theorem tailTrace_566228 : CollatzResearch.WordTrace tailWord_566228 prefixEnd_566228 290747124034115864045971 := by
  unfold tailWord_566228
  simp only [CollatzResearch.WordTrace]
  refine ⟨10326015896330067444253669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13768021195106756592338225 10326015896330067444253669)
  ·
    refine ⟨1936127980561887645797563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10326015896330067444253669 1936127980561887645797563)
    ·
      refine ⟨2904191970842831468696345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936127980561887645797563 2904191970842831468696345)
      ·
        refine ⟨2178143978132123601522259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2904191970842831468696345 2178143978132123601522259)
        ·
          refine ⟨3267215967198185402283389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178143978132123601522259 3267215967198185402283389)
          ·
            refine ⟨1225205987699319525856271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3267215967198185402283389 1225205987699319525856271)
            ·
              refine ⟨1837808981548979288784407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225205987699319525856271 1837808981548979288784407)
              ·
                refine ⟨2756713472323468933176611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837808981548979288784407 2756713472323468933176611)
                ·
                  refine ⟨4135070208485203399764917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756713472323468933176611 4135070208485203399764917)
                  ·
                    refine ⟨387662832045487818727961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4135070208485203399764917 387662832045487818727961)
                    ·
                      refine ⟨290747124034115864045971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387662832045487818727961 290747124034115864045971)
                      ·
                        rfl

theorem cell23_566228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_566228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566228 prefixEnd_566228 := by exact prefixLift 566228
  have htrace : WordTrace (prefixWord ++ tailWord_566228) baseStart_566228 baseEnd_566228 := by
    simpa [prefixWord, tailWord_566228, baseEnd_566228] using wordTrace_append hprefix tailTrace_566228
  have hstable : (prefixWord ++ tailWord_566228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566228).length < 2 ^ (prefixWord ++ tailWord_566228).sum := by decide
  have hdescent : baseEnd_566228 < baseStart_566228 := by decide
  rcases family_descends (prefixWord ++ tailWord_566228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566378 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_566378 : Nat := 118140960795 + 566378 * 2 ^ 59
def prefixEnd_566378 : Nat := 4983230072969 + 3 ^ 40 * 566378 * 2
def baseEnd_566378 : Nat := 290824146132290277170281

theorem tailTrace_566378 : CollatzResearch.WordTrace tailWord_566378 prefixEnd_566378 290824146132290277170281 := by
  unfold tailWord_566378
  simp only [CollatzResearch.WordTrace]
  refine ⟨5164375685529177626616947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13771668494744473670978525 5164375685529177626616947)
  ·
    refine ⟨7746563528293766439925421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5164375685529177626616947 7746563528293766439925421)
    ·
      refine ⟨2904961323110162414972033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7746563528293766439925421 2904961323110162414972033)
      ·
        refine ⟨2178720992332621811229025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2904961323110162414972033 2178720992332621811229025)
        ·
          refine ⟨1634040744249466358421769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2178720992332621811229025 1634040744249466358421769)
          ·
            refine ⟨1225530558187099768816327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1634040744249466358421769 1225530558187099768816327)
            ·
              refine ⟨1838295837280649653224491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225530558187099768816327 1838295837280649653224491)
              ·
                refine ⟨2757443755920974479836737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838295837280649653224491 2757443755920974479836737)
                ·
                  refine ⟨2068082816940730859877553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2757443755920974479836737 2068082816940730859877553)
                  ·
                    refine ⟨1551062112705548144908165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2068082816940730859877553 1551062112705548144908165)
                    ·
                      refine ⟨290824146132290277170281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1551062112705548144908165 290824146132290277170281)
                      ·
                        rfl

theorem cell23_566378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_566378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566378 prefixEnd_566378 := by exact prefixLift 566378
  have htrace : WordTrace (prefixWord ++ tailWord_566378) baseStart_566378 baseEnd_566378 := by
    simpa [prefixWord, tailWord_566378, baseEnd_566378] using wordTrace_append hprefix tailTrace_566378
  have hstable : (prefixWord ++ tailWord_566378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566378).length < 2 ^ (prefixWord ++ tailWord_566378).sum := by decide
  have hdescent : baseEnd_566378 < baseStart_566378 := by decide
  rcases family_descends (prefixWord ++ tailWord_566378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566382 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_566382 : Nat := 118140960795 + 566382 * 2 ^ 59
def prefixEnd_566382 : Nat := 4983230072969 + 3 ^ 40 * 566382 * 2
def baseEnd_566382 : Nat := 290826200054908261520263

theorem tailTrace_566382 : CollatzResearch.WordTrace tailWord_566382 prefixEnd_566382 290826200054908261520263 := by
  unfold tailWord_566382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582206079262777398701675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13771765756068146126408933 2582206079262777398701675)
  ·
    refine ⟨3873309118894166098052513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2582206079262777398701675 3873309118894166098052513)
    ·
      refine ⟨2904981839170624573539385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3873309118894166098052513 2904981839170624573539385)
      ·
        refine ⟨2178736379377968430154539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2904981839170624573539385 2178736379377968430154539)
        ·
          refine ⟨3268104569066952645231809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178736379377968430154539 3268104569066952645231809)
          ·
            refine ⟨2451078426800214483923857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3268104569066952645231809 2451078426800214483923857)
            ·
              refine ⟨1838308820100160862942893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2451078426800214483923857 1838308820100160862942893)
              ·
                refine ⟨689365807537560323603585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1838308820100160862942893 689365807537560323603585)
                ·
                  refine ⟨517024355653170242702689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 689365807537560323603585 517024355653170242702689)
                  ·
                    refine ⟨387768266739877682027017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 517024355653170242702689 387768266739877682027017)
                    ·
                      refine ⟨290826200054908261520263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387768266739877682027017 290826200054908261520263)
                      ·
                        rfl

theorem cell23_566382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_566382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566382 prefixEnd_566382 := by exact prefixLift 566382
  have htrace : WordTrace (prefixWord ++ tailWord_566382) baseStart_566382 baseEnd_566382 := by
    simpa [prefixWord, tailWord_566382, baseEnd_566382] using wordTrace_append hprefix tailTrace_566382
  have hstable : (prefixWord ++ tailWord_566382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566382).length < 2 ^ (prefixWord ++ tailWord_566382).sum := by decide
  have hdescent : baseEnd_566382 < baseStart_566382 := by decide
  rcases family_descends (prefixWord ++ tailWord_566382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566405 : List Nat := [1, 3, 1, 1, 6, 1, 2, 3, 5]
def baseStart_566405 : Nat := 118140960795 + 566405 * 2 ^ 59
def prefixEnd_566405 : Nat := 4983230072969 + 3 ^ 40 * 566405 * 2
def baseEnd_566405 : Nat := 32315334456662407948073

theorem tailTrace_566405 : CollatzResearch.WordTrace tailWord_566405 prefixEnd_566405 32315334456662407948073 := by
  unfold tailWord_566405
  simp only [CollatzResearch.WordTrace]
  refine ⟨20658487513018894117700669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13772325008679262745133779 20658487513018894117700669)
  ·
    refine ⟨7746932817382085294137751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20658487513018894117700669 7746932817382085294137751)
    ·
      refine ⟨11620399226073127941206627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7746932817382085294137751 11620399226073127941206627)
      ·
        refine ⟨17430598839109691911809941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11620399226073127941206627 17430598839109691911809941)
        ·
          refine ⟨817059320583266808366091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17430598839109691911809941 817059320583266808366091)
          ·
            refine ⟨1225588980874900212549137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817059320583266808366091 1225588980874900212549137)
            ·
              refine ⟨919191735656175159411853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225588980874900212549137 919191735656175159411853)
              ·
                refine ⟨344696900871065684779445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 919191735656175159411853 344696900871065684779445)
                ·
                  refine ⟨32315334456662407948073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 344696900871065684779445 32315334456662407948073)
                  ·
                    rfl

theorem cell23_566405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_566405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566405 prefixEnd_566405 := by exact prefixLift 566405
  have htrace : WordTrace (prefixWord ++ tailWord_566405) baseStart_566405 baseEnd_566405 := by
    simpa [prefixWord, tailWord_566405, baseEnd_566405] using wordTrace_append hprefix tailTrace_566405
  have hstable : (prefixWord ++ tailWord_566405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566405).length < 2 ^ (prefixWord ++ tailWord_566405).sum := by decide
  have hdescent : baseEnd_566405 < baseStart_566405 := by decide
  rcases family_descends (prefixWord ++ tailWord_566405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566458 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_566458 : Nat := 118140960795 + 566458 * 2 ^ 59
def prefixEnd_566458 : Nat := 4983230072969 + 3 ^ 40 * 566458 * 2
def baseEnd_566458 : Nat := 290865224584649964169913

theorem tailTrace_566458 : CollatzResearch.WordTrace tailWord_566458 prefixEnd_566458 290865224584649964169913 := by
  unfold tailWord_566458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165105145456721042345007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13773613721217922779586685 5165105145456721042345007)
  ·
    refine ⟨7747657718185081563517511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5165105145456721042345007 7747657718185081563517511)
    ·
      refine ⟨11621486577277622345276267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7747657718185081563517511 11621486577277622345276267)
      ·
        refine ⟨17432229865916433517914401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11621486577277622345276267 17432229865916433517914401)
        ·
          refine ⟨13074172399437325138435801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17432229865916433517914401 13074172399437325138435801)
          ·
            refine ⟨9805629299577993853826851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13074172399437325138435801 9805629299577993853826851)
            ·
              refine ⟨14708443949366990780740277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9805629299577993853826851 14708443949366990780740277)
              ·
                refine ⟨1378916620253155385694401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14708443949366990780740277 1378916620253155385694401)
                ·
                  refine ⟨1034187465189866539270801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1378916620253155385694401 1034187465189866539270801)
                  ·
                    refine ⟨775640598892399904453101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1034187465189866539270801 775640598892399904453101)
                    ·
                      refine ⟨290865224584649964169913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 775640598892399904453101 290865224584649964169913)
                      ·
                        rfl

theorem cell23_566458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_566458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566458 prefixEnd_566458 := by exact prefixLift 566458
  have htrace : WordTrace (prefixWord ++ tailWord_566458) baseStart_566458 baseEnd_566458 := by
    simpa [prefixWord, tailWord_566458, baseEnd_566458] using wordTrace_append hprefix tailTrace_566458
  have hstable : (prefixWord ++ tailWord_566458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566458).length < 2 ^ (prefixWord ++ tailWord_566458).sum := by decide
  have hdescent : baseEnd_566458 < baseStart_566458 := by decide
  rcases family_descends (prefixWord ++ tailWord_566458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566461 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 8]
def baseStart_566461 : Nat := 118140960795 + 566461 * 2 ^ 59
def prefixEnd_566461 : Nat := 4983230072969 + 3 ^ 40 * 566461 * 2
def baseEnd_566461 : Nat := 32318529447401494714711

theorem tailTrace_566461 : CollatzResearch.WordTrace tailWord_566461 prefixEnd_566461 32318529447401494714711 := by
  unfold tailWord_566461
  simp only [CollatzResearch.WordTrace]
  refine ⟨20660530000816015681739237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13773686667210677121159491 20660530000816015681739237)
  ·
    refine ⟨3873849375153002940326107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20660530000816015681739237 3873849375153002940326107)
    ·
      refine ⟨5810774062729504410489161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3873849375153002940326107 5810774062729504410489161)
      ·
        refine ⟨4358080547047128307866871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5810774062729504410489161 4358080547047128307866871)
        ·
          refine ⟨6537120820570692461800307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4358080547047128307866871 6537120820570692461800307)
          ·
            refine ⟨9805681230856038692700461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6537120820570692461800307 9805681230856038692700461)
            ·
              refine ⟨3677130461571014509762673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9805681230856038692700461 3677130461571014509762673)
              ·
                refine ⟨2757847846178260882322005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3677130461571014509762673 2757847846178260882322005)
                ·
                  refine ⟨32318529447401494714711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2757847846178260882322005 32318529447401494714711)
                  ·
                    rfl

theorem cell23_566461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_566461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566461 prefixEnd_566461 := by exact prefixLift 566461
  have htrace : WordTrace (prefixWord ++ tailWord_566461) baseStart_566461 baseEnd_566461 := by
    simpa [prefixWord, tailWord_566461, baseEnd_566461] using wordTrace_append hprefix tailTrace_566461
  have hstable : (prefixWord ++ tailWord_566461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566461).length < 2 ^ (prefixWord ++ tailWord_566461).sum := by decide
  have hdescent : baseEnd_566461 < baseStart_566461 := by decide
  rcases family_descends (prefixWord ++ tailWord_566461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566508 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_566508 : Nat := 118140960795 + 566508 * 2 ^ 59
def prefixEnd_566508 : Nat := 4983230072969 + 3 ^ 40 * 566508 * 2
def baseEnd_566508 : Nat := 96963632872458256181561

theorem tailTrace_566508 : CollatzResearch.WordTrace tailWord_566508 prefixEnd_566508 96963632872458256181561 := by
  unfold tailWord_566508
  simp only [CollatzResearch.WordTrace]
  refine ⟨10331122115822871354350089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13774829487763828472466785 10331122115822871354350089)
  ·
    refine ⟨7748341586867153515762567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10331122115822871354350089 7748341586867153515762567)
    ·
      refine ⟨11622512380300730273643851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7748341586867153515762567 11622512380300730273643851)
      ·
        refine ⟨17433768570451095410465777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11622512380300730273643851 17433768570451095410465777)
        ·
          refine ⟨13075326427838321557849333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17433768570451095410465777 13075326427838321557849333)
          ·
            refine ⟨1225811852609842646048375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13075326427838321557849333 1225811852609842646048375)
            ·
              refine ⟨1838717778914763969072563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225811852609842646048375 1838717778914763969072563)
              ·
                refine ⟨2758076668372145953608845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838717778914763969072563 2758076668372145953608845)
                ·
                  refine ⟨1034278750639554732603317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2758076668372145953608845 1034278750639554732603317)
                  ·
                    refine ⟨96963632872458256181561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1034278750639554732603317 96963632872458256181561)
                    ·
                      rfl

theorem cell23_566508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_566508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566508 prefixEnd_566508 := by exact prefixLift 566508
  have htrace : WordTrace (prefixWord ++ tailWord_566508) baseStart_566508 baseEnd_566508 := by
    simpa [prefixWord, tailWord_566508, baseEnd_566508] using wordTrace_append hprefix tailTrace_566508
  have hstable : (prefixWord ++ tailWord_566508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566508).length < 2 ^ (prefixWord ++ tailWord_566508).sum := by decide
  have hdescent : baseEnd_566508 < baseStart_566508 := by decide
  rcases family_descends (prefixWord ++ tailWord_566508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566515 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 2, 3, 2]
def baseStart_566515 : Nat := 118140960795 + 566515 * 2 ^ 59
def prefixEnd_566515 : Nat := 4983230072969 + 3 ^ 40 * 566515 * 2
def baseEnd_566515 : Nat := 290894492981956241157151

theorem tailTrace_566515 : CollatzResearch.WordTrace tailWord_566515 prefixEnd_566515 290894492981956241157151 := by
  unfold tailWord_566515
  simp only [CollatzResearch.WordTrace]
  refine ⟨20662499542620382904204999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13774999695080255269469999 20662499542620382904204999)
  ·
    refine ⟨30993749313930574356307499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20662499542620382904204999 30993749313930574356307499)
    ·
      refine ⟨46490623970895861534461249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30993749313930574356307499 46490623970895861534461249)
      ·
        refine ⟨34867967978171896150845937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46490623970895861534461249 34867967978171896150845937)
        ·
          refine ⟨26150975983628922113134453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34867967978171896150845937 26150975983628922113134453)
          ·
            refine ⟨2451653998465211448106355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26150975983628922113134453 2451653998465211448106355)
            ·
              refine ⟨3677480997697817172159533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451653998465211448106355 3677480997697817172159533)
              ·
                refine ⟨1379055374136681439559825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3677480997697817172159533 1379055374136681439559825)
                ·
                  refine ⟨1034291530602511079669869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379055374136681439559825 1034291530602511079669869)
                  ·
                    refine ⟨387859323975941654876201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1034291530602511079669869 387859323975941654876201)
                    ·
                      refine ⟨290894492981956241157151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387859323975941654876201 290894492981956241157151)
                      ·
                        rfl

theorem cell23_566515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 3, 2].length) (baseStart_566515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566515 prefixEnd_566515 := by exact prefixLift 566515
  have htrace : WordTrace (prefixWord ++ tailWord_566515) baseStart_566515 baseEnd_566515 := by
    simpa [prefixWord, tailWord_566515, baseEnd_566515] using wordTrace_append hprefix tailTrace_566515
  have hstable : (prefixWord ++ tailWord_566515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566515).length < 2 ^ (prefixWord ++ tailWord_566515).sum := by decide
  have hdescent : baseEnd_566515 < baseStart_566515 := by decide
  rcases family_descends (prefixWord ++ tailWord_566515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566522 : List Nat := [3, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3]
def baseStart_566522 : Nat := 118140960795 + 566522 * 2 ^ 59
def prefixEnd_566522 : Nat := 4983230072969 + 3 ^ 40 * 566522 * 2
def baseEnd_566522 : Nat := 290898087346537713769619

theorem tailTrace_566522 : CollatzResearch.WordTrace tailWord_566522 prefixEnd_566522 290898087346537713769619 := by
  unfold tailWord_566522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165688713398755774927455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13775169902396682066473213 5165688713398755774927455)
  ·
    refine ⟨7748533070098133662391183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5165688713398755774927455 7748533070098133662391183)
    ·
      refine ⟨11622799605147200493586775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7748533070098133662391183 11622799605147200493586775)
      ·
        refine ⟨17434199407720800740380163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11622799605147200493586775 17434199407720800740380163)
        ·
          refine ⟨26151299111581201110570245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17434199407720800740380163 26151299111581201110570245)
          ·
            refine ⟨4903368583421475208231921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26151299111581201110570245 4903368583421475208231921)
            ·
              refine ⟨3677526437566106406173941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4903368583421475208231921 3677526437566106406173941)
              ·
                refine ⟨344768103521822475578807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3677526437566106406173941 344768103521822475578807)
                ·
                  refine ⟨517152155282733713368211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344768103521822475578807 517152155282733713368211)
                  ·
                    refine ⟨775728232924100570052317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 517152155282733713368211 775728232924100570052317)
                    ·
                      refine ⟨290898087346537713769619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 775728232924100570052317 290898087346537713769619)
                      ·
                        rfl

theorem cell23_566522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3].length) (baseStart_566522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566522 prefixEnd_566522 := by exact prefixLift 566522
  have htrace : WordTrace (prefixWord ++ tailWord_566522) baseStart_566522 baseEnd_566522 := by
    simpa [prefixWord, tailWord_566522, baseEnd_566522] using wordTrace_append hprefix tailTrace_566522
  have hstable : (prefixWord ++ tailWord_566522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566522).length < 2 ^ (prefixWord ++ tailWord_566522).sum := by decide
  have hdescent : baseEnd_566522 < baseStart_566522 := by decide
  rcases family_descends (prefixWord ++ tailWord_566522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566532 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_566532 : Nat := 118140960795 + 566532 * 2 ^ 59
def prefixEnd_566532 : Nat := 4983230072969 + 3 ^ 40 * 566532 * 2
def baseEnd_566532 : Nat := 290903222153082674644573

theorem tailTrace_566532 : CollatzResearch.WordTrace tailWord_566532 prefixEnd_566532 290903222153082674644573 := by
  unfold tailWord_566532
  simp only [CollatzResearch.WordTrace]
  refine ⟨10331559791779397403786925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13775413055705863205049233 10331559791779397403786925)
  ·
    refine ⟨3874334921917274026420097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10331559791779397403786925 3874334921917274026420097)
    ·
      refine ⟨2905751191437955519815073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3874334921917274026420097 2905751191437955519815073)
      ·
        refine ⟨2179313393578466639861305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2905751191437955519815073 2179313393578466639861305)
        ·
          refine ⟨1634485045183849979895979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2179313393578466639861305 1634485045183849979895979)
          ·
            refine ⟨2451727567775774969843969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634485045183849979895979 2451727567775774969843969)
            ·
              refine ⟨1838795675831831227382977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2451727567775774969843969 1838795675831831227382977)
              ·
                refine ⟨1379096756873873420537233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1838795675831831227382977 1379096756873873420537233)
                ·
                  refine ⟨1034322567655405065402925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379096756873873420537233 1034322567655405065402925)
                  ·
                    refine ⟨387870962870776899526097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1034322567655405065402925 387870962870776899526097)
                    ·
                      refine ⟨290903222153082674644573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387870962870776899526097 290903222153082674644573)
                      ·
                        rfl

theorem cell23_566532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_566532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566532 prefixEnd_566532 := by exact prefixLift 566532
  have htrace : WordTrace (prefixWord ++ tailWord_566532) baseStart_566532 baseEnd_566532 := by
    simpa [prefixWord, tailWord_566532, baseEnd_566532] using wordTrace_append hprefix tailTrace_566532
  have hstable : (prefixWord ++ tailWord_566532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566532).length < 2 ^ (prefixWord ++ tailWord_566532).sum := by decide
  have hdescent : baseEnd_566532 < baseStart_566532 := by decide
  rcases family_descends (prefixWord ++ tailWord_566532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566539 : List Nat := [1, 1, 1, 1, 5, 3, 4, 2, 1, 1, 3]
def baseStart_566539 : Nat := 118140960795 + 566539 * 2 ^ 59
def prefixEnd_566539 : Nat := 4983230072969 + 3 ^ 40 * 566539 * 2
def baseEnd_566539 : Nat := 290906816517664147257041

theorem tailTrace_566539 : CollatzResearch.WordTrace tailWord_566539 prefixEnd_566539 290906816517664147257041 := by
  unfold tailWord_566539
  simp only [CollatzResearch.WordTrace]
  refine ⟨20663374894533435003078671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13775583263022290002052447 20663374894533435003078671)
  ·
    refine ⟨30995062341800152504618007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20663374894533435003078671 30995062341800152504618007)
    ·
      refine ⟨46492593512700228756927011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30995062341800152504618007 46492593512700228756927011)
      ·
        refine ⟨69738890269050343135390517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46492593512700228756927011 69738890269050343135390517)
        ·
          refine ⟨6538020962723469668942861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69738890269050343135390517 6538020962723469668942861)
          ·
            refine ⟨2451757861021301125853573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6538020962723469668942861 2451757861021301125853573)
            ·
              refine ⟨459704598941493961097545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2451757861021301125853573 459704598941493961097545)
              ·
                refine ⟨344778449206120470823159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459704598941493961097545 344778449206120470823159)
                ·
                  refine ⟨517167673809180706234739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344778449206120470823159 517167673809180706234739)
                  ·
                    refine ⟨775751510713771059352109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 517167673809180706234739 775751510713771059352109)
                    ·
                      refine ⟨290906816517664147257041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 775751510713771059352109 290906816517664147257041)
                      ·
                        rfl

theorem cell23_566539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 1, 1, 3].length) (baseStart_566539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566539 prefixEnd_566539 := by exact prefixLift 566539
  have htrace : WordTrace (prefixWord ++ tailWord_566539) baseStart_566539 baseEnd_566539 := by
    simpa [prefixWord, tailWord_566539, baseEnd_566539] using wordTrace_append hprefix tailTrace_566539
  have hstable : (prefixWord ++ tailWord_566539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566539).length < 2 ^ (prefixWord ++ tailWord_566539).sum := by decide
  have hdescent : baseEnd_566539 < baseStart_566539 := by decide
  rcases family_descends (prefixWord ++ tailWord_566539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566565 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_566565 : Nat := 118140960795 + 566565 * 2 ^ 59
def prefixEnd_566565 : Nat := 4983230072969 + 3 ^ 40 * 566565 * 2
def baseEnd_566565 : Nat := 290920167014681045531921

theorem tailTrace_566565 : CollatzResearch.WordTrace tailWord_566565 prefixEnd_566565 290920167014681045531921 := by
  unfold tailWord_566565
  simp only [CollatzResearch.WordTrace]
  refine ⟨20664323192439241443525149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13776215461626160962350099 20664323192439241443525149)
  ·
    refine ⟨7749121197164715541321931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20664323192439241443525149 7749121197164715541321931)
    ·
      refine ⟨11623681795747073311982897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7749121197164715541321931 11623681795747073311982897)
      ·
        refine ⟨8717761346810304983987173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11623681795747073311982897 8717761346810304983987173)
        ·
          refine ⟨1634580252526932184497595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8717761346810304983987173 1634580252526932184497595)
          ·
            refine ⟨2451870378790398276746393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634580252526932184497595 2451870378790398276746393)
            ·
              refine ⟨1838902784092798707559795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2451870378790398276746393 1838902784092798707559795)
              ·
                refine ⟨2758354176139198061339693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838902784092798707559795 2758354176139198061339693)
                ·
                  refine ⟨1034382816052199273002385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2758354176139198061339693 1034382816052199273002385)
                  ·
                    refine ⟨775787112039149454751789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1034382816052199273002385 775787112039149454751789)
                    ·
                      refine ⟨290920167014681045531921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 775787112039149454751789 290920167014681045531921)
                      ·
                        rfl

theorem cell23_566565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_566565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566565 prefixEnd_566565 := by exact prefixLift 566565
  have htrace : WordTrace (prefixWord ++ tailWord_566565) baseStart_566565 baseEnd_566565 := by
    simpa [prefixWord, tailWord_566565, baseEnd_566565] using wordTrace_append hprefix tailTrace_566565
  have hstable : (prefixWord ++ tailWord_566565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566565).length < 2 ^ (prefixWord ++ tailWord_566565).sum := by decide
  have hdescent : baseEnd_566565 < baseStart_566565 := by decide
  rcases family_descends (prefixWord ++ tailWord_566565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566571 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 6]
def baseStart_566571 : Nat := 118140960795 + 566571 * 2 ^ 59
def prefixEnd_566571 : Nat := 4983230072969 + 3 ^ 40 * 566571 * 2
def baseEnd_566571 : Nat := 290923247898608022056893

theorem tailTrace_566571 : CollatzResearch.WordTrace tailWord_566571 prefixEnd_566571 290923247898608022056893 := by
  unfold tailWord_566571
  simp only [CollatzResearch.WordTrace]
  refine ⟨20664542030417504468243567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13776361353611669645495711 20664542030417504468243567)
  ·
    refine ⟨30996813045626256702365351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20664542030417504468243567 30996813045626256702365351)
    ·
      refine ⟨46495219568439385053548027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30996813045626256702365351 46495219568439385053548027)
      ·
        refine ⟨69742829352659077580322041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46495219568439385053548027 69742829352659077580322041)
        ·
          refine ⟨52307122014494308185241531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69742829352659077580322041 52307122014494308185241531)
          ·
            refine ⟨78460683021741462277862297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52307122014494308185241531 78460683021741462277862297)
            ·
              refine ⟨58845512266306096708396723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78460683021741462277862297 58845512266306096708396723)
              ·
                refine ⟨88268268399459145062595085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58845512266306096708396723 88268268399459145062595085)
                ·
                  refine ⟨33100600649797179398473157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88268268399459145062595085 33100600649797179398473157)
                  ·
                    refine ⟨6206362621836971137213717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33100600649797179398473157 6206362621836971137213717)
                    ·
                      refine ⟨290923247898608022056893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6206362621836971137213717 290923247898608022056893)
                      ·
                        rfl

theorem cell23_566571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_566571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566571 prefixEnd_566571 := by exact prefixLift 566571
  have htrace : WordTrace (prefixWord ++ tailWord_566571) baseStart_566571 baseEnd_566571 := by
    simpa [prefixWord, tailWord_566571, baseEnd_566571] using wordTrace_append hprefix tailTrace_566571
  have hstable : (prefixWord ++ tailWord_566571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566571).length < 2 ^ (prefixWord ++ tailWord_566571).sum := by decide
  have hdescent : baseEnd_566571 < baseStart_566571 := by decide
  rcases family_descends (prefixWord ++ tailWord_566571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566579 : List Nat := [1, 1, 1, 2, 5, 2, 1, 5, 1, 2, 2]
def baseStart_566579 : Nat := 118140960795 + 566579 * 2 ^ 59
def prefixEnd_566579 : Nat := 4983230072969 + 3 ^ 40 * 566579 * 2
def baseEnd_566579 : Nat := 290927355743843990756857

theorem tailTrace_566579 : CollatzResearch.WordTrace tailWord_566579 prefixEnd_566579 290927355743843990756857 := by
  unfold tailWord_566579
  simp only [CollatzResearch.WordTrace]
  refine ⟨20664833814388521834534791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13776555876259014556356527 20664833814388521834534791)
  ·
    refine ⟨30997250721582782751802187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20664833814388521834534791 30997250721582782751802187)
    ·
      refine ⟨46495876082374174127703281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30997250721582782751802187 46495876082374174127703281)
      ·
        refine ⟨34871907061780630595777461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46495876082374174127703281 34871907061780630595777461)
        ·
          refine ⟨3269241287041934118354137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34871907061780630595777461 3269241287041934118354137)
          ·
            refine ⟨2451930965281450588765603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3269241287041934118354137 2451930965281450588765603)
            ·
              refine ⟨3677896447922175883148405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451930965281450588765603 3677896447922175883148405)
              ·
                refine ⟨344802791992703989045163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3677896447922175883148405 344802791992703989045163)
                ·
                  refine ⟨517204187989055983567745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344802791992703989045163 517204187989055983567745)
                  ·
                    refine ⟨387903140991791987675809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 517204187989055983567745 387903140991791987675809)
                    ·
                      refine ⟨290927355743843990756857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387903140991791987675809 290927355743843990756857)
                      ·
                        rfl

theorem cell23_566579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 1, 2, 2].length) (baseStart_566579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566579 prefixEnd_566579 := by exact prefixLift 566579
  have htrace : WordTrace (prefixWord ++ tailWord_566579) baseStart_566579 baseEnd_566579 := by
    simpa [prefixWord, tailWord_566579, baseEnd_566579] using wordTrace_append hprefix tailTrace_566579
  have hstable : (prefixWord ++ tailWord_566579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566579).length < 2 ^ (prefixWord ++ tailWord_566579).sum := by decide
  have hdescent : baseEnd_566579 < baseStart_566579 := by decide
  rcases family_descends (prefixWord ++ tailWord_566579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566596 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_566596 : Nat := 118140960795 + 566596 * 2 ^ 59
def prefixEnd_566596 : Nat := 4983230072969 + 3 ^ 40 * 566596 * 2
def baseEnd_566596 : Nat := 290936084914970424244279

theorem tailTrace_566596 : CollatzResearch.WordTrace tailWord_566596 prefixEnd_566596 290936084914970424244279 := by
  unfold tailWord_566596
  simp only [CollatzResearch.WordTrace]
  refine ⟨10332726927663466868951821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13776969236884622491935761 10332726927663466868951821)
  ·
    refine ⟨3874772597873800075856933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10332726927663466868951821 3874772597873800075856933)
    ·
      refine ⟨726519862101337514223175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3874772597873800075856933 726519862101337514223175)
      ·
        refine ⟨1089779793152006271334763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726519862101337514223175 1089779793152006271334763)
        ·
          refine ⟨1634669689728009407002145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089779793152006271334763 1634669689728009407002145)
          ·
            refine ⟨1226002267296007055251609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1634669689728009407002145 1226002267296007055251609)
            ·
              refine ⟨919501700472005291438707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1226002267296007055251609 919501700472005291438707)
              ·
                refine ⟨1379252550708007937158061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919501700472005291438707 1379252550708007937158061)
                ·
                  refine ⟨517219706515502976434273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1379252550708007937158061 517219706515502976434273)
                  ·
                    refine ⟨387914779886627232325705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 517219706515502976434273 387914779886627232325705)
                    ·
                      refine ⟨290936084914970424244279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387914779886627232325705 290936084914970424244279)
                      ·
                        rfl

theorem cell23_566596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_566596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566596 prefixEnd_566596 := by exact prefixLift 566596
  have htrace : WordTrace (prefixWord ++ tailWord_566596) baseStart_566596 baseEnd_566596 := by
    simpa [prefixWord, tailWord_566596, baseEnd_566596] using wordTrace_append hprefix tailTrace_566596
  have hstable : (prefixWord ++ tailWord_566596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566596).length < 2 ^ (prefixWord ++ tailWord_566596).sum := by decide
  have hdescent : baseEnd_566596 < baseStart_566596 := by decide
  rcases family_descends (prefixWord ++ tailWord_566596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566618 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_566618 : Nat := 118140960795 + 566618 * 2 ^ 59
def prefixEnd_566618 : Nat := 4983230072969 + 3 ^ 40 * 566618 * 2
def baseEnd_566618 : Nat := 290947381489369338169177

theorem tailTrace_566618 : CollatzResearch.WordTrace tailWord_566618 prefixEnd_566618 290947381489369338169177 := by
  unfold tailWord_566618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5166564065311807873801127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13777504174164820996803005 5166564065311807873801127)
  ·
    refine ⟨7749846097967711810701691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5166564065311807873801127 7749846097967711810701691)
    ·
      refine ⟨11624769146951567716052537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7749846097967711810701691 11624769146951567716052537)
      ·
        refine ⟨8718576860213675787039403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11624769146951567716052537 8718576860213675787039403)
        ·
          refine ⟨13077865290320513680559105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8718576860213675787039403 13077865290320513680559105)
          ·
            refine ⟨9808398967740385260419329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13077865290320513680559105 9808398967740385260419329)
            ·
              refine ⟨7356299225805288945314497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9808398967740385260419329 7356299225805288945314497)
              ·
                refine ⟨5517224419353966708985873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7356299225805288945314497 5517224419353966708985873)
                ·
                  refine ⟨4137918314515475031739405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5517224419353966708985873 4137918314515475031739405)
                  ·
                    refine ⟨1551719367943303136902277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4137918314515475031739405 1551719367943303136902277)
                    ·
                      refine ⟨290947381489369338169177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1551719367943303136902277 290947381489369338169177)
                      ·
                        rfl

theorem cell23_566618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_566618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566618 prefixEnd_566618 := by exact prefixLift 566618
  have htrace : WordTrace (prefixWord ++ tailWord_566618) baseStart_566618 baseEnd_566618 := by
    simpa [prefixWord, tailWord_566618, baseEnd_566618] using wordTrace_append hprefix tailTrace_566618
  have hstable : (prefixWord ++ tailWord_566618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566618).length < 2 ^ (prefixWord ++ tailWord_566618).sum := by decide
  have hdescent : baseEnd_566618 < baseStart_566618 := by decide
  rcases family_descends (prefixWord ++ tailWord_566618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566652 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_566652 : Nat := 118140960795 + 566652 * 2 ^ 59
def prefixEnd_566652 : Nat := 4983230072969 + 3 ^ 40 * 566652 * 2
def baseEnd_566652 : Nat := 290964839831622205144021

theorem tailTrace_566652 : CollatzResearch.WordTrace tailWord_566652 prefixEnd_566652 290964839831622205144021 := by
  unfold tailWord_566652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10333748171562027650971105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13778330895416036867961473 10333748171562027650971105)
  ·
    refine ⟨7750311128671520738228329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10333748171562027650971105 7750311128671520738228329)
    ·
      refine ⟨5812733346503640553671247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7750311128671520738228329 5812733346503640553671247)
      ·
        refine ⟨8719100019755460830506871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5812733346503640553671247 8719100019755460830506871)
        ·
          refine ⟨13078650029633191245760307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8719100019755460830506871 13078650029633191245760307)
          ·
            refine ⟨19617975044449786868640461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13078650029633191245760307 19617975044449786868640461)
            ·
              refine ⟨7356740641668670075740173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19617975044449786868640461 7356740641668670075740173)
              ·
                refine ⟨2758777740625751278402565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7356740641668670075740173 2758777740625751278402565)
                ·
                  refine ⟨517270826367328364700481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2758777740625751278402565 517270826367328364700481)
                  ·
                    refine ⟨387953119775496273525361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 517270826367328364700481 387953119775496273525361)
                    ·
                      refine ⟨290964839831622205144021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387953119775496273525361 290964839831622205144021)
                      ·
                        rfl

theorem cell23_566652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_566652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566652 prefixEnd_566652 := by exact prefixLift 566652
  have htrace : WordTrace (prefixWord ++ tailWord_566652) baseStart_566652 baseEnd_566652 := by
    simpa [prefixWord, tailWord_566652, baseEnd_566652] using wordTrace_append hprefix tailTrace_566652
  have hstable : (prefixWord ++ tailWord_566652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566652).length < 2 ^ (prefixWord ++ tailWord_566652).sum := by decide
  have hdescent : baseEnd_566652 < baseStart_566652 := by decide
  rcases family_descends (prefixWord ++ tailWord_566652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566686 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_566686 : Nat := 118140960795 + 566686 * 2 ^ 59
def prefixEnd_566686 : Nat := 4983230072969 + 3 ^ 40 * 566686 * 2
def baseEnd_566686 : Nat := 290982298173875072118865

theorem tailTrace_566686 : CollatzResearch.WordTrace tailWord_566686 prefixEnd_566686 290982298173875072118865 := by
  unfold tailWord_566686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2583592053125109888584989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13779157616667252739119941 2583592053125109888584989)
  ·
    refine ⟨968847019921916208219371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2583592053125109888584989 968847019921916208219371)
    ·
      refine ⟨1453270529882874312329057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968847019921916208219371 1453270529882874312329057)
      ·
        refine ⟨1089952897412155734246793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1453270529882874312329057 1089952897412155734246793)
        ·
          refine ⟨817464673059116800685095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1089952897412155734246793 817464673059116800685095)
          ·
            refine ⟨1226197009588675201027643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817464673059116800685095 1226197009588675201027643)
            ·
              refine ⟨1839295514383012801541465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226197009588675201027643 1839295514383012801541465)
              ·
                refine ⟨1379471635787259601156099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839295514383012801541465 1379471635787259601156099)
                ·
                  refine ⟨2069207453680889401734149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379471635787259601156099 2069207453680889401734149)
                  ·
                    refine ⟨387976397565166762825153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2069207453680889401734149 387976397565166762825153)
                    ·
                      refine ⟨290982298173875072118865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 387976397565166762825153 290982298173875072118865)
                      ·
                        rfl

theorem cell23_566686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_566686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566686 prefixEnd_566686 := by exact prefixLift 566686
  have htrace : WordTrace (prefixWord ++ tailWord_566686) baseStart_566686 baseEnd_566686 := by
    simpa [prefixWord, tailWord_566686, baseEnd_566686] using wordTrace_append hprefix tailTrace_566686
  have hstable : (prefixWord ++ tailWord_566686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566686).length < 2 ^ (prefixWord ++ tailWord_566686).sum := by decide
  have hdescent : baseEnd_566686 < baseStart_566686 := by decide
  rcases family_descends (prefixWord ++ tailWord_566686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566705 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 2, 5]
def baseStart_566705 : Nat := 118140960795 + 566705 * 2 ^ 59
def prefixEnd_566705 : Nat := 4983230072969 + 3 ^ 40 * 566705 * 2
def baseEnd_566705 : Nat := 96997351435436832593759

theorem tailTrace_566705 : CollatzResearch.WordTrace tailWord_566705 prefixEnd_566705 96997351435436832593759 := by
  unfold tailWord_566705
  simp only [CollatzResearch.WordTrace]
  refine ⟨20669429411932045353621569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13779619607954696902414379 20669429411932045353621569)
  ·
    refine ⟨15502072058949034015216177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20669429411932045353621569 15502072058949034015216177)
    ·
      refine ⟨11626554044211775511412133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15502072058949034015216177 11626554044211775511412133)
      ·
        refine ⟨2179978883289707908389775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11626554044211775511412133 2179978883289707908389775)
        ·
          refine ⟨3269968324934561862584663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179978883289707908389775 3269968324934561862584663)
          ·
            refine ⟨4904952487401842793876995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269968324934561862584663 4904952487401842793876995)
            ·
              refine ⟨7357428731102764190815493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904952487401842793876995 7357428731102764190815493)
              ·
                refine ⟨1379517887081768285777905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7357428731102764190815493 1379517887081768285777905)
                ·
                  refine ⟨1034638415311326214333429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1379517887081768285777905 1034638415311326214333429)
                  ·
                    refine ⟨96997351435436832593759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1034638415311326214333429 96997351435436832593759)
                    ·
                      rfl

theorem cell23_566705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_566705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566705 prefixEnd_566705 := by exact prefixLift 566705
  have htrace : WordTrace (prefixWord ++ tailWord_566705) baseStart_566705 baseEnd_566705 := by
    simpa [prefixWord, tailWord_566705, baseEnd_566705] using wordTrace_append hprefix tailTrace_566705
  have hstable : (prefixWord ++ tailWord_566705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566705).length < 2 ^ (prefixWord ++ tailWord_566705).sum := by decide
  have hdescent : baseEnd_566705 < baseStart_566705 := by decide
  rcases family_descends (prefixWord ++ tailWord_566705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566709 : List Nat := [1, 3, 3, 2, 2, 1, 4, 2, 5]
def baseStart_566709 : Nat := 118140960795 + 566709 * 2 ^ 59
def prefixEnd_566709 : Nat := 4983230072969 + 3 ^ 40 * 566709 * 2
def baseEnd_566709 : Nat := 32332678692103164681251

theorem tailTrace_566709 : CollatzResearch.WordTrace tailWord_566709 prefixEnd_566709 32332678692103164681251 := by
  unfold tailWord_566709
  simp only [CollatzResearch.WordTrace]
  refine ⟨20669575303917554036767181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13779716869278369357844787 20669575303917554036767181)
  ·
    refine ⟨7751090738969082763787693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20669575303917554036767181 7751090738969082763787693)
    ·
      refine ⟨2906659027113406036420385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7751090738969082763787693 2906659027113406036420385)
      ·
        refine ⟨2179994270335054527315289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2906659027113406036420385 2179994270335054527315289)
        ·
          refine ⟨1634995702751290895486467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2179994270335054527315289 1634995702751290895486467)
          ·
            refine ⟨2452493554126936343229701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634995702751290895486467 2452493554126936343229701)
            ·
              refine ⟨459842541398800564355569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2452493554126936343229701 459842541398800564355569)
              ·
                refine ⟨344881906049100423266677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459842541398800564355569 344881906049100423266677)
                ·
                  refine ⟨32332678692103164681251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 344881906049100423266677 32332678692103164681251)
                  ·
                    rfl

theorem cell23_566709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_566709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566709 prefixEnd_566709 := by exact prefixLift 566709
  have htrace : WordTrace (prefixWord ++ tailWord_566709) baseStart_566709 baseEnd_566709 := by
    simpa [prefixWord, tailWord_566709, baseEnd_566709] using wordTrace_append hprefix tailTrace_566709
  have hstable : (prefixWord ++ tailWord_566709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566709).length < 2 ^ (prefixWord ++ tailWord_566709).sum := by decide
  have hdescent : baseEnd_566709 < baseStart_566709 := by decide
  rcases family_descends (prefixWord ++ tailWord_566709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566735 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 5, 4]
def baseStart_566735 : Nat := 118140960795 + 566735 * 2 ^ 59
def prefixEnd_566735 : Nat := 4983230072969 + 3 ^ 40 * 566735 * 2
def baseEnd_566735 : Nat := 97002486241981793468713

theorem tailTrace_566735 : CollatzResearch.WordTrace tailWord_566735 prefixEnd_566735 97002486241981793468713 := by
  unfold tailWord_566735
  simp only [CollatzResearch.WordTrace]
  refine ⟨20670523601823360477213659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13780349067882240318142439 20670523601823360477213659)
  ·
    refine ⟨31005785402735040715820489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20670523601823360477213659 31005785402735040715820489)
    ·
      refine ⟨23254339052051280536865367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31005785402735040715820489 23254339052051280536865367)
      ·
        refine ⟨34881508578076920805298051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23254339052051280536865367 34881508578076920805298051)
        ·
          refine ⟨52322262867115381207947077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34881508578076920805298051 52322262867115381207947077)
          ·
            refine ⟨9810424287584133976490077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52322262867115381207947077 9810424287584133976490077)
            ·
              refine ⟨3678909107844050241183779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9810424287584133976490077 3678909107844050241183779)
              ·
                refine ⟨5518363661766075361775669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3678909107844050241183779 5518363661766075361775669)
                ·
                  refine ⟨517346593290569565166469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5518363661766075361775669 517346593290569565166469)
                  ·
                    refine ⟨97002486241981793468713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 517346593290569565166469 97002486241981793468713)
                    ·
                      rfl

theorem cell23_566735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 4].length) (baseStart_566735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566735 prefixEnd_566735 := by exact prefixLift 566735
  have htrace : WordTrace (prefixWord ++ tailWord_566735) baseStart_566735 baseEnd_566735 := by
    simpa [prefixWord, tailWord_566735, baseEnd_566735] using wordTrace_append hprefix tailTrace_566735
  have hstable : (prefixWord ++ tailWord_566735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566735).length < 2 ^ (prefixWord ++ tailWord_566735).sum := by decide
  have hdescent : baseEnd_566735 < baseStart_566735 := by decide
  rcases family_descends (prefixWord ++ tailWord_566735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566755 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 6]
def baseStart_566755 : Nat := 118140960795 + 566755 * 2 ^ 59
def prefixEnd_566755 : Nat := 4983230072969 + 3 ^ 40 * 566755 * 2
def baseEnd_566755 : Nat := 291017728339035302156047

theorem tailTrace_566755 : CollatzResearch.WordTrace tailWord_566755 prefixEnd_566755 291017728339035302156047 := by
  unfold tailWord_566755
  simp only [CollatzResearch.WordTrace]
  refine ⟨20671253061750903892941719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13780835374500602595294479 20671253061750903892941719)
  ·
    refine ⟨31006879592626355839412579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20671253061750903892941719 31006879592626355839412579)
    ·
      refine ⟨46510319388939533759118869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31006879592626355839412579 46510319388939533759118869)
      ·
        refine ⟨2180171221356540644958697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46510319388939533759118869 2180171221356540644958697)
        ·
          refine ⟨1635128416017405483719023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2180171221356540644958697 1635128416017405483719023)
          ·
            refine ⟨2452692624026108225578535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635128416017405483719023 2452692624026108225578535)
            ·
              refine ⟨3679038936039162338367803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452692624026108225578535 3679038936039162338367803)
              ·
                refine ⟨5518558404058743507551705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679038936039162338367803 5518558404058743507551705)
                ·
                  refine ⟨4138918803044057630663779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5518558404058743507551705 4138918803044057630663779)
                  ·
                    refine ⟨6208378204566086445995669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4138918803044057630663779 6208378204566086445995669)
                    ·
                      refine ⟨291017728339035302156047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6208378204566086445995669 291017728339035302156047)
                      ·
                        rfl

theorem cell23_566755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_566755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566755 prefixEnd_566755 := by exact prefixLift 566755
  have htrace : WordTrace (prefixWord ++ tailWord_566755) baseStart_566755 baseEnd_566755 := by
    simpa [prefixWord, tailWord_566755, baseEnd_566755] using wordTrace_append hprefix tailTrace_566755
  have hstable : (prefixWord ++ tailWord_566755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566755).length < 2 ^ (prefixWord ++ tailWord_566755).sum := by decide
  have hdescent : baseEnd_566755 < baseStart_566755 := by decide
  rcases family_descends (prefixWord ++ tailWord_566755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566769 : List Nat := [1, 2, 2, 2, 3, 2, 2, 4, 1, 4]
def baseStart_566769 : Nat := 118140960795 + 566769 * 2 ^ 59
def prefixEnd_566769 : Nat := 4983230072969 + 3 ^ 40 * 566769 * 2
def baseEnd_566769 : Nat := 97008305689399415793661

theorem tailTrace_566769 : CollatzResearch.WordTrace tailWord_566769 prefixEnd_566769 97008305689399415793661 := by
  unfold tailWord_566769
  simp only [CollatzResearch.WordTrace]
  refine ⟨20671763683700184283951361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13781175789133456189300907 20671763683700184283951361)
  ·
    refine ⟨15503822762775138212963521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20671763683700184283951361 15503822762775138212963521)
    ·
      refine ⟨11627867072081353659722641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15503822762775138212963521 11627867072081353659722641)
      ·
        refine ⟨8720900304061015244791981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11627867072081353659722641 8720900304061015244791981)
        ·
          refine ⟨3270337614022880716796993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8720900304061015244791981 3270337614022880716796993)
          ·
            refine ⟨2452753210517160537597745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270337614022880716796993 2452753210517160537597745)
            ·
              refine ⟨1839564907887870403198309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452753210517160537597745 1839564907887870403198309)
              ·
                refine ⟨344918420228975700599683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1839564907887870403198309 344918420228975700599683)
                ·
                  refine ⟨517377630343463550899525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344918420228975700599683 517377630343463550899525)
                  ·
                    refine ⟨97008305689399415793661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 517377630343463550899525 97008305689399415793661)
                    ·
                      rfl

theorem cell23_566769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_566769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566769 prefixEnd_566769 := by exact prefixLift 566769
  have htrace : WordTrace (prefixWord ++ tailWord_566769) baseStart_566769 baseEnd_566769 := by
    simpa [prefixWord, tailWord_566769, baseEnd_566769] using wordTrace_append hprefix tailTrace_566769
  have hstable : (prefixWord ++ tailWord_566769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566769).length < 2 ^ (prefixWord ++ tailWord_566769).sum := by decide
  have hdescent : baseEnd_566769 < baseStart_566769 := by decide
  rcases family_descends (prefixWord ++ tailWord_566769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566812 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_566812 : Nat := 118140960795 + 566812 * 2 ^ 59
def prefixEnd_566812 : Nat := 4983230072969 + 3 ^ 40 * 566812 * 2
def baseEnd_566812 : Nat := 97015665578780526381095

theorem tailTrace_566812 : CollatzResearch.WordTrace tailWord_566812 prefixEnd_566812 97015665578780526381095 := by
  unfold tailWord_566812
  simp only [CollatzResearch.WordTrace]
  refine ⟨10336666011272201313883345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13782221348362935085177793 10336666011272201313883345)
  ·
    refine ⟨7752499508454150985412509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10336666011272201313883345 7752499508454150985412509)
    ·
      refine ⟨2907187315670306619529691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7752499508454150985412509 2907187315670306619529691)
      ·
        refine ⟨4360780973505459929294537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907187315670306619529691 4360780973505459929294537)
        ·
          refine ⟨3270585730129094946970903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4360780973505459929294537 3270585730129094946970903)
          ·
            refine ⟨4905878595193642420456355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270585730129094946970903 4905878595193642420456355)
            ·
              refine ⟨7358817892790463630684533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4905878595193642420456355 7358817892790463630684533)
              ·
                refine ⟨689889177449105965376675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7358817892790463630684533 689889177449105965376675)
                ·
                  refine ⟨1034833766173658948065013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689889177449105965376675 1034833766173658948065013)
                  ·
                    refine ⟨97015665578780526381095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1034833766173658948065013 97015665578780526381095)
                    ·
                      rfl

theorem cell23_566812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_566812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566812 prefixEnd_566812 := by exact prefixLift 566812
  have htrace : WordTrace (prefixWord ++ tailWord_566812) baseStart_566812 baseEnd_566812 := by
    simpa [prefixWord, tailWord_566812, baseEnd_566812] using wordTrace_append hprefix tailTrace_566812
  have hstable : (prefixWord ++ tailWord_566812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566812).length < 2 ^ (prefixWord ++ tailWord_566812).sum := by decide
  have hdescent : baseEnd_566812 < baseStart_566812 := by decide
  rcases family_descends (prefixWord ++ tailWord_566812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566866 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_566866 : Nat := 118140960795 + 566866 * 2 ^ 59
def prefixEnd_566866 : Nat := 4983230072969 + 3 ^ 40 * 566866 * 2
def baseEnd_566866 : Nat := 291074724691684367868037

theorem tailTrace_566866 : CollatzResearch.WordTrace tailWord_566866 prefixEnd_566866 291074724691684367868037 := by
  unfold tailWord_566866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168825391087192462558113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13783534376232513233488301 5168825391087192462558113)
  ·
    refine ⟨3876619043315394346918585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5168825391087192462558113 3876619043315394346918585)
    ·
      refine ⟨2907464282486545760188939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3876619043315394346918585 2907464282486545760188939)
      ·
        refine ⟨4361196423729818640283409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907464282486545760188939 4361196423729818640283409)
        ·
          refine ⟨3270897317797363980212557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4361196423729818640283409 3270897317797363980212557)
          ·
            refine ⟨1226586494174011492579709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3270897317797363980212557 1226586494174011492579709)
            ·
              refine ⟨459969935315254309717391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1226586494174011492579709 459969935315254309717391)
              ·
                refine ⟨689954902972881464576087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459969935315254309717391 689954902972881464576087)
                ·
                  refine ⟨1034932354459322196864131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689954902972881464576087 1034932354459322196864131)
                  ·
                    refine ⟨1552398531688983295296197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1034932354459322196864131 1552398531688983295296197)
                    ·
                      refine ⟨291074724691684367868037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1552398531688983295296197 291074724691684367868037)
                      ·
                        rfl

theorem cell23_566866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_566866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566866 prefixEnd_566866 := by exact prefixLift 566866
  have htrace : WordTrace (prefixWord ++ tailWord_566866) baseStart_566866 baseEnd_566866 := by
    simpa [prefixWord, tailWord_566866, baseEnd_566866] using wordTrace_append hprefix tailTrace_566866
  have hstable : (prefixWord ++ tailWord_566866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566866).length < 2 ^ (prefixWord ++ tailWord_566866).sum := by decide
  have hdescent : baseEnd_566866 < baseStart_566866 := by decide
  rcases family_descends (prefixWord ++ tailWord_566866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566876 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_566876 : Nat := 118140960795 + 566876 * 2 ^ 59
def prefixEnd_566876 : Nat := 4983230072969 + 3 ^ 40 * 566876 * 2
def baseEnd_566876 : Nat := 97026619832743109580997

theorem tailTrace_566876 : CollatzResearch.WordTrace tailWord_566876 prefixEnd_566876 97026619832743109580997 := by
  unfold tailWord_566876
  simp only [CollatzResearch.WordTrace]
  refine ⟨10337833147156270779048241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13783777529541694372064321 10337833147156270779048241)
  ·
    refine ⟨7753374860367203084286181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10337833147156270779048241 7753374860367203084286181)
    ·
      refine ⟨1453757786318850578303659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7753374860367203084286181 1453757786318850578303659)
      ·
        refine ⟨2180636679478275867455489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1453757786318850578303659 2180636679478275867455489)
        ·
          refine ⟨1635477509608706900591617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2180636679478275867455489 1635477509608706900591617)
          ·
            refine ⟨1226608132206530175443713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1635477509608706900591617 1226608132206530175443713)
            ·
              refine ⟨919956099154897631582785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1226608132206530175443713 919956099154897631582785)
              ·
                refine ⟨689967074366173223687089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 919956099154897631582785 689967074366173223687089)
                ·
                  refine ⟨517475305774629917765317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 689967074366173223687089 517475305774629917765317)
                  ·
                    refine ⟨97026619832743109580997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 517475305774629917765317 97026619832743109580997)
                    ·
                      rfl

theorem cell23_566876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_566876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566876 prefixEnd_566876 := by exact prefixLift 566876
  have htrace : WordTrace (prefixWord ++ tailWord_566876) baseStart_566876 baseEnd_566876 := by
    simpa [prefixWord, tailWord_566876, baseEnd_566876] using wordTrace_append hprefix tailTrace_566876
  have hstable : (prefixWord ++ tailWord_566876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566876).length < 2 ^ (prefixWord ++ tailWord_566876).sum := by decide
  have hdescent : baseEnd_566876 < baseStart_566876 := by decide
  rcases family_descends (prefixWord ++ tailWord_566876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566883 : List Nat := [1, 1, 1, 5, 1, 4, 1, 4, 1, 2, 2]
def baseStart_566883 : Nat := 118140960795 + 566883 * 2 ^ 59
def prefixEnd_566883 : Nat := 4983230072969 + 3 ^ 40 * 566883 * 2
def baseEnd_566883 : Nat := 291083453862810801355459

theorem tailTrace_566883 : CollatzResearch.WordTrace tailWord_566883 prefixEnd_566883 291083453862810801355459 := by
  unfold tailWord_566883
  simp only [CollatzResearch.WordTrace]
  refine ⟨20675921605287181753601303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13783947736858121169067535 20675921605287181753601303)
  ·
    refine ⟨31013882407930772630401955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20675921605287181753601303 31013882407930772630401955)
    ·
      refine ⟨46520823611896158945602933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31013882407930772630401955 46520823611896158945602933)
      ·
        refine ⟨4361327213615264901150275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46520823611896158945602933 4361327213615264901150275)
        ·
          refine ⟨6541990820422897351725413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4361327213615264901150275 6541990820422897351725413)
          ·
            refine ⟨1226623278829293253448515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6541990820422897351725413 1226623278829293253448515)
            ·
              refine ⟨1839934918243939880172773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226623278829293253448515 1839934918243939880172773)
              ·
                refine ⟨344987797170738727532395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1839934918243939880172773 344987797170738727532395)
                ·
                  refine ⟨517481695756108091298593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344987797170738727532395 517481695756108091298593)
                  ·
                    refine ⟨388111271817081068473945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 517481695756108091298593 388111271817081068473945)
                    ·
                      refine ⟨291083453862810801355459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388111271817081068473945 291083453862810801355459)
                      ·
                        rfl

theorem cell23_566883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_566883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566883 prefixEnd_566883 := by exact prefixLift 566883
  have htrace : WordTrace (prefixWord ++ tailWord_566883) baseStart_566883 baseEnd_566883 := by
    simpa [prefixWord, tailWord_566883, baseEnd_566883] using wordTrace_append hprefix tailTrace_566883
  have hstable : (prefixWord ++ tailWord_566883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566883).length < 2 ^ (prefixWord ++ tailWord_566883).sum := by decide
  have hdescent : baseEnd_566883 < baseStart_566883 := by decide
  rcases family_descends (prefixWord ++ tailWord_566883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566895 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_566895 : Nat := 118140960795 + 566895 * 2 ^ 59
def prefixEnd_566895 : Nat := 4983230072969 + 3 ^ 40 * 566895 * 2
def baseEnd_566895 : Nat := 291089615630664754405403

theorem tailTrace_566895 : CollatzResearch.WordTrace tailWord_566895 prefixEnd_566895 291089615630664754405403 := by
  unfold tailWord_566895
  simp only [CollatzResearch.WordTrace]
  refine ⟨20676359281243707803038139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13784239520829138535358759 20676359281243707803038139)
  ·
    refine ⟨31014538921865561704557209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20676359281243707803038139 31014538921865561704557209)
    ·
      refine ⟨23260904191399171278417907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31014538921865561704557209 23260904191399171278417907)
      ·
        refine ⟨34891356287098756917626861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23260904191399171278417907 34891356287098756917626861)
        ·
          refine ⟨13084258607662033844110073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34891356287098756917626861 13084258607662033844110073)
          ·
            refine ⟨9813193955746525383082555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13084258607662033844110073 9813193955746525383082555)
            ·
              refine ⟨14719790933619788074623833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9813193955746525383082555 14719790933619788074623833)
              ·
                refine ⟨11039843200214841055967875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14719790933619788074623833 11039843200214841055967875)
                ·
                  refine ⟨16559764800322261583951813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11039843200214841055967875 16559764800322261583951813)
                  ·
                    refine ⟨3104955900060424046990965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16559764800322261583951813 3104955900060424046990965)
                    ·
                      refine ⟨291089615630664754405403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3104955900060424046990965 291089615630664754405403)
                      ·
                        rfl

theorem cell23_566895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_566895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566895 prefixEnd_566895 := by exact prefixLift 566895
  have htrace : WordTrace (prefixWord ++ tailWord_566895) baseStart_566895 baseEnd_566895 := by
    simpa [prefixWord, tailWord_566895, baseEnd_566895] using wordTrace_append hprefix tailTrace_566895
  have hstable : (prefixWord ++ tailWord_566895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566895).length < 2 ^ (prefixWord ++ tailWord_566895).sum := by decide
  have hdescent : baseEnd_566895 < baseStart_566895 := by decide
  rcases family_descends (prefixWord ++ tailWord_566895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566915 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 3, 8]
def baseStart_566915 : Nat := 118140960795 + 566915 * 2 ^ 59
def prefixEnd_566915 : Nat := 4983230072969 + 3 ^ 40 * 566915 * 2
def baseEnd_566915 : Nat := 97033295081251558718437

theorem tailTrace_566915 : CollatzResearch.WordTrace tailWord_566915 prefixEnd_566915 97033295081251558718437 := by
  unfold tailWord_566915
  simp only [CollatzResearch.WordTrace]
  refine ⟨20677088741171251218766199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13784725827447500812510799 20677088741171251218766199)
  ·
    refine ⟨31015633111756876828149299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20677088741171251218766199 31015633111756876828149299)
    ·
      refine ⟨46523449667635315242223949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31015633111756876828149299 46523449667635315242223949)
      ·
        refine ⟨17446293625363243215833981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46523449667635315242223949 17446293625363243215833981)
        ·
          refine ⟨6542360109511216205937743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17446293625363243215833981 6542360109511216205937743)
          ·
            refine ⟨9813540164266824308906615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6542360109511216205937743 9813540164266824308906615)
            ·
              refine ⟨14720310246400236463359923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9813540164266824308906615 14720310246400236463359923)
              ·
                refine ⟨22080465369600354695039885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14720310246400236463359923 22080465369600354695039885)
                ·
                  refine ⟨8280174513600133010639957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22080465369600354695039885 8280174513600133010639957)
                  ·
                    refine ⟨97033295081251558718437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8280174513600133010639957 97033295081251558718437)
                    ·
                      rfl

theorem cell23_566915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 8].length) (baseStart_566915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566915 prefixEnd_566915 := by exact prefixLift 566915
  have htrace : WordTrace (prefixWord ++ tailWord_566915) baseStart_566915 baseEnd_566915 := by
    simpa [prefixWord, tailWord_566915, baseEnd_566915] using wordTrace_append hprefix tailTrace_566915
  have hstable : (prefixWord ++ tailWord_566915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566915).length < 2 ^ (prefixWord ++ tailWord_566915).sum := by decide
  have hdescent : baseEnd_566915 < baseStart_566915 := by decide
  rcases family_descends (prefixWord ++ tailWord_566915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566920 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_566920 : Nat := 118140960795 + 566920 * 2 ^ 59
def prefixEnd_566920 : Nat := 4983230072969 + 3 ^ 40 * 566920 * 2
def baseEnd_566920 : Nat := 291102452647027156592789

theorem tailTrace_566920 : CollatzResearch.WordTrace tailWord_566920 prefixEnd_566920 291102452647027156592789 := by
  unfold tailWord_566920
  simp only [CollatzResearch.WordTrace]
  refine ⟨10338635553076568536349107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13784847404102091381798809 10338635553076568536349107)
  ·
    refine ⟨15507953329614852804523661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10338635553076568536349107 15507953329614852804523661)
    ·
      refine ⟨5815482498605569801696373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15507953329614852804523661 5815482498605569801696373)
      ·
        refine ⟨545201484244272168909035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5815482498605569801696373 545201484244272168909035)
        ·
          refine ⟨817802226366408253363553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545201484244272168909035 817802226366408253363553)
          ·
            refine ⟨613351669774806190022665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817802226366408253363553 613351669774806190022665)
            ·
              refine ⟨460013752331104642516999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613351669774806190022665 460013752331104642516999)
              ·
                refine ⟨690020628496656963775499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460013752331104642516999 690020628496656963775499)
                ·
                  refine ⟨1035030942744985445663249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690020628496656963775499 1035030942744985445663249)
                  ·
                    refine ⟨776273207058739084247437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1035030942744985445663249 776273207058739084247437)
                    ·
                      refine ⟨291102452647027156592789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 776273207058739084247437 291102452647027156592789)
                      ·
                        rfl

theorem cell23_566920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_566920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566920 prefixEnd_566920 := by exact prefixLift 566920
  have htrace : WordTrace (prefixWord ++ tailWord_566920) baseStart_566920 baseEnd_566920 := by
    simpa [prefixWord, tailWord_566920, baseEnd_566920] using wordTrace_append hprefix tailTrace_566920
  have hstable : (prefixWord ++ tailWord_566920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566920).length < 2 ^ (prefixWord ++ tailWord_566920).sum := by decide
  have hdescent : baseEnd_566920 < baseStart_566920 := by decide
  rcases family_descends (prefixWord ++ tailWord_566920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566962 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 7]
def baseStart_566962 : Nat := 118140960795 + 566962 * 2 ^ 59
def prefixEnd_566962 : Nat := 4983230072969 + 3 ^ 40 * 566962 * 2
def baseEnd_566962 : Nat := 32347113203835110251955

theorem tailTrace_566962 : CollatzResearch.WordTrace tailWord_566962 prefixEnd_566962 32347113203835110251955 := by
  unfold tailWord_566962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169700743000244561431785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13785868648000652163818093 5169700743000244561431785)
  ·
    refine ⟨3877275557250183421073839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5169700743000244561431785 3877275557250183421073839)
    ·
      refine ⟨5815913335875275131610759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3877275557250183421073839 5815913335875275131610759)
      ·
        refine ⟨8723870003812912697416139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5815913335875275131610759 8723870003812912697416139)
        ·
          refine ⟨13085805005719369046124209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8723870003812912697416139 13085805005719369046124209)
          ·
            refine ⟨9814353754289526784593157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13085805005719369046124209 9814353754289526784593157)
            ·
              refine ⟨1840191328929286272111217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9814353754289526784593157 1840191328929286272111217)
              ·
                refine ⟨1380143496696964704083413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840191328929286272111217 1380143496696964704083413)
                ·
                  refine ⟨32347113203835110251955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1380143496696964704083413 32347113203835110251955)
                  ·
                    rfl

theorem cell23_566962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_566962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566962 prefixEnd_566962 := by exact prefixLift 566962
  have htrace : WordTrace (prefixWord ++ tailWord_566962) baseStart_566962 baseEnd_566962 := by
    simpa [prefixWord, tailWord_566962, baseEnd_566962] using wordTrace_append hprefix tailTrace_566962
  have hstable : (prefixWord ++ tailWord_566962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566962).length < 2 ^ (prefixWord ++ tailWord_566962).sum := by decide
  have hdescent : baseEnd_566962 < baseStart_566962 := by decide
  rcases family_descends (prefixWord ++ tailWord_566962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566996 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 7]
def baseStart_566996 : Nat := 118140960795 + 566996 * 2 ^ 59
def prefixEnd_566996 : Nat := 4983230072969 + 3 ^ 40 * 566996 * 2
def baseEnd_566996 : Nat := 32349053019640984360271

theorem tailTrace_566996 : CollatzResearch.WordTrace tailWord_566996 prefixEnd_566996 32349053019640984360271 := by
  unfold tailWord_566996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10340021526938901026232421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13786695369251868034976561 10340021526938901026232421)
  ·
    refine ⟨1938754036301043942418579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10340021526938901026232421 1938754036301043942418579)
    ·
      refine ⟨2908131054451565913627869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1938754036301043942418579 2908131054451565913627869)
      ·
        refine ⟨1090549145419337217610451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2908131054451565913627869 1090549145419337217610451)
        ·
          refine ⟨1635823718129005826415677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090549145419337217610451 1635823718129005826415677)
          ·
            refine ⟨613433894298377184905879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1635823718129005826415677 613433894298377184905879)
            ·
              refine ⟨920150841447565777358819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613433894298377184905879 920150841447565777358819)
              ·
                refine ⟨1380226262171348666038229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920150841447565777358819 1380226262171348666038229)
                ·
                  refine ⟨32349053019640984360271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1380226262171348666038229 32349053019640984360271)
                  ·
                    rfl

theorem cell23_566996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_566996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566996 prefixEnd_566996 := by exact prefixLift 566996
  have htrace : WordTrace (prefixWord ++ tailWord_566996) baseStart_566996 baseEnd_566996 := by
    simpa [prefixWord, tailWord_566996, baseEnd_566996] using wordTrace_append hprefix tailTrace_566996
  have hstable : (prefixWord ++ tailWord_566996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566996).length < 2 ^ (prefixWord ++ tailWord_566996).sum := by decide
  have hdescent : baseEnd_566996 < baseStart_566996 := by decide
  rcases family_descends (prefixWord ++ tailWord_566996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_566999 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 2, 5, 2]
def baseStart_566999 : Nat := 118140960795 + 566999 * 2 ^ 59
def prefixEnd_566999 : Nat := 4983230072969 + 3 ^ 40 * 566999 * 2
def baseEnd_566999 : Nat := 291143017618732347504925

theorem tailTrace_566999 : CollatzResearch.WordTrace tailWord_566999 prefixEnd_566999 291143017618732347504925 := by
  unfold tailWord_566999
  simp only [CollatzResearch.WordTrace]
  refine ⟨20680152472866933564824051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13786768315244622376549367 20680152472866933564824051)
  ·
    refine ⟨31020228709300400347236077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20680152472866933564824051 31020228709300400347236077)
    ·
      refine ⟨11632585765987650130213529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31020228709300400347236077 11632585765987650130213529)
      ·
        refine ⟨8724439324490737597660147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11632585765987650130213529 8724439324490737597660147)
        ·
          refine ⟨13086658986736106396490221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8724439324490737597660147 13086658986736106396490221)
          ·
            refine ⟨4907497120026039898683833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13086658986736106396490221 4907497120026039898683833)
            ·
              refine ⟨3680622840019529924012875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4907497120026039898683833 3680622840019529924012875)
              ·
                refine ⟨5520934260029294886019313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680622840019529924012875 5520934260029294886019313)
                ·
                  refine ⟨4140700695021971164514485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5520934260029294886019313 4140700695021971164514485)
                  ·
                    refine ⟨388190690158309796673233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4140700695021971164514485 388190690158309796673233)
                    ·
                      refine ⟨291143017618732347504925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388190690158309796673233 291143017618732347504925)
                      ·
                        rfl

theorem cell23_566999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_566999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_566999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_566999 prefixEnd_566999 := by exact prefixLift 566999
  have htrace : WordTrace (prefixWord ++ tailWord_566999) baseStart_566999 baseEnd_566999 := by
    simpa [prefixWord, tailWord_566999, baseEnd_566999] using wordTrace_append hprefix tailTrace_566999
  have hstable : (prefixWord ++ tailWord_566999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_566999).length < 2 ^ (prefixWord ++ tailWord_566999).sum := by decide
  have hdescent : baseEnd_566999 < baseStart_566999 := by decide
  rcases family_descends (prefixWord ++ tailWord_566999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567002 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_567002 : Nat := 118140960795 + 567002 * 2 ^ 59
def prefixEnd_567002 : Nat := 4983230072969 + 3 ^ 40 * 567002 * 2
def baseEnd_567002 : Nat := 291144558060695835767411

theorem tailTrace_567002 : CollatzResearch.WordTrace tailWord_567002 prefixEnd_567002 291144558060695835767411 := by
  unfold tailWord_567002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170065472964016269295815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13786841261237376718122173 5170065472964016269295815)
  ·
    refine ⟨7755098209446024403943723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5170065472964016269295815 7755098209446024403943723)
    ·
      refine ⟨11632647314169036605915585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7755098209446024403943723 11632647314169036605915585)
      ·
        refine ⟨8724485485626777454436689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11632647314169036605915585 8724485485626777454436689)
        ·
          refine ⟨6543364114220083090827517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8724485485626777454436689 6543364114220083090827517)
          ·
            refine ⟨2453761542832531159060319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6543364114220083090827517 2453761542832531159060319)
            ·
              refine ⟨3680642314248796738590479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453761542832531159060319 3680642314248796738590479)
              ·
                refine ⟨5520963471373195107885719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680642314248796738590479 5520963471373195107885719)
                ·
                  refine ⟨8281445207059792661828579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520963471373195107885719 8281445207059792661828579)
                  ·
                    refine ⟨12422167810589688992742869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8281445207059792661828579 12422167810589688992742869)
                    ·
                      refine ⟨291144558060695835767411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12422167810589688992742869 291144558060695835767411)
                      ·
                        rfl

theorem cell23_567002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_567002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567002 prefixEnd_567002 := by exact prefixLift 567002
  have htrace : WordTrace (prefixWord ++ tailWord_567002) baseStart_567002 baseEnd_567002 := by
    simpa [prefixWord, tailWord_567002, baseEnd_567002] using wordTrace_append hprefix tailTrace_567002
  have hstable : (prefixWord ++ tailWord_567002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567002).length < 2 ^ (prefixWord ++ tailWord_567002).sum := by decide
  have hdescent : baseEnd_567002 < baseStart_567002 := by decide
  rcases family_descends (prefixWord ++ tailWord_567002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567052 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 8]
def baseStart_567052 : Nat := 118140960795 + 567052 * 2 ^ 59
def prefixEnd_567052 : Nat := 4983230072969 + 3 ^ 40 * 567052 * 2
def baseEnd_567052 : Nat := 32352248010380071126909

theorem tailTrace_567052 : CollatzResearch.WordTrace tailWord_567052 prefixEnd_567052 32352248010380071126909 := by
  unfold tailWord_567052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10341042770837461808251705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13788057027783282411002273 10341042770837461808251705)
  ·
    refine ⟨7755782078128096356188779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10341042770837461808251705 7755782078128096356188779)
    ·
      refine ⟨11633673117192144534283169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7755782078128096356188779 11633673117192144534283169)
      ·
        refine ⟨8725254837894108400712377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11633673117192144534283169 8725254837894108400712377)
        ·
          refine ⟨6543941128420581300534283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8725254837894108400712377 6543941128420581300534283)
          ·
            refine ⟨9815911692630871950801425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6543941128420581300534283 9815911692630871950801425)
            ·
              refine ⟨7361933769473153963101069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9815911692630871950801425 7361933769473153963101069)
              ·
                refine ⟨2760725163552432736162901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7361933769473153963101069 2760725163552432736162901)
                ·
                  refine ⟨32352248010380071126909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2760725163552432736162901 32352248010380071126909)
                  ·
                    rfl

theorem cell23_567052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_567052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567052 prefixEnd_567052 := by exact prefixLift 567052
  have htrace : WordTrace (prefixWord ++ tailWord_567052) baseStart_567052 baseEnd_567052 := by
    simpa [prefixWord, tailWord_567052, baseEnd_567052] using wordTrace_append hprefix tailTrace_567052
  have hstable : (prefixWord ++ tailWord_567052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567052).length < 2 ^ (prefixWord ++ tailWord_567052).sum := by decide
  have hdescent : baseEnd_567052 < baseStart_567052 := by decide
  rcases family_descends (prefixWord ++ tailWord_567052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567103 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 6]
def baseStart_567103 : Nat := 118140960795 + 567103 * 2 ^ 59
def prefixEnd_567103 : Nat := 4983230072969 + 3 ^ 40 * 567103 * 2
def baseEnd_567103 : Nat := 32355157734088882289383

theorem tailTrace_567103 : CollatzResearch.WordTrace tailWord_567103 prefixEnd_567103 32355157734088882289383 := by
  unfold tailWord_567103
  simp only [CollatzResearch.WordTrace]
  refine ⟨20683945664490159326609963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13789297109660106217739975 20683945664490159326609963)
  ·
    refine ⟨31025918496735238989914945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20683945664490159326609963 31025918496735238989914945)
    ·
      refine ⟨23269438872551429242436209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31025918496735238989914945 23269438872551429242436209)
      ·
        refine ⟨17452079154413571931827157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23269438872551429242436209 17452079154413571931827157)
        ·
          refine ⟨409033105181568092152199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17452079154413571931827157 409033105181568092152199)
          ·
            refine ⟨613549657772352138228299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409033105181568092152199 613549657772352138228299)
            ·
              refine ⟨920324486658528207342449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613549657772352138228299 920324486658528207342449)
              ·
                refine ⟨690243364993896155506837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920324486658528207342449 690243364993896155506837)
                ·
                  refine ⟨32355157734088882289383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 690243364993896155506837 32355157734088882289383)
                  ·
                    rfl

theorem cell23_567103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 6].length) (baseStart_567103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567103 prefixEnd_567103 := by exact prefixLift 567103
  have htrace : WordTrace (prefixWord ++ tailWord_567103) baseStart_567103 baseEnd_567103 := by
    simpa [prefixWord, tailWord_567103, baseEnd_567103] using wordTrace_append hprefix tailTrace_567103
  have hstable : (prefixWord ++ tailWord_567103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567103).length < 2 ^ (prefixWord ++ tailWord_567103).sum := by decide
  have hdescent : baseEnd_567103 < baseStart_567103 := by decide
  rcases family_descends (prefixWord ++ tailWord_567103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567113 : List Nat := [1, 2, 1, 1, 2, 4, 1, 6, 1, 1, 3]
def baseStart_567113 : Nat := 118140960795 + 567113 * 2 ^ 59
def prefixEnd_567113 : Nat := 4983230072969 + 3 ^ 40 * 567113 * 2
def baseEnd_567113 : Nat := 291201554413344901479401

theorem tailTrace_567113 : CollatzResearch.WordTrace tailWord_567113 prefixEnd_567113 291201554413344901479401 := by
  unfold tailWord_567113
  simp only [CollatzResearch.WordTrace]
  refine ⟨20684310394453931034473993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13789540262969287356315995 20684310394453931034473993)
  ·
    refine ⟨15513232795840448275855495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20684310394453931034473993 15513232795840448275855495)
    ·
      refine ⟨23269849193760672413783243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15513232795840448275855495 23269849193760672413783243)
      ·
        refine ⟨34904773790641008620674865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23269849193760672413783243 34904773790641008620674865)
        ·
          refine ⟨26178580342980756465506149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34904773790641008620674865 26178580342980756465506149)
          ·
            refine ⟨4908483814308891837282403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26178580342980756465506149 4908483814308891837282403)
            ·
              refine ⟨7362725721463337755923605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908483814308891837282403 7362725721463337755923605)
              ·
                refine ⟨345127768193593957308919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7362725721463337755923605 345127768193593957308919)
                ·
                  refine ⟨517691652290390935963379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345127768193593957308919 517691652290390935963379)
                  ·
                    refine ⟨776537478435586403945069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 517691652290390935963379 776537478435586403945069)
                    ·
                      refine ⟨291201554413344901479401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 776537478435586403945069 291201554413344901479401)
                      ·
                        rfl

theorem cell23_567113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 1, 1, 3].length) (baseStart_567113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567113 prefixEnd_567113 := by exact prefixLift 567113
  have htrace : WordTrace (prefixWord ++ tailWord_567113) baseStart_567113 baseEnd_567113 := by
    simpa [prefixWord, tailWord_567113, baseEnd_567113] using wordTrace_append hprefix tailTrace_567113
  have hstable : (prefixWord ++ tailWord_567113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567113).length < 2 ^ (prefixWord ++ tailWord_567113).sum := by decide
  have hdescent : baseEnd_567113 < baseStart_567113 := by decide
  rcases family_descends (prefixWord ++ tailWord_567113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567136 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 4]
def baseStart_567136 : Nat := 118140960795 + 567136 * 2 ^ 59
def prefixEnd_567136 : Nat := 4983230072969 + 3 ^ 40 * 567136 * 2
def baseEnd_567136 : Nat := 291213364468398311491795

theorem tailTrace_567136 : CollatzResearch.WordTrace tailWord_567136 prefixEnd_567136 291213364468398311491795 := by
  unfold tailWord_567136
  simp only [CollatzResearch.WordTrace]
  refine ⟨10342574636685302981280631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13790099515580403975040841 10342574636685302981280631)
  ·
    refine ⟨15513861955027954471920947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10342574636685302981280631 15513861955027954471920947)
    ·
      refine ⟨23270792932541931707881421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15513861955027954471920947 23270792932541931707881421)
      ·
        refine ⟨8726547349703224390455533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23270792932541931707881421 8726547349703224390455533)
        ·
          refine ⟨3272455256138709146420825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8726547349703224390455533 3272455256138709146420825)
          ·
            refine ⟨2454341442104031859815619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3272455256138709146420825 2454341442104031859815619)
            ·
              refine ⟨3681512163156047789723429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454341442104031859815619 3681512163156047789723429)
              ·
                refine ⟨690283530591758960573143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3681512163156047789723429 690283530591758960573143)
                ·
                  refine ⟨1035425295887638440859715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690283530591758960573143 1035425295887638440859715)
                  ·
                    refine ⟨1553137943831457661289573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1035425295887638440859715 1553137943831457661289573)
                    ·
                      refine ⟨291213364468398311491795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1553137943831457661289573 291213364468398311491795)
                      ·
                        rfl

theorem cell23_567136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_567136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567136 prefixEnd_567136 := by exact prefixLift 567136
  have htrace : WordTrace (prefixWord ++ tailWord_567136) baseStart_567136 baseEnd_567136 := by
    simpa [prefixWord, tailWord_567136, baseEnd_567136] using wordTrace_append hprefix tailTrace_567136
  have hstable : (prefixWord ++ tailWord_567136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567136).length < 2 ^ (prefixWord ++ tailWord_567136).sum := by decide
  have hdescent : baseEnd_567136 < baseStart_567136 := by decide
  rcases family_descends (prefixWord ++ tailWord_567136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567176 : List Nat := [2, 1, 3, 3, 3, 1, 2, 8]
def baseStart_567176 : Nat := 118140960795 + 567176 * 2 ^ 59
def prefixEnd_567176 : Nat := 4983230072969 + 3 ^ 40 * 567176 * 2
def baseEnd_567176 : Nat := 10786440877576968703393

theorem tailTrace_567176 : CollatzResearch.WordTrace tailWord_567176 prefixEnd_567176 10786440877576968703393 := by
  unfold tailWord_567176
  simp only [CollatzResearch.WordTrace]
  refine ⟨10343304096612846397008691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13791072128817128529344921 10343304096612846397008691)
  ·
    refine ⟨15514956144919269595513037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10343304096612846397008691 15514956144919269595513037)
    ·
      refine ⟨5818108554344726098317389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15514956144919269595513037 5818108554344726098317389)
      ·
        refine ⟨2181790707879272286869021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5818108554344726098317389 2181790707879272286869021)
        ·
          refine ⟨818171515454727107575883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2181790707879272286869021 818171515454727107575883)
          ·
            refine ⟨1227257273182090661363825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818171515454727107575883 1227257273182090661363825)
            ·
              refine ⟨920442954886567996022869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227257273182090661363825 920442954886567996022869)
              ·
                refine ⟨10786440877576968703393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 920442954886567996022869 10786440877576968703393)
                ·
                  rfl

theorem cell23_567176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 8].length) (baseStart_567176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567176 prefixEnd_567176 := by exact prefixLift 567176
  have htrace : WordTrace (prefixWord ++ tailWord_567176) baseStart_567176 baseEnd_567176 := by
    simpa [prefixWord, tailWord_567176, baseEnd_567176] using wordTrace_append hprefix tailTrace_567176
  have hstable : (prefixWord ++ tailWord_567176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567176).length < 2 ^ (prefixWord ++ tailWord_567176).sum := by decide
  have hdescent : baseEnd_567176 < baseStart_567176 := by decide
  rcases family_descends (prefixWord ++ tailWord_567176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567214 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_567214 : Nat := 118140960795 + 567214 * 2 ^ 59
def prefixEnd_567214 : Nat := 4983230072969 + 3 ^ 40 * 567214 * 2
def baseEnd_567214 : Nat := 97084471986483002105479

theorem tailTrace_567214 : CollatzResearch.WordTrace tailWord_567214 prefixEnd_567214 97084471986483002105479 := by
  unfold tailWord_567214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585999270886003160487587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13791996111392016855933797 2585999270886003160487587)
  ·
    refine ⟨3878998906329004740731381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2585999270886003160487587 3878998906329004740731381)
    ·
      refine ⟨363656147468344194443567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3878998906329004740731381 363656147468344194443567)
      ·
        refine ⟨545484221202516291665351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363656147468344194443567 545484221202516291665351)
        ·
          refine ⟨818226331803774437498027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545484221202516291665351 818226331803774437498027)
          ·
            refine ⟨1227339497705661656247041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818226331803774437498027 1227339497705661656247041)
            ·
              refine ⟨920504623279246242185281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227339497705661656247041 920504623279246242185281)
              ·
                refine ⟨690378467459434681638961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 920504623279246242185281 690378467459434681638961)
                ·
                  refine ⟨517783850594576011229221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 690378467459434681638961 517783850594576011229221)
                  ·
                    refine ⟨97084471986483002105479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 517783850594576011229221 97084471986483002105479)
                    ·
                      rfl

theorem cell23_567214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_567214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567214 prefixEnd_567214 := by exact prefixLift 567214
  have htrace : WordTrace (prefixWord ++ tailWord_567214) baseStart_567214 baseEnd_567214 := by
    simpa [prefixWord, tailWord_567214, baseEnd_567214] using wordTrace_append hprefix tailTrace_567214
  have hstable : (prefixWord ++ tailWord_567214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567214).length < 2 ^ (prefixWord ++ tailWord_567214).sum := by decide
  have hdescent : baseEnd_567214 < baseStart_567214 := by decide
  rcases family_descends (prefixWord ++ tailWord_567214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567219 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 2, 6]
def baseStart_567219 : Nat := 118140960795 + 567219 * 2 ^ 59
def prefixEnd_567219 : Nat := 4983230072969 + 3 ^ 40 * 567219 * 2
def baseEnd_567219 : Nat := 97085327787573828917971

theorem tailTrace_567219 : CollatzResearch.WordTrace tailWord_567219 prefixEnd_567219 97085327787573828917971 := by
  unfold tailWord_567219
  simp only [CollatzResearch.WordTrace]
  refine ⟨20688176532069911137832711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13792117688046607425221807 20688176532069911137832711)
  ·
    refine ⟨31032264798104866706749067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20688176532069911137832711 31032264798104866706749067)
    ·
      refine ⟨46548397197157300060123601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31032264798104866706749067 46548397197157300060123601)
      ·
        refine ⟨34911297897867975045092701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46548397197157300060123601 34911297897867975045092701)
        ·
          refine ⟨13091736711700490641909763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34911297897867975045092701 13091736711700490641909763)
          ·
            refine ⟨19637605067550735962864645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13091736711700490641909763 19637605067550735962864645)
            ·
              refine ⟨3682050950165762993037121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19637605067550735962864645 3682050950165762993037121)
              ·
                refine ⟨2761538212624322244777841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3682050950165762993037121 2761538212624322244777841)
                ·
                  refine ⟨2071153659468241683583381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2761538212624322244777841 2071153659468241683583381)
                  ·
                    refine ⟨97085327787573828917971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2071153659468241683583381 97085327787573828917971)
                    ·
                      rfl

theorem cell23_567219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 6].length) (baseStart_567219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567219 prefixEnd_567219 := by exact prefixLift 567219
  have htrace : WordTrace (prefixWord ++ tailWord_567219) baseStart_567219 baseEnd_567219 := by
    simpa [prefixWord, tailWord_567219, baseEnd_567219] using wordTrace_append hprefix tailTrace_567219
  have hstable : (prefixWord ++ tailWord_567219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567219).length < 2 ^ (prefixWord ++ tailWord_567219).sum := by decide
  have hdescent : baseEnd_567219 < baseStart_567219 := by decide
  rcases family_descends (prefixWord ++ tailWord_567219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567243 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 1, 4, 2]
def baseStart_567243 : Nat := 118140960795 + 567243 * 2 ^ 59
def prefixEnd_567243 : Nat := 4983230072969 + 3 ^ 40 * 567243 * 2
def baseEnd_567243 : Nat := 291268306898429392853803

theorem tailTrace_567243 : CollatzResearch.WordTrace tailWord_567243 prefixEnd_567243 291268306898429392853803 := by
  unfold tailWord_567243
  simp only [CollatzResearch.WordTrace]
  refine ⟨20689051883982963236706383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13792701255988642157804255 20689051883982963236706383)
  ·
    refine ⟨31033577825974444855059575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20689051883982963236706383 31033577825974444855059575)
    ·
      refine ⟨46550366738961667282589363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31033577825974444855059575 46550366738961667282589363)
      ·
        refine ⟨69825550108442500923884045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46550366738961667282589363 69825550108442500923884045)
        ·
          refine ⟨26184581290665937846456517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69825550108442500923884045 26184581290665937846456517)
          ·
            refine ⟨4909608991999863346210597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26184581290665937846456517 4909608991999863346210597)
            ·
              refine ⟨920551685999974377414487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4909608991999863346210597 920551685999974377414487)
              ·
                refine ⟨1380827528999961566121731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920551685999974377414487 1380827528999961566121731)
                ·
                  refine ⟨2071241293499942349182597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380827528999961566121731 2071241293499942349182597)
                  ·
                    refine ⟨388357742531239190471737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2071241293499942349182597 388357742531239190471737)
                    ·
                      refine ⟨291268306898429392853803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388357742531239190471737 291268306898429392853803)
                      ·
                        rfl

theorem cell23_567243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 4, 2].length) (baseStart_567243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567243 prefixEnd_567243 := by exact prefixLift 567243
  have htrace : WordTrace (prefixWord ++ tailWord_567243) baseStart_567243 baseEnd_567243 := by
    simpa [prefixWord, tailWord_567243, baseEnd_567243] using wordTrace_append hprefix tailTrace_567243
  have hstable : (prefixWord ++ tailWord_567243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567243).length < 2 ^ (prefixWord ++ tailWord_567243).sum := by decide
  have hdescent : baseEnd_567243 < baseStart_567243 := by decide
  rcases family_descends (prefixWord ++ tailWord_567243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567246 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_567246 : Nat := 118140960795 + 567246 * 2 ^ 59
def prefixEnd_567246 : Nat := 4983230072969 + 3 ^ 40 * 567246 * 2
def baseEnd_567246 : Nat := 291269847340392881116289

theorem tailTrace_567246 : CollatzResearch.WordTrace tailWord_567246 prefixEnd_567246 291269847340392881116289 := by
  unfold tailWord_567246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2586145162871511843633199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13792774201981396499377061 2586145162871511843633199)
  ·
    refine ⟨3879217744307267765449799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2586145162871511843633199 3879217744307267765449799)
    ·
      refine ⟨5818826616460901648174699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3879217744307267765449799 5818826616460901648174699)
      ·
        refine ⟨8728239924691352472262049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5818826616460901648174699 8728239924691352472262049)
        ·
          refine ⟨6546179943518514354196537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8728239924691352472262049 6546179943518514354196537)
          ·
            refine ⟨4909634957638885765647403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6546179943518514354196537 4909634957638885765647403)
            ·
              refine ⟨7364452436458328648471105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4909634957638885765647403 7364452436458328648471105)
              ·
                refine ⟨5523339327343746486353329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7364452436458328648471105 5523339327343746486353329)
                ·
                  refine ⟨4142504495507809864764997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5523339327343746486353329 4142504495507809864764997)
                  ·
                    refine ⟨776719592907714349643437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4142504495507809864764997 776719592907714349643437)
                    ·
                      refine ⟨291269847340392881116289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 776719592907714349643437 291269847340392881116289)
                      ·
                        rfl

theorem cell23_567246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_567246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567246 prefixEnd_567246 := by exact prefixLift 567246
  have htrace : WordTrace (prefixWord ++ tailWord_567246) baseStart_567246 baseEnd_567246 := by
    simpa [prefixWord, tailWord_567246, baseEnd_567246] using wordTrace_append hprefix tailTrace_567246
  have hstable : (prefixWord ++ tailWord_567246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567246).length < 2 ^ (prefixWord ++ tailWord_567246).sum := by decide
  have hdescent : baseEnd_567246 < baseStart_567246 := by decide
  rcases family_descends (prefixWord ++ tailWord_567246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567317 : List Nat := [1, 3, 2, 1, 6, 1, 1, 3, 5]
def baseStart_567317 : Nat := 118140960795 + 567317 * 2 ^ 59
def prefixEnd_567317 : Nat := 4983230072969 + 3 ^ 40 * 567317 * 2
def baseEnd_567317 : Nat := 32367367162984678147607

theorem tailTrace_567317 : CollatzResearch.WordTrace tailWord_567317 prefixEnd_567317 32367367162984678147607 := by
  unfold tailWord_567317
  simp only [CollatzResearch.WordTrace]
  refine ⟨20691750885714873874900205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13794500590476582583266803 20691750885714873874900205)
  ·
    refine ⟨7759406582143077703087577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20691750885714873874900205 7759406582143077703087577)
    ·
      refine ⟨5819554936607308277315683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7759406582143077703087577 5819554936607308277315683)
      ·
        refine ⟨8729332404910962415973525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5819554936607308277315683 8729332404910962415973525)
        ·
          refine ⟨409187456480201363248759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8729332404910962415973525 409187456480201363248759)
          ·
            refine ⟨613781184720302044873139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409187456480201363248759 613781184720302044873139)
            ·
              refine ⟨920671777080453067309709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613781184720302044873139 920671777080453067309709)
              ·
                refine ⟨345251916405169900241141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 920671777080453067309709 345251916405169900241141)
                ·
                  refine ⟨32367367162984678147607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345251916405169900241141 32367367162984678147607)
                  ·
                    rfl

theorem cell23_567317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_567317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567317 prefixEnd_567317 := by exact prefixLift 567317
  have htrace : WordTrace (prefixWord ++ tailWord_567317) baseStart_567317 baseEnd_567317 := by
    simpa [prefixWord, tailWord_567317, baseEnd_567317] using wordTrace_append hprefix tailTrace_567317
  have hstable : (prefixWord ++ tailWord_567317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567317).length < 2 ^ (prefixWord ++ tailWord_567317).sum := by decide
  have hdescent : baseEnd_567317 < baseStart_567317 := by decide
  rcases family_descends (prefixWord ++ tailWord_567317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567333 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_567333 : Nat := 118140960795 + 567333 * 2 ^ 59
def prefixEnd_567333 : Nat := 4983230072969 + 3 ^ 40 * 567333 * 2
def baseEnd_567333 : Nat := 291314520157334040728389

theorem tailTrace_567333 : CollatzResearch.WordTrace tailWord_567333 prefixEnd_567333 291314520157334040728389 := by
  unfold tailWord_567333
  simp only [CollatzResearch.WordTrace]
  refine ⟨20692334453656908607482653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13794889635771272404988435 20692334453656908607482653)
  ·
    refine ⟨7759625420121340727805995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20692334453656908607482653 7759625420121340727805995)
    ·
      refine ⟨11639438130182011091708993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7759625420121340727805995 11639438130182011091708993)
      ·
        refine ⟨8729578597636508318781745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11639438130182011091708993 8729578597636508318781745)
        ·
          refine ⟨6547183948227381239086309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8729578597636508318781745 6547183948227381239086309)
          ·
            refine ⟨1227596990292633982328683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6547183948227381239086309 1227596990292633982328683)
            ·
              refine ⟨1841395485438950973493025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227596990292633982328683 1841395485438950973493025)
              ·
                refine ⟨1381046614079213230119769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1841395485438950973493025 1381046614079213230119769)
                ·
                  refine ⟨1035784960559409922589827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1381046614079213230119769 1035784960559409922589827)
                  ·
                    refine ⟨1553677440839114883884741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1035784960559409922589827 1553677440839114883884741)
                    ·
                      refine ⟨291314520157334040728389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1553677440839114883884741 291314520157334040728389)
                      ·
                        rfl

theorem cell23_567333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_567333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567333 prefixEnd_567333 := by exact prefixLift 567333
  have htrace : WordTrace (prefixWord ++ tailWord_567333) baseStart_567333 baseEnd_567333 := by
    simpa [prefixWord, tailWord_567333, baseEnd_567333] using wordTrace_append hprefix tailTrace_567333
  have hstable : (prefixWord ++ tailWord_567333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567333).length < 2 ^ (prefixWord ++ tailWord_567333).sum := by decide
  have hdescent : baseEnd_567333 < baseStart_567333 := by decide
  rcases family_descends (prefixWord ++ tailWord_567333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567350 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_567350 : Nat := 118140960795 + 567350 * 2 ^ 59
def prefixEnd_567350 : Nat := 4983230072969 + 3 ^ 40 * 567350 * 2
def baseEnd_567350 : Nat := 291323249328460474215811

theorem tailTrace_567350 : CollatzResearch.WordTrace tailWord_567350 prefixEnd_567350 291323249328460474215811 := by
  unfold tailWord_567350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1293309655912207531928219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13795302996396880340567669 1293309655912207531928219)
  ·
    refine ⟨1939964483868311297892329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1293309655912207531928219 1939964483868311297892329)
    ·
      refine ⟨1454973362901233473419247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1939964483868311297892329 1454973362901233473419247)
      ·
        refine ⟨2182460044351850210128871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454973362901233473419247 2182460044351850210128871)
        ·
          refine ⟨3273690066527775315193307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182460044351850210128871 3273690066527775315193307)
          ·
            refine ⟨4910535099791662972789961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273690066527775315193307 4910535099791662972789961)
            ·
              refine ⟨3682901324843747229592471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4910535099791662972789961 3682901324843747229592471)
              ·
                refine ⟨5524351987265620844388707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682901324843747229592471 5524351987265620844388707)
                ·
                  refine ⟨8286527980898431266583061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5524351987265620844388707 8286527980898431266583061)
                  ·
                    refine ⟨388430999104613965621081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8286527980898431266583061 388430999104613965621081)
                    ·
                      refine ⟨291323249328460474215811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388430999104613965621081 291323249328460474215811)
                      ·
                        rfl

theorem cell23_567350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_567350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567350 prefixEnd_567350 := by exact prefixLift 567350
  have htrace : WordTrace (prefixWord ++ tailWord_567350) baseStart_567350 baseEnd_567350 := by
    simpa [prefixWord, tailWord_567350, baseEnd_567350] using wordTrace_append hprefix tailTrace_567350
  have hstable : (prefixWord ++ tailWord_567350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567350).length < 2 ^ (prefixWord ++ tailWord_567350).sum := by decide
  have hdescent : baseEnd_567350 < baseStart_567350 := by decide
  rcases family_descends (prefixWord ++ tailWord_567350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567393 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 3, 5, 2]
def baseStart_567393 : Nat := 118140960795 + 567393 * 2 ^ 59
def prefixEnd_567393 : Nat := 4983230072969 + 3 ^ 40 * 567393 * 2
def baseEnd_567393 : Nat := 291345328996603805978113

theorem tailTrace_567393 : CollatzResearch.WordTrace tailWord_567393 prefixEnd_567393 291345328996603805978113 := by
  unfold tailWord_567393
  simp only [CollatzResearch.WordTrace]
  refine ⟨20694522833439538854666833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13796348555626359236444555 20694522833439538854666833)
  ·
    refine ⟨15520892125079654141000125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20694522833439538854666833 15520892125079654141000125)
    ·
      refine ⟨5820334546904870302875047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15520892125079654141000125 5820334546904870302875047)
      ·
        refine ⟨8730501820357305454312571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820334546904870302875047 8730501820357305454312571)
        ·
          refine ⟨13095752730535958181468857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8730501820357305454312571 13095752730535958181468857)
          ·
            refine ⟨9821814547901968636101643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13095752730535958181468857 9821814547901968636101643)
            ·
              refine ⟨14732721821852952954152465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9821814547901968636101643 14732721821852952954152465)
              ·
                refine ⟨11049541366389714715614349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14732721821852952954152465 11049541366389714715614349)
                ·
                  refine ⟨4143578012396143018355381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11049541366389714715614349 4143578012396143018355381)
                  ·
                    refine ⟨388460438662138407970817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4143578012396143018355381 388460438662138407970817)
                    ·
                      refine ⟨291345328996603805978113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388460438662138407970817 291345328996603805978113)
                      ·
                        rfl

theorem cell23_567393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_567393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567393 prefixEnd_567393 := by exact prefixLift 567393
  have htrace : WordTrace (prefixWord ++ tailWord_567393) baseStart_567393 baseEnd_567393 := by
    simpa [prefixWord, tailWord_567393, baseEnd_567393] using wordTrace_append hprefix tailTrace_567393
  have hstable : (prefixWord ++ tailWord_567393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567393).length < 2 ^ (prefixWord ++ tailWord_567393).sum := by decide
  have hdescent : baseEnd_567393 < baseStart_567393 := by decide
  rcases family_descends (prefixWord ++ tailWord_567393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567394 : List Nat := [3, 3, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_567394 : Nat := 118140960795 + 567394 * 2 ^ 59
def prefixEnd_567394 : Nat := 4983230072969 + 3 ^ 40 * 567394 * 2
def baseEnd_567394 : Nat := 97115280825752767355203

theorem tailTrace_567394 : CollatzResearch.WordTrace tailWord_567394 prefixEnd_567394 97115280825752767355203 := by
  unfold tailWord_567394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173639826608979006363309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13796372870957277350302157 5173639826608979006363309)
  ·
    refine ⟨1940114934978367127386241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5173639826608979006363309 1940114934978367127386241)
    ·
      refine ⟨1455086201233775345539681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1940114934978367127386241 1455086201233775345539681)
      ·
        refine ⟨1091314650925331509154761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1455086201233775345539681 1091314650925331509154761)
        ·
          refine ⟨818485988193998631866071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1091314650925331509154761 818485988193998631866071)
          ·
            refine ⟨1227728982290997947799107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818485988193998631866071 1227728982290997947799107)
            ·
              refine ⟨1841593473436496921698661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227728982290997947799107 1841593473436496921698661)
              ·
                refine ⟨345298776269343172818499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1841593473436496921698661 345298776269343172818499)
                ·
                  refine ⟨517948164404014759227749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345298776269343172818499 517948164404014759227749)
                  ·
                    refine ⟨97115280825752767355203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 517948164404014759227749 97115280825752767355203)
                    ·
                      rfl

theorem cell23_567394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_567394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567394 prefixEnd_567394 := by exact prefixLift 567394
  have htrace : WordTrace (prefixWord ++ tailWord_567394) baseStart_567394 baseEnd_567394 := by
    simpa [prefixWord, tailWord_567394, baseEnd_567394] using wordTrace_append hprefix tailTrace_567394
  have hstable : (prefixWord ++ tailWord_567394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567394).length < 2 ^ (prefixWord ++ tailWord_567394).sum := by decide
  have hdescent : baseEnd_567394 < baseStart_567394 := by decide
  rcases family_descends (prefixWord ++ tailWord_567394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567427 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 2, 3, 2]
def baseStart_567427 : Nat := 118140960795 + 567427 * 2 ^ 59
def prefixEnd_567427 : Nat := 4983230072969 + 3 ^ 40 * 567427 * 2
def baseEnd_567427 : Nat := 291362787338856672952957

theorem tailTrace_567427 : CollatzResearch.WordTrace tailWord_567427 prefixEnd_567427 291362787338856672952957 := by
  unfold tailWord_567427
  simp only [CollatzResearch.WordTrace]
  refine ⟨20695762915316362661404535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13797175276877575107603023 20695762915316362661404535)
  ·
    refine ⟨31043644372974543992106803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20695762915316362661404535 31043644372974543992106803)
    ·
      refine ⟨46565466559461815988160205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31043644372974543992106803 46565466559461815988160205)
      ·
        refine ⟨17462049959798180995560077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46565466559461815988160205 17462049959798180995560077)
        ·
          refine ⟨6548268734924317873335029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17462049959798180995560077 6548268734924317873335029)
          ·
            refine ⟨613900193899154800625159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6548268734924317873335029 613900193899154800625159)
            ·
              refine ⟨920850290848732200937739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613900193899154800625159 920850290848732200937739)
              ·
                refine ⟨1381275436273098301406609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920850290848732200937739 1381275436273098301406609)
                ·
                  refine ⟨1035956577204823726054957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1381275436273098301406609 1035956577204823726054957)
                  ·
                    refine ⟨388483716451808897270609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1035956577204823726054957 388483716451808897270609)
                    ·
                      refine ⟨291362787338856672952957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388483716451808897270609 291362787338856672952957)
                      ·
                        rfl

theorem cell23_567427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_567427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567427 prefixEnd_567427 := by exact prefixLift 567427
  have htrace : WordTrace (prefixWord ++ tailWord_567427) baseStart_567427 baseEnd_567427 := by
    simpa [prefixWord, tailWord_567427, baseEnd_567427] using wordTrace_append hprefix tailTrace_567427
  have hstable : (prefixWord ++ tailWord_567427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567427).length < 2 ^ (prefixWord ++ tailWord_567427).sum := by decide
  have hdescent : baseEnd_567427 < baseStart_567427 := by decide
  rcases family_descends (prefixWord ++ tailWord_567427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567433 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 4, 4]
def baseStart_567433 : Nat := 118140960795 + 567433 * 2 ^ 59
def prefixEnd_567433 : Nat := 4983230072969 + 3 ^ 40 * 567433 * 2
def baseEnd_567433 : Nat := 97121956074261216492643

theorem tailTrace_567433 : CollatzResearch.WordTrace tailWord_567433 prefixEnd_567433 97121956074261216492643 := by
  unfold tailWord_567433
  simp only [CollatzResearch.WordTrace]
  refine ⟨20695981753294625686122953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13797321168863083790748635 20695981753294625686122953)
  ·
    refine ⟨15521986314970969264592215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20695981753294625686122953 15521986314970969264592215)
    ·
      refine ⟨23282979472456453896888323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15521986314970969264592215 23282979472456453896888323)
      ·
        refine ⟨34924469208684680845332485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23282979472456453896888323 34924469208684680845332485)
        ·
          refine ⟨6548337976628377658499841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34924469208684680845332485 6548337976628377658499841)
          ·
            refine ⟨4911253482471283243874881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6548337976628377658499841 4911253482471283243874881)
            ·
              refine ⟨3683440111853462432906161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4911253482471283243874881 3683440111853462432906161)
              ·
                refine ⟨2762580083890096824679621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3683440111853462432906161 2762580083890096824679621)
                ·
                  refine ⟨517983765729393154627429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2762580083890096824679621 517983765729393154627429)
                  ·
                    refine ⟨97121956074261216492643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 517983765729393154627429 97121956074261216492643)
                    ·
                      rfl

theorem cell23_567433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 4].length) (baseStart_567433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567433 prefixEnd_567433 := by exact prefixLift 567433
  have htrace : WordTrace (prefixWord ++ tailWord_567433) baseStart_567433 baseEnd_567433 := by
    simpa [prefixWord, tailWord_567433, baseEnd_567433] using wordTrace_append hprefix tailTrace_567433
  have hstable : (prefixWord ++ tailWord_567433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567433).length < 2 ^ (prefixWord ++ tailWord_567433).sum := by decide
  have hdescent : baseEnd_567433 < baseStart_567433 := by decide
  rcases family_descends (prefixWord ++ tailWord_567433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567434 : List Nat := [3, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3]
def baseStart_567434 : Nat := 118140960795 + 567434 * 2 ^ 59
def prefixEnd_567434 : Nat := 4983230072969 + 3 ^ 40 * 567434 * 2
def baseEnd_567434 : Nat := 291366381703438145565425

theorem tailTrace_567434 : CollatzResearch.WordTrace tailWord_567434 prefixEnd_567434 291366381703438145565425 := by
  unfold tailWord_567434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174004556572750714227339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13797345484194001904606237 5174004556572750714227339)
  ·
    refine ⟨7761006834859126071341009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5174004556572750714227339 7761006834859126071341009)
    ·
      refine ⟨5820755126144344553505757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7761006834859126071341009 5820755126144344553505757)
      ·
        refine ⟨2182783172304129207564659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5820755126144344553505757 2182783172304129207564659)
        ·
          refine ⟨3274174758456193811346989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182783172304129207564659 3274174758456193811346989)
          ·
            refine ⟨1227815534421072679255121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3274174758456193811346989 1227815534421072679255121)
            ·
              refine ⟨920861650815804509441341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227815534421072679255121 920861650815804509441341)
              ·
                refine ⟨345323119055926691040503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 920861650815804509441341 345323119055926691040503)
                ·
                  refine ⟨517984678583890036560755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345323119055926691040503 517984678583890036560755)
                  ·
                    refine ⟨776977017875835054841133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 517984678583890036560755 776977017875835054841133)
                    ·
                      refine ⟨291366381703438145565425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 776977017875835054841133 291366381703438145565425)
                      ·
                        rfl

theorem cell23_567434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_567434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567434 prefixEnd_567434 := by exact prefixLift 567434
  have htrace : WordTrace (prefixWord ++ tailWord_567434) baseStart_567434 baseEnd_567434 := by
    simpa [prefixWord, tailWord_567434, baseEnd_567434] using wordTrace_append hprefix tailTrace_567434
  have hstable : (prefixWord ++ tailWord_567434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567434).length < 2 ^ (prefixWord ++ tailWord_567434).sum := by decide
  have hdescent : baseEnd_567434 < baseStart_567434 := by decide
  rcases family_descends (prefixWord ++ tailWord_567434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567436 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_567436 : Nat := 118140960795 + 567436 * 2 ^ 59
def prefixEnd_567436 : Nat := 4983230072969 + 3 ^ 40 * 567436 * 2
def baseEnd_567436 : Nat := 291367408664747137740415

theorem tailTrace_567436 : CollatzResearch.WordTrace tailWord_567436 prefixEnd_567436 291367408664747137740415 := by
  unfold tailWord_567436
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348045586141878599241081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13797394114855838132321441 10348045586141878599241081)
  ·
    refine ⟨7761034189606408949430811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10348045586141878599241081 7761034189606408949430811)
    ·
      refine ⟨11641551284409613424146217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7761034189606408949430811 11641551284409613424146217)
      ·
        refine ⟨8731163463307210068109663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11641551284409613424146217 8731163463307210068109663)
        ·
          refine ⟨13096745194960815102164495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8731163463307210068109663 13096745194960815102164495)
          ·
            refine ⟨19645117792441222653246743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13096745194960815102164495 19645117792441222653246743)
            ·
              refine ⟨29467676688661833979870115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19645117792441222653246743 29467676688661833979870115)
              ·
                refine ⟨44201515032992750969805173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29467676688661833979870115 44201515032992750969805173)
                ·
                  refine ⟨4143892034343070403419235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44201515032992750969805173 4143892034343070403419235)
                  ·
                    refine ⟨6215838051514605605128853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4143892034343070403419235 6215838051514605605128853)
                    ·
                      refine ⟨291367408664747137740415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6215838051514605605128853 291367408664747137740415)
                      ·
                        rfl

theorem cell23_567436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_567436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567436 prefixEnd_567436 := by exact prefixLift 567436
  have htrace : WordTrace (prefixWord ++ tailWord_567436) baseStart_567436 baseEnd_567436 := by
    simpa [prefixWord, tailWord_567436, baseEnd_567436] using wordTrace_append hprefix tailTrace_567436
  have hstable : (prefixWord ++ tailWord_567436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567436).length < 2 ^ (prefixWord ++ tailWord_567436).sum := by decide
  have hdescent : baseEnd_567436 < baseStart_567436 := by decide
  rcases family_descends (prefixWord ++ tailWord_567436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567440 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 5, 2, 2]
def baseStart_567440 : Nat := 118140960795 + 567440 * 2 ^ 59
def prefixEnd_567440 : Nat := 4983230072969 + 3 ^ 40 * 567440 * 2
def baseEnd_567440 : Nat := 291369462587365122090397

theorem tailTrace_567440 : CollatzResearch.WordTrace tailWord_567440 prefixEnd_567440 291369462587365122090397 := by
  unfold tailWord_567440
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348118532134632940813887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13797491376179510587751849 10348118532134632940813887)
  ·
    refine ⟨15522177798201949411220831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10348118532134632940813887 15522177798201949411220831)
    ·
      refine ⟨23283266697302924116831247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15522177798201949411220831 23283266697302924116831247)
      ·
        refine ⟨34924900045954386175246871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23283266697302924116831247 34924900045954386175246871)
        ·
          refine ⟨52387350068931579262870307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34924900045954386175246871 52387350068931579262870307)
          ·
            refine ⟨78581025103397368894305461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52387350068931579262870307 78581025103397368894305461)
            ·
              refine ⟨7366971103443503333841137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78581025103397368894305461 7366971103443503333841137)
              ·
                refine ⟨5525228327582627500380853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7366971103443503333841137 5525228327582627500380853)
                ·
                  refine ⟨517990155710871328160705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5525228327582627500380853 517990155710871328160705)
                  ·
                    refine ⟨388492616783153496120529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 517990155710871328160705 388492616783153496120529)
                    ·
                      refine ⟨291369462587365122090397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388492616783153496120529 291369462587365122090397)
                      ·
                        rfl

theorem cell23_567440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 2, 2].length) (baseStart_567440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567440 prefixEnd_567440 := by exact prefixLift 567440
  have htrace : WordTrace (prefixWord ++ tailWord_567440) baseStart_567440 baseEnd_567440 := by
    simpa [prefixWord, tailWord_567440, baseEnd_567440] using wordTrace_append hprefix tailTrace_567440
  have hstable : (prefixWord ++ tailWord_567440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567440).length < 2 ^ (prefixWord ++ tailWord_567440).sum := by decide
  have hdescent : baseEnd_567440 < baseStart_567440 := by decide
  rcases family_descends (prefixWord ++ tailWord_567440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567457 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 3, 2, 2]
def baseStart_567457 : Nat := 118140960795 + 567457 * 2 ^ 59
def prefixEnd_567457 : Nat := 4983230072969 + 3 ^ 40 * 567457 * 2
def baseEnd_567457 : Nat := 291378191758491555577819

theorem tailTrace_567457 : CollatzResearch.WordTrace tailWord_567457 prefixEnd_567457 291378191758491555577819 := by
  unfold tailWord_567457
  simp only [CollatzResearch.WordTrace]
  refine ⟨20696857105207677784996625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13797904736805118523331083 20696857105207677784996625)
  ·
    refine ⟨15522642828905758338747469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20696857105207677784996625 15522642828905758338747469)
    ·
      refine ⟨5820991060839659377030301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15522642828905758338747469 5820991060839659377030301)
      ·
        refine ⟨2182871647814872266386363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5820991060839659377030301 2182871647814872266386363)
        ·
          refine ⟨3274307471722308399579545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182871647814872266386363 3274307471722308399579545)
          ·
            refine ⟨2455730603791731299684659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274307471722308399579545 2455730603791731299684659)
            ·
              refine ⟨3683595905687596949526989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455730603791731299684659 3683595905687596949526989)
              ·
                refine ⟨1381348464632848856072621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3683595905687596949526989 1381348464632848856072621)
                ·
                  refine ⟨518005674237318321027233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1381348464632848856072621 518005674237318321027233)
                  ·
                    refine ⟨388504255677988740770425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 518005674237318321027233 388504255677988740770425)
                    ·
                      refine ⟨291378191758491555577819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388504255677988740770425 291378191758491555577819)
                      ·
                        rfl

theorem cell23_567457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_567457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567457 prefixEnd_567457 := by exact prefixLift 567457
  have htrace : WordTrace (prefixWord ++ tailWord_567457) baseStart_567457 baseEnd_567457 := by
    simpa [prefixWord, tailWord_567457, baseEnd_567457] using wordTrace_append hprefix tailTrace_567457
  have hstable : (prefixWord ++ tailWord_567457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567457).length < 2 ^ (prefixWord ++ tailWord_567457).sum := by decide
  have hdescent : baseEnd_567457 < baseStart_567457 := by decide
  rcases family_descends (prefixWord ++ tailWord_567457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567460 : List Nat := [2, 3, 1, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_567460 : Nat := 118140960795 + 567460 * 2 ^ 59
def prefixEnd_567460 : Nat := 4983230072969 + 3 ^ 40 * 567460 * 2
def baseEnd_567460 : Nat := 291379732200455043840305

theorem tailTrace_567460 : CollatzResearch.WordTrace tailWord_567460 prefixEnd_567460 291379732200455043840305 := by
  unfold tailWord_567460
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348483262098404648677917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13797977682797872864903889 10348483262098404648677917)
  ·
    refine ⟨3880681223286901743254219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10348483262098404648677917 3880681223286901743254219)
    ·
      refine ⟨5821021834930352614881329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3880681223286901743254219 5821021834930352614881329)
      ·
        refine ⟨4365766376197764461160997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5821021834930352614881329 4365766376197764461160997)
        ·
          refine ⟨818581195537080836467687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4365766376197764461160997 818581195537080836467687)
          ·
            refine ⟨1227871793305621254701531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818581195537080836467687 1227871793305621254701531)
            ·
              refine ⟨1841807689958431882052297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227871793305621254701531 1841807689958431882052297)
              ·
                refine ⟨1381355767468823911539223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1841807689958431882052297 1381355767468823911539223)
                ·
                  refine ⟨2072033651203235867308835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381355767468823911539223 2072033651203235867308835)
                  ·
                    refine ⟨3108050476804853800963253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2072033651203235867308835 3108050476804853800963253)
                    ·
                      refine ⟨291379732200455043840305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3108050476804853800963253 291379732200455043840305)
                      ·
                        rfl

theorem cell23_567460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_567460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567460 prefixEnd_567460 := by exact prefixLift 567460
  have htrace : WordTrace (prefixWord ++ tailWord_567460) baseStart_567460 baseEnd_567460 := by
    simpa [prefixWord, tailWord_567460, baseEnd_567460] using wordTrace_append hprefix tailTrace_567460
  have hstable : (prefixWord ++ tailWord_567460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567460).length < 2 ^ (prefixWord ++ tailWord_567460).sum := by decide
  have hdescent : baseEnd_567460 < baseStart_567460 := by decide
  rcases family_descends (prefixWord ++ tailWord_567460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567550 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_567550 : Nat := 118140960795 + 567550 * 2 ^ 59
def prefixEnd_567550 : Nat := 4983230072969 + 3 ^ 40 * 567550 * 2
def baseEnd_567550 : Nat := 291425945459359691714891

theorem tailTrace_567550 : CollatzResearch.WordTrace tailWord_567550 prefixEnd_567550 291425945459359691714891 := by
  unfold tailWord_567550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2587531136733844333516513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13800166062580503112088069 2587531136733844333516513)
  ·
    refine ⟨1940648352550383250137385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2587531136733844333516513 1940648352550383250137385)
    ·
      refine ⟨1455486264412787437603039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1940648352550383250137385 1455486264412787437603039)
      ·
        refine ⟨2183229396619181156404559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455486264412787437603039 2183229396619181156404559)
        ·
          refine ⟨3274844094928771734606839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183229396619181156404559 3274844094928771734606839)
          ·
            refine ⟨4912266142393157601910259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3274844094928771734606839 4912266142393157601910259)
            ·
              refine ⟨7368399213589736402865389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912266142393157601910259 7368399213589736402865389)
              ·
                refine ⟨2763149705096151151074521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7368399213589736402865389 2763149705096151151074521)
                ·
                  refine ⟨2072362278822113363305891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2763149705096151151074521 2072362278822113363305891)
                  ·
                    refine ⟨3108543418233170044958837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2072362278822113363305891 3108543418233170044958837)
                    ·
                      refine ⟨291425945459359691714891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3108543418233170044958837 291425945459359691714891)
                      ·
                        rfl

theorem cell23_567550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_567550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567550 prefixEnd_567550 := by exact prefixLift 567550
  have htrace : WordTrace (prefixWord ++ tailWord_567550) baseStart_567550 baseEnd_567550 := by
    simpa [prefixWord, tailWord_567550, baseEnd_567550] using wordTrace_append hprefix tailTrace_567550
  have hstable : (prefixWord ++ tailWord_567550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567550).length < 2 ^ (prefixWord ++ tailWord_567550).sum := by decide
  have hdescent : baseEnd_567550 < baseStart_567550 := by decide
  rcases family_descends (prefixWord ++ tailWord_567550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567564 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 2, 2, 2]
def baseStart_567564 : Nat := 118140960795 + 567564 * 2 ^ 59
def prefixEnd_567564 : Nat := 4983230072969 + 3 ^ 40 * 567564 * 2
def baseEnd_567564 : Nat := 291433134188522636939827

theorem tailTrace_567564 : CollatzResearch.WordTrace tailWord_567564 prefixEnd_567564 291433134188522636939827 := by
  unfold tailWord_567564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350379857910017529570873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13800506477213356706094497 10350379857910017529570873)
  ·
    refine ⟨7762784893432513147178155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10350379857910017529570873 7762784893432513147178155)
    ·
      refine ⟨11644177340148769720767233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7762784893432513147178155 11644177340148769720767233)
      ·
        refine ⟨8733133005111577290575425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11644177340148769720767233 8733133005111577290575425)
        ·
          refine ⟨6549849753833682967931569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8733133005111577290575425 6549849753833682967931569)
          ·
            refine ⟨4912387315375262225948677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6549849753833682967931569 4912387315375262225948677)
            ·
              refine ⟨921072621632861667365377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4912387315375262225948677 921072621632861667365377)
              ·
                refine ⟨690804466224646250524033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921072621632861667365377 690804466224646250524033)
                ·
                  refine ⟨518103349668484687893025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 690804466224646250524033 518103349668484687893025)
                  ·
                    refine ⟨388577512251363515919769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 518103349668484687893025 388577512251363515919769)
                    ·
                      refine ⟨291433134188522636939827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388577512251363515919769 291433134188522636939827)
                      ·
                        rfl

theorem cell23_567564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_567564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567564 prefixEnd_567564 := by exact prefixLift 567564
  have htrace : WordTrace (prefixWord ++ tailWord_567564) baseStart_567564 baseEnd_567564 := by
    simpa [prefixWord, tailWord_567564, baseEnd_567564] using wordTrace_append hprefix tailTrace_567564
  have hstable : (prefixWord ++ tailWord_567564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567564).length < 2 ^ (prefixWord ++ tailWord_567564).sum := by decide
  have hdescent : baseEnd_567564 < baseStart_567564 := by decide
  rcases family_descends (prefixWord ++ tailWord_567564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567604 : List Nat := [2, 5, 1, 1, 1, 3, 2, 3, 5]
def baseStart_567604 : Nat := 118140960795 + 567604 * 2 ^ 59
def prefixEnd_567604 : Nat := 4983230072969 + 3 ^ 40 * 567604 * 2
def baseEnd_567604 : Nat := 32383741490522497826627

theorem tailTrace_567604 : CollatzResearch.WordTrace tailWord_567604 prefixEnd_567604 32383741490522497826627 := by
  unfold tailWord_567604
  simp only [CollatzResearch.WordTrace]
  refine ⟨10351109317837560945298933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13801479090450081260398577 10351109317837560945298933)
  ·
    refine ⟨970416498547271338621775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10351109317837560945298933 970416498547271338621775)
    ·
      refine ⟨1455624747820907007932663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970416498547271338621775 1455624747820907007932663)
      ·
        refine ⟨2183437121731360511898995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455624747820907007932663 2183437121731360511898995)
        ·
          refine ⟨3275155682597040767848493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183437121731360511898995 3275155682597040767848493)
          ·
            refine ⟨1228183380973890287943185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3275155682597040767848493 1228183380973890287943185)
            ·
              refine ⟨921137535730417715957389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1228183380973890287943185 921137535730417715957389)
              ·
                refine ⟨345426575898906643484021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 921137535730417715957389 345426575898906643484021)
                ·
                  refine ⟨32383741490522497826627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345426575898906643484021 32383741490522497826627)
                  ·
                    rfl

theorem cell23_567604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_567604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567604 prefixEnd_567604 := by exact prefixLift 567604
  have htrace : WordTrace (prefixWord ++ tailWord_567604) baseStart_567604 baseEnd_567604 := by
    simpa [prefixWord, tailWord_567604, baseEnd_567604] using wordTrace_append hprefix tailTrace_567604
  have hstable : (prefixWord ++ tailWord_567604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567604).length < 2 ^ (prefixWord ++ tailWord_567604).sum := by decide
  have hdescent : baseEnd_567604 < baseStart_567604 := by decide
  rcases family_descends (prefixWord ++ tailWord_567604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567640 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_567640 : Nat := 118140960795 + 567640 * 2 ^ 59
def prefixEnd_567640 : Nat := 4983230072969 + 3 ^ 40 * 567640 * 2
def baseEnd_567640 : Nat := 291472158718264339589477

theorem tailTrace_567640 : CollatzResearch.WordTrace tailWord_567640 prefixEnd_567640 291472158718264339589477 := by
  unfold tailWord_567640
  simp only [CollatzResearch.WordTrace]
  refine ⟨10351765831772350019454187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13802354442363133359272249 10351765831772350019454187)
  ·
    refine ⟨15527648747658525029181281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10351765831772350019454187 15527648747658525029181281)
    ·
      refine ⟨11645736560743893771885961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15527648747658525029181281 11645736560743893771885961)
      ·
        refine ⟨8734302420557920328914471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11645736560743893771885961 8734302420557920328914471)
        ·
          refine ⟨13101453630836880493371707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8734302420557920328914471 13101453630836880493371707)
          ·
            refine ⟨19652180446255320740057561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13101453630836880493371707 19652180446255320740057561)
            ·
              refine ⟨14739135334691490555043171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19652180446255320740057561 14739135334691490555043171)
              ·
                refine ⟨22108703002037235832564757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14739135334691490555043171 22108703002037235832564757)
                ·
                  refine ⟨1036345453220495429651473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22108703002037235832564757 1036345453220495429651473)
                  ·
                    refine ⟨777259089915371572238605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1036345453220495429651473 777259089915371572238605)
                    ·
                      refine ⟨291472158718264339589477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 777259089915371572238605 291472158718264339589477)
                      ·
                        rfl

theorem cell23_567640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_567640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567640 prefixEnd_567640 := by exact prefixLift 567640
  have htrace : WordTrace (prefixWord ++ tailWord_567640) baseStart_567640 baseEnd_567640 := by
    simpa [prefixWord, tailWord_567640, baseEnd_567640] using wordTrace_append hprefix tailTrace_567640
  have hstable : (prefixWord ++ tailWord_567640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567640).length < 2 ^ (prefixWord ++ tailWord_567640).sum := by decide
  have hdescent : baseEnd_567640 < baseStart_567640 := by decide
  rcases family_descends (prefixWord ++ tailWord_567640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567663 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_567663 : Nat := 118140960795 + 567663 * 2 ^ 59
def prefixEnd_567663 : Nat := 4983230072969 + 3 ^ 40 * 567663 * 2
def baseEnd_567663 : Nat := 291483968773317749601871

theorem tailTrace_567663 : CollatzResearch.WordTrace tailWord_567663 prefixEnd_567663 291483968773317749601871 := by
  unfold tailWord_567663
  simp only [CollatzResearch.WordTrace]
  refine ⟨20704370542461374966995643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13802913694974249977997095 20704370542461374966995643)
  ·
    refine ⟨31056555813692062450493465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20704370542461374966995643 31056555813692062450493465)
    ·
      refine ⟨23292416860269046837870099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31056555813692062450493465 23292416860269046837870099)
      ·
        refine ⟨34938625290403570256805149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23292416860269046837870099 34938625290403570256805149)
        ·
          refine ⟨13101984483901338846301931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34938625290403570256805149 13101984483901338846301931)
          ·
            refine ⟨19652976725852008269452897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13101984483901338846301931 19652976725852008269452897)
            ·
              refine ⟨14739732544389006202089673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19652976725852008269452897 14739732544389006202089673)
              ·
                refine ⟨11054799408291754651567255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14739732544389006202089673 11054799408291754651567255)
                ·
                  refine ⟨16582199112437631977350883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11054799408291754651567255 16582199112437631977350883)
                  ·
                    refine ⟨24873298668656447966026325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16582199112437631977350883 24873298668656447966026325)
                    ·
                      refine ⟨291483968773317749601871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 24873298668656447966026325 291483968773317749601871)
                      ·
                        rfl

theorem cell23_567663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_567663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567663 prefixEnd_567663 := by exact prefixLift 567663
  have htrace : WordTrace (prefixWord ++ tailWord_567663) baseStart_567663 baseEnd_567663 := by
    simpa [prefixWord, tailWord_567663, baseEnd_567663] using wordTrace_append hprefix tailTrace_567663
  have hstable : (prefixWord ++ tailWord_567663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567663).length < 2 ^ (prefixWord ++ tailWord_567663).sum := by decide
  have hdescent : baseEnd_567663 < baseStart_567663 := by decide
  rcases family_descends (prefixWord ++ tailWord_567663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567664 : List Nat := [2, 1, 1, 1, 4, 3, 3, 3, 1, 4]
def baseStart_567664 : Nat := 118140960795 + 567664 * 2 ^ 59
def prefixEnd_567664 : Nat := 4983230072969 + 3 ^ 40 * 567664 * 2
def baseEnd_567664 : Nat := 97161494084657415229789

theorem tailTrace_567664 : CollatzResearch.WordTrace tailWord_567664 prefixEnd_567664 97161494084657415229789 := by
  unfold tailWord_567664
  simp only [CollatzResearch.WordTrace]
  refine ⟨10352203507728876068891023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13802938010305168091854697 10352203507728876068891023)
  ·
    refine ⟨15528305261593314103336535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10352203507728876068891023 15528305261593314103336535)
    ·
      refine ⟨23292457892389971155004803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15528305261593314103336535 23292457892389971155004803)
      ·
        refine ⟨34938686838584956732507205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23292457892389971155004803 34938686838584956732507205)
        ·
          refine ⟨6551003782234679387345101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34938686838584956732507205 6551003782234679387345101)
          ·
            refine ⟨2456626418338004770254413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6551003782234679387345101 2456626418338004770254413)
            ·
              refine ⟨921234906876751788845405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2456626418338004770254413 921234906876751788845405)
              ·
                refine ⟨345463090078781920817027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 921234906876751788845405 345463090078781920817027)
                ·
                  refine ⟨518194635118172881225541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345463090078781920817027 518194635118172881225541)
                  ·
                    refine ⟨97161494084657415229789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 518194635118172881225541 97161494084657415229789)
                    ·
                      rfl

theorem cell23_567664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 4].length) (baseStart_567664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567664 prefixEnd_567664 := by exact prefixLift 567664
  have htrace : WordTrace (prefixWord ++ tailWord_567664) baseStart_567664 baseEnd_567664 := by
    simpa [prefixWord, tailWord_567664, baseEnd_567664] using wordTrace_append hprefix tailTrace_567664
  have hstable : (prefixWord ++ tailWord_567664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567664).length < 2 ^ (prefixWord ++ tailWord_567664).sum := by decide
  have hdescent : baseEnd_567664 < baseStart_567664 := by decide
  rcases family_descends (prefixWord ++ tailWord_567664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567694 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_567694 : Nat := 118140960795 + 567694 * 2 ^ 59
def prefixEnd_567694 : Nat := 4983230072969 + 3 ^ 40 * 567694 * 2
def baseEnd_567694 : Nat := 32388876297067458701581

theorem tailTrace_567694 : CollatzResearch.WordTrace tailWord_567694 prefixEnd_567694 32388876297067458701581 := by
  unfold tailWord_567694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2588187650668633407671767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13803667470232711507582757 2588187650668633407671767)
  ·
    refine ⟨3882281476002950111507651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2588187650668633407671767 3882281476002950111507651)
    ·
      refine ⟨5823422214004425167261477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3882281476002950111507651 5823422214004425167261477)
      ·
        refine ⟨1091891665125829718861527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5823422214004425167261477 1091891665125829718861527)
        ·
          refine ⟨1637837497688744578292291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091891665125829718861527 1637837497688744578292291)
          ·
            refine ⟨2456756246533116867438437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637837497688744578292291 2456756246533116867438437)
            ·
              refine ⟨460641796224959412644707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2456756246533116867438437 460641796224959412644707)
              ·
                refine ⟨690962694337439118967061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460641796224959412644707 690962694337439118967061)
                ·
                  refine ⟨32388876297067458701581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 690962694337439118967061 32388876297067458701581)
                  ·
                    rfl

theorem cell23_567694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_567694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567694 prefixEnd_567694 := by exact prefixLift 567694
  have htrace : WordTrace (prefixWord ++ tailWord_567694) baseStart_567694 baseEnd_567694 := by
    simpa [prefixWord, tailWord_567694, baseEnd_567694] using wordTrace_append hprefix tailTrace_567694
  have hstable : (prefixWord ++ tailWord_567694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567694).length < 2 ^ (prefixWord ++ tailWord_567694).sum := by decide
  have hdescent : baseEnd_567694 < baseStart_567694 := by decide
  rcases family_descends (prefixWord ++ tailWord_567694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567732 : List Nat := [2, 5, 2, 2, 1, 2, 2, 2, 1, 4]
def baseStart_567732 : Nat := 118140960795 + 567732 * 2 ^ 59
def prefixEnd_567732 : Nat := 4983230072969 + 3 ^ 40 * 567732 * 2
def baseEnd_567732 : Nat := 97173132979492659879685

theorem tailTrace_567732 : CollatzResearch.WordTrace tailWord_567732 prefixEnd_567732 97173132979492659879685 := by
  unfold tailWord_567732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10353443589605699875628725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13804591452807599834171633 10353443589605699875628725)
  ·
    refine ⟨970635336525534363340193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10353443589605699875628725 970635336525534363340193)
    ·
      refine ⟨727976502394150772505145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 970635336525534363340193 727976502394150772505145)
      ·
        refine ⟨545982376795613079378859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 727976502394150772505145 545982376795613079378859)
        ·
          refine ⟨818973565193419619068289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545982376795613079378859 818973565193419619068289)
          ·
            refine ⟨614230173895064714301217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 818973565193419619068289 614230173895064714301217)
            ·
              refine ⟨460672630421298535725913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614230173895064714301217 460672630421298535725913)
              ·
                refine ⟨345504472815973901794435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460672630421298535725913 345504472815973901794435)
                ·
                  refine ⟨518256709223960852691653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345504472815973901794435 518256709223960852691653)
                  ·
                    refine ⟨97173132979492659879685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 518256709223960852691653 97173132979492659879685)
                    ·
                      rfl

theorem cell23_567732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_567732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567732 prefixEnd_567732 := by exact prefixLift 567732
  have htrace : WordTrace (prefixWord ++ tailWord_567732) baseStart_567732 baseEnd_567732 := by
    simpa [prefixWord, tailWord_567732, baseEnd_567732] using wordTrace_append hprefix tailTrace_567732
  have hstable : (prefixWord ++ tailWord_567732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567732).length < 2 ^ (prefixWord ++ tailWord_567732).sum := by decide
  have hdescent : baseEnd_567732 < baseStart_567732 := by decide
  rcases family_descends (prefixWord ++ tailWord_567732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567744 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 3, 2, 2]
def baseStart_567744 : Nat := 118140960795 + 567744 * 2 ^ 59
def prefixEnd_567744 : Nat := 4983230072969 + 3 ^ 40 * 567744 * 2
def baseEnd_567744 : Nat := 291525560706331932688999

theorem tailTrace_567744 : CollatzResearch.WordTrace tailWord_567744 prefixEnd_567744 291525560706331932688999 := by
  unfold tailWord_567744
  simp only [CollatzResearch.WordTrace]
  refine ⟨10353662427583962900347143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13804883236778617200462857 10353662427583962900347143)
  ·
    refine ⟨15530493641375944350520715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10353662427583962900347143 15530493641375944350520715)
    ·
      refine ⟨23295740462063916525781073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15530493641375944350520715 23295740462063916525781073)
      ·
        refine ⟨17471805346547937394335805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23295740462063916525781073 17471805346547937394335805)
        ·
          refine ⟨6551927004955476522875927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17471805346547937394335805 6551927004955476522875927)
          ·
            refine ⟨9827890507433214784313891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6551927004955476522875927 9827890507433214784313891)
            ·
              refine ⟨14741835761149822176470837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9827890507433214784313891 14741835761149822176470837)
              ·
                refine ⟨1382047102607795829044141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14741835761149822176470837 1382047102607795829044141)
                ·
                  refine ⟨518267663477923435891553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1382047102607795829044141 518267663477923435891553)
                  ·
                    refine ⟨388700747608442576918665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 518267663477923435891553 388700747608442576918665)
                    ·
                      refine ⟨291525560706331932688999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388700747608442576918665 291525560706331932688999)
                      ·
                        rfl

theorem cell23_567744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 2, 2].length) (baseStart_567744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567744 prefixEnd_567744 := by exact prefixLift 567744
  have htrace : WordTrace (prefixWord ++ tailWord_567744) baseStart_567744 baseEnd_567744 := by
    simpa [prefixWord, tailWord_567744, baseEnd_567744] using wordTrace_append hprefix tailTrace_567744
  have hstable : (prefixWord ++ tailWord_567744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567744).length < 2 ^ (prefixWord ++ tailWord_567744).sum := by decide
  have hdescent : baseEnd_567744 < baseStart_567744 := by decide
  rcases family_descends (prefixWord ++ tailWord_567744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567764 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_567764 : Nat := 118140960795 + 567764 * 2 ^ 59
def prefixEnd_567764 : Nat := 4983230072969 + 3 ^ 40 * 567764 * 2
def baseEnd_567764 : Nat := 291535830319421854438907

theorem tailTrace_567764 : CollatzResearch.WordTrace tailWord_567764 prefixEnd_567764 291535830319421854438907 := by
  unfold tailWord_567764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10354027157547734608211173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13805369543396979477614897 10354027157547734608211173)
  ·
    refine ⟨1941380092040200239039595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10354027157547734608211173 1941380092040200239039595)
    ·
      refine ⟨2912070138060300358559393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1941380092040200239039595 2912070138060300358559393)
      ·
        refine ⟨2184052603545225268919545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2912070138060300358559393 2184052603545225268919545)
        ·
          refine ⟨1638039452658918951689659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2184052603545225268919545 1638039452658918951689659)
          ·
            refine ⟨2457059178988378427534489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638039452658918951689659 2457059178988378427534489)
            ·
              refine ⟨1842794384241283820650867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2457059178988378427534489 1842794384241283820650867)
              ·
                refine ⟨2764191576361925730976301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842794384241283820650867 2764191576361925730976301)
                ·
                  refine ⟨1036571841135722149116113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2764191576361925730976301 1036571841135722149116113)
                  ·
                    refine ⟨777428880851791611837085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1036571841135722149116113 777428880851791611837085)
                    ·
                      refine ⟨291535830319421854438907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 777428880851791611837085 291535830319421854438907)
                      ·
                        rfl

theorem cell23_567764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_567764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567764 prefixEnd_567764 := by exact prefixLift 567764
  have htrace : WordTrace (prefixWord ++ tailWord_567764) baseStart_567764 baseEnd_567764 := by
    simpa [prefixWord, tailWord_567764, baseEnd_567764] using wordTrace_append hprefix tailTrace_567764
  have hstable : (prefixWord ++ tailWord_567764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567764).length < 2 ^ (prefixWord ++ tailWord_567764).sum := by decide
  have hdescent : baseEnd_567764 < baseStart_567764 := by decide
  rcases family_descends (prefixWord ++ tailWord_567764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567777 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 3]
def baseStart_567777 : Nat := 118140960795 + 567777 * 2 ^ 59
def prefixEnd_567777 : Nat := 4983230072969 + 3 ^ 40 * 567777 * 2
def baseEnd_567777 : Nat := 291542505567930303576347

theorem tailTrace_567777 : CollatzResearch.WordTrace tailWord_567777 prefixEnd_567777 291542505567930303576347 := by
  unfold tailWord_567777
  simp only [CollatzResearch.WordTrace]
  refine ⟨20708528464048372436645585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13805685642698914957763723 20708528464048372436645585)
  ·
    refine ⟨15531396348036279327484189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20708528464048372436645585 15531396348036279327484189)
    ·
      refine ⟨5824273630513604747806571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15531396348036279327484189 5824273630513604747806571)
      ·
        refine ⟨8736410445770407121709857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824273630513604747806571 8736410445770407121709857)
        ·
          refine ⟨6552307834327805341282393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8736410445770407121709857 6552307834327805341282393)
          ·
            refine ⟨4914230875745854005961795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6552307834327805341282393 4914230875745854005961795)
            ·
              refine ⟨7371346313618781008942693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914230875745854005961795 7371346313618781008942693)
              ·
                refine ⟨1382127433803521439176755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7371346313618781008942693 1382127433803521439176755)
                ·
                  refine ⟨2073191150705282158765133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382127433803521439176755 2073191150705282158765133)
                  ·
                    refine ⟨777446681514480809536925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2073191150705282158765133 777446681514480809536925)
                    ·
                      refine ⟨291542505567930303576347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 777446681514480809536925 291542505567930303576347)
                      ·
                        rfl

theorem cell23_567777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_567777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567777 prefixEnd_567777 := by exact prefixLift 567777
  have htrace : WordTrace (prefixWord ++ tailWord_567777) baseStart_567777 baseEnd_567777 := by
    simpa [prefixWord, tailWord_567777, baseEnd_567777] using wordTrace_append hprefix tailTrace_567777
  have hstable : (prefixWord ++ tailWord_567777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567777).length < 2 ^ (prefixWord ++ tailWord_567777).sum := by decide
  have hdescent : baseEnd_567777 < baseStart_567777 := by decide
  rcases family_descends (prefixWord ++ tailWord_567777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567778 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_567778 : Nat := 118140960795 + 567778 * 2 ^ 59
def prefixEnd_567778 : Nat := 4983230072969 + 3 ^ 40 * 567778 * 2
def baseEnd_567778 : Nat := 291543019048584799663843

theorem tailTrace_567778 : CollatzResearch.WordTrace tailWord_567778 prefixEnd_567778 291543019048584799663843 := by
  unfold tailWord_567778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5177141234261187401857997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13805709958029833071621325 5177141234261187401857997)
  ·
    refine ⟨1941427962847945275696749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5177141234261187401857997 1941427962847945275696749)
    ·
      refine ⟨728035486067979478386281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1941427962847945275696749 728035486067979478386281)
      ·
        refine ⟨546026614550984608789711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728035486067979478386281 546026614550984608789711)
        ·
          refine ⟨819039921826476913184567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546026614550984608789711 819039921826476913184567)
          ·
            refine ⟨1228559882739715369776851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819039921826476913184567 1228559882739715369776851)
            ·
              refine ⟨1842839824109573054665277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228559882739715369776851 1842839824109573054665277)
              ·
                refine ⟨691064934041089895499479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1842839824109573054665277 691064934041089895499479)
                ·
                  refine ⟨1036597401061634843249219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691064934041089895499479 1036597401061634843249219)
                  ·
                    refine ⟨1554896101592452264873829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1036597401061634843249219 1554896101592452264873829)
                    ·
                      refine ⟨291543019048584799663843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1554896101592452264873829 291543019048584799663843)
                      ·
                        rfl

theorem cell23_567778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_567778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567778 prefixEnd_567778 := by exact prefixLift 567778
  have htrace : WordTrace (prefixWord ++ tailWord_567778) baseStart_567778 baseEnd_567778 := by
    simpa [prefixWord, tailWord_567778, baseEnd_567778] using wordTrace_append hprefix tailTrace_567778
  have hstable : (prefixWord ++ tailWord_567778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567778).length < 2 ^ (prefixWord ++ tailWord_567778).sum := by decide
  have hdescent : baseEnd_567778 < baseStart_567778 := by decide
  rcases family_descends (prefixWord ++ tailWord_567778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567781 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 3]
def baseStart_567781 : Nat := 118140960795 + 567781 * 2 ^ 59
def prefixEnd_567781 : Nat := 4983230072969 + 3 ^ 40 * 567781 * 2
def baseEnd_567781 : Nat := 291544559490548287926329

theorem tailTrace_567781 : CollatzResearch.WordTrace tailWord_567781 prefixEnd_567781 291544559490548287926329 := by
  unfold tailWord_567781
  simp only [CollatzResearch.WordTrace]
  refine ⟨20708674356033881119791197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13805782904022587413194131 20708674356033881119791197)
  ·
    refine ⟨7765752883512705419921699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20708674356033881119791197 7765752883512705419921699)
    ·
      refine ⟨11648629325269058129882549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7765752883512705419921699 11648629325269058129882549)
      ·
        refine ⟨1092058999243974199676489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11648629325269058129882549 1092058999243974199676489)
        ·
          refine ⟨819044249432980649757367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1092058999243974199676489 819044249432980649757367)
          ·
            refine ⟨1228566374149470974636051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819044249432980649757367 1228566374149470974636051)
            ·
              refine ⟨1842849561224206461954077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228566374149470974636051 1842849561224206461954077)
              ·
                refine ⟨691068585459077423232779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1842849561224206461954077 691068585459077423232779)
                ·
                  refine ⟨1036602878188616134849169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691068585459077423232779 1036602878188616134849169)
                  ·
                    refine ⟨777452158641462101136877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1036602878188616134849169 777452158641462101136877)
                    ·
                      refine ⟨291544559490548287926329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 777452158641462101136877 291544559490548287926329)
                      ·
                        rfl

theorem cell23_567781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_567781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567781 prefixEnd_567781 := by exact prefixLift 567781
  have htrace : WordTrace (prefixWord ++ tailWord_567781) baseStart_567781 baseEnd_567781 := by
    simpa [prefixWord, tailWord_567781, baseEnd_567781] using wordTrace_append hprefix tailTrace_567781
  have hstable : (prefixWord ++ tailWord_567781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567781).length < 2 ^ (prefixWord ++ tailWord_567781).sum := by decide
  have hdescent : baseEnd_567781 < baseStart_567781 := by decide
  rcases family_descends (prefixWord ++ tailWord_567781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567811 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 2, 1, 3]
def baseStart_567811 : Nat := 118140960795 + 567811 * 2 ^ 59
def prefixEnd_567811 : Nat := 4983230072969 + 3 ^ 40 * 567811 * 2
def baseEnd_567811 : Nat := 291559963910183170551191

theorem tailTrace_567811 : CollatzResearch.WordTrace tailWord_567811 prefixEnd_567811 291559963910183170551191 := by
  unfold tailWord_567811
  simp only [CollatzResearch.WordTrace]
  refine ⟨20709768545925196243383287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13806512363950130828922191 20709768545925196243383287)
  ·
    refine ⟨31064652818887794365074931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20709768545925196243383287 31064652818887794365074931)
    ·
      refine ⟨46596979228331691547612397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31064652818887794365074931 46596979228331691547612397)
      ·
        refine ⟨17473867210624384330354649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46596979228331691547612397 17473867210624384330354649)
        ·
          refine ⟨13105400407968288247765987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17473867210624384330354649 13105400407968288247765987)
          ·
            refine ⟨19658100611952432371648981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13105400407968288247765987 19658100611952432371648981)
            ·
              refine ⟨460736733092635133710523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19658100611952432371648981 460736733092635133710523)
              ·
                refine ⟨691105099638952700565785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460736733092635133710523 691105099638952700565785)
                ·
                  refine ⟨518328824729214525424339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 691105099638952700565785 518328824729214525424339)
                  ·
                    refine ⟨777493237093821788136509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 518328824729214525424339 777493237093821788136509)
                    ·
                      refine ⟨291559963910183170551191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 777493237093821788136509 291559963910183170551191)
                      ·
                        rfl

theorem cell23_567811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_567811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567811 prefixEnd_567811 := by exact prefixLift 567811
  have htrace : WordTrace (prefixWord ++ tailWord_567811) baseStart_567811 baseEnd_567811 := by
    simpa [prefixWord, tailWord_567811, baseEnd_567811] using wordTrace_append hprefix tailTrace_567811
  have hstable : (prefixWord ++ tailWord_567811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567811).length < 2 ^ (prefixWord ++ tailWord_567811).sum := by decide
  have hdescent : baseEnd_567811 < baseStart_567811 := by decide
  rcases family_descends (prefixWord ++ tailWord_567811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567834 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2]
def baseStart_567834 : Nat := 118140960795 + 567834 * 2 ^ 59
def prefixEnd_567834 : Nat := 4983230072969 + 3 ^ 40 * 567834 * 2
def baseEnd_567834 : Nat := 291571773965236580563585

theorem tailTrace_567834 : CollatzResearch.WordTrace tailWord_567834 prefixEnd_567834 291571773965236580563585 := by
  unfold tailWord_567834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5177651856210467792867639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13807071616561247447647037 5177651856210467792867639)
  ·
    refine ⟨7766477784315701689301459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5177651856210467792867639 7766477784315701689301459)
    ·
      refine ⟨11649716676473552533952189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7766477784315701689301459 11649716676473552533952189)
      ·
        refine ⟨4368643753677582200232071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11649716676473552533952189 4368643753677582200232071)
        ·
          refine ⟨6552965630516373300348107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368643753677582200232071 6552965630516373300348107)
          ·
            refine ⟨9829448445774559950522161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6552965630516373300348107 9829448445774559950522161)
            ·
              refine ⟨7372086334330919962891621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9829448445774559950522161 7372086334330919962891621)
              ·
                refine ⟨1382266187687047493042179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7372086334330919962891621 1382266187687047493042179)
                ·
                  refine ⟨2073399281530571239563269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382266187687047493042179 2073399281530571239563269)
                  ·
                    refine ⟨388762365286982107418113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2073399281530571239563269 388762365286982107418113)
                    ·
                      refine ⟨291571773965236580563585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388762365286982107418113 291571773965236580563585)
                      ·
                        rfl

theorem cell23_567834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_567834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567834 prefixEnd_567834 := by exact prefixLift 567834
  have htrace : WordTrace (prefixWord ++ tailWord_567834) baseStart_567834 baseEnd_567834 := by
    simpa [prefixWord, tailWord_567834, baseEnd_567834] using wordTrace_append hprefix tailTrace_567834
  have hstable : (prefixWord ++ tailWord_567834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567834).length < 2 ^ (prefixWord ++ tailWord_567834).sum := by decide
  have hdescent : baseEnd_567834 < baseStart_567834 := by decide
  rcases family_descends (prefixWord ++ tailWord_567834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567837 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_567837 : Nat := 118140960795 + 567837 * 2 ^ 59
def prefixEnd_567837 : Nat := 4983230072969 + 3 ^ 40 * 567837 * 2
def baseEnd_567837 : Nat := 291573314407200068826071

theorem tailTrace_567837 : CollatzResearch.WordTrace tailWord_567837 prefixEnd_567837 291573314407200068826071 := by
  unfold tailWord_567837
  simp only [CollatzResearch.WordTrace]
  refine ⟨20710716843831002683829765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13807144562554001789219843 20710716843831002683829765)
  ·
    refine ⟨3883259408218313003218081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20710716843831002683829765 3883259408218313003218081)
    ·
      refine ⟨2912444556163734752413561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3883259408218313003218081 2912444556163734752413561)
      ·
        refine ⟨2184333417122801064310171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2912444556163734752413561 2184333417122801064310171)
        ·
          refine ⟨3276500125684201596465257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184333417122801064310171 3276500125684201596465257)
          ·
            refine ⟨2457375094263151197348943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3276500125684201596465257 2457375094263151197348943)
            ·
              refine ⟨3686062641394726796023415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457375094263151197348943 3686062641394726796023415)
              ·
                refine ⟨5529093962092090194035123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686062641394726796023415 5529093962092090194035123)
                ·
                  refine ⟨8293640943138135291052685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5529093962092090194035123 8293640943138135291052685)
                  ·
                    refine ⟨3110115353676800734144757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8293640943138135291052685 3110115353676800734144757)
                    ·
                      refine ⟨291573314407200068826071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3110115353676800734144757 291573314407200068826071)
                      ·
                        rfl

theorem cell23_567837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_567837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567837 prefixEnd_567837 := by exact prefixLift 567837
  have htrace : WordTrace (prefixWord ++ tailWord_567837) baseStart_567837 baseEnd_567837 := by
    simpa [prefixWord, tailWord_567837, baseEnd_567837] using wordTrace_append hprefix tailTrace_567837
  have hstable : (prefixWord ++ tailWord_567837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567837).length < 2 ^ (prefixWord ++ tailWord_567837).sum := by decide
  have hdescent : baseEnd_567837 < baseStart_567837 := by decide
  rcases family_descends (prefixWord ++ tailWord_567837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567857 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 7]
def baseStart_567857 : Nat := 118140960795 + 567857 * 2 ^ 59
def prefixEnd_567857 : Nat := 4983230072969 + 3 ^ 40 * 567857 * 2
def baseEnd_567857 : Nat := 32398176002254443397331

theorem tailTrace_567857 : CollatzResearch.WordTrace tailWord_567857 prefixEnd_567857 32398176002254443397331 := by
  unfold tailWord_567857
  simp only [CollatzResearch.WordTrace]
  refine ⟨20711446303758546099557825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13807630869172364066371883 20711446303758546099557825)
  ·
    refine ⟨15533584727818909574668369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20711446303758546099557825 15533584727818909574668369)
    ·
      refine ⟨11650188545864182181001277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15533584727818909574668369 11650188545864182181001277)
      ·
        refine ⟨4368820704699068317875479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11650188545864182181001277 4368820704699068317875479)
        ·
          refine ⟨6553231057048602476813219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368820704699068317875479 6553231057048602476813219)
          ·
            refine ⟨9829846585572903715219829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6553231057048602476813219 9829846585572903715219829)
            ·
              refine ⟨921548117397459723301859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9829846585572903715219829 921548117397459723301859)
              ·
                refine ⟨1382322176096189584952789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921548117397459723301859 1382322176096189584952789)
                ·
                  refine ⟨32398176002254443397331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1382322176096189584952789 32398176002254443397331)
                  ·
                    rfl

theorem cell23_567857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 7].length) (baseStart_567857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567857 prefixEnd_567857 := by exact prefixLift 567857
  have htrace : WordTrace (prefixWord ++ tailWord_567857) baseStart_567857 baseEnd_567857 := by
    simpa [prefixWord, tailWord_567857, baseEnd_567857] using wordTrace_append hprefix tailTrace_567857
  have hstable : (prefixWord ++ tailWord_567857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567857).length < 2 ^ (prefixWord ++ tailWord_567857).sum := by decide
  have hdescent : baseEnd_567857 < baseStart_567857 := by decide
  rcases family_descends (prefixWord ++ tailWord_567857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567868 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_567868 : Nat := 118140960795 + 567868 * 2 ^ 59
def prefixEnd_567868 : Nat := 4983230072969 + 3 ^ 40 * 567868 * 2
def baseEnd_567868 : Nat := 291589232307489447538429

theorem tailTrace_567868 : CollatzResearch.WordTrace tailWord_567868 prefixEnd_567868 291589232307489447538429 := by
  unfold tailWord_567868
  simp only [CollatzResearch.WordTrace]
  refine ⟨10355923753359347489104129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13807898337812463318805505 10355923753359347489104129)
  ·
    refine ⟨7766942815019510616828097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10355923753359347489104129 7766942815019510616828097)
    ·
      refine ⟨5825207111264632962621073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7766942815019510616828097 5825207111264632962621073)
      ·
        refine ⟨4368905333448474721965805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5825207111264632962621073 4368905333448474721965805)
        ·
          refine ⟨1638339500043178020737177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4368905333448474721965805 1638339500043178020737177)
          ·
            refine ⟨1228754625032383515552883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1638339500043178020737177 1228754625032383515552883)
            ·
              refine ⟨1843131937548575273329325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228754625032383515552883 1843131937548575273329325)
              ·
                refine ⟨691174476580715727498497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1843131937548575273329325 691174476580715727498497)
                ·
                  refine ⟨518380857435536795623873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 691174476580715727498497 518380857435536795623873)
                  ·
                    refine ⟨388785643076652596717905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 518380857435536795623873 388785643076652596717905)
                    ·
                      refine ⟨291589232307489447538429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388785643076652596717905 291589232307489447538429)
                      ·
                        rfl

theorem cell23_567868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_567868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567868 prefixEnd_567868 := by exact prefixLift 567868
  have htrace : WordTrace (prefixWord ++ tailWord_567868) baseStart_567868 baseEnd_567868 := by
    simpa [prefixWord, tailWord_567868, baseEnd_567868] using wordTrace_append hprefix tailTrace_567868
  have hstable : (prefixWord ++ tailWord_567868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567868).length < 2 ^ (prefixWord ++ tailWord_567868).sum := by decide
  have hdescent : baseEnd_567868 < baseStart_567868 := by decide
  rcases family_descends (prefixWord ++ tailWord_567868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567887 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 2, 5]
def baseStart_567887 : Nat := 118140960795 + 567887 * 2 ^ 59
def prefixEnd_567887 : Nat := 4983230072969 + 3 ^ 40 * 567887 * 2
def baseEnd_567887 : Nat := 97199662813308291066947

theorem tailTrace_567887 : CollatzResearch.WordTrace tailWord_567887 prefixEnd_567887 97199662813308291066947 := by
  unfold tailWord_567887
  simp only [CollatzResearch.WordTrace]
  refine ⟨20712540493649861223149915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13808360329099907482099943 20712540493649861223149915)
  ·
    refine ⟨31068810740474791834724873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20712540493649861223149915 31068810740474791834724873)
    ·
      refine ⟨23301608055356093876043655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31068810740474791834724873 23301608055356093876043655)
      ·
        refine ⟨34952412083034140814065483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23301608055356093876043655 34952412083034140814065483)
        ·
          refine ⟨52428618124551211221098225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34952412083034140814065483 52428618124551211221098225)
          ·
            refine ⟨39321463593413408415823669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52428618124551211221098225 39321463593413408415823669)
            ·
              refine ⟨3686387211882507038983469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39321463593413408415823669 3686387211882507038983469)
              ·
                refine ⟨1382395204455940139618801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3686387211882507038983469 1382395204455940139618801)
                ·
                  refine ⟨1036796403341955104714101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1382395204455940139618801 1036796403341955104714101)
                  ·
                    refine ⟨97199662813308291066947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1036796403341955104714101 97199662813308291066947)
                    ·
                      rfl

theorem cell23_567887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_567887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567887 prefixEnd_567887 := by exact prefixLift 567887
  have htrace : WordTrace (prefixWord ++ tailWord_567887) baseStart_567887 baseEnd_567887 := by
    simpa [prefixWord, tailWord_567887, baseEnd_567887] using wordTrace_append hprefix tailTrace_567887
  have hstable : (prefixWord ++ tailWord_567887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567887).length < 2 ^ (prefixWord ++ tailWord_567887).sum := by decide
  have hdescent : baseEnd_567887 < baseStart_567887 := by decide
  rcases family_descends (prefixWord ++ tailWord_567887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567941 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 4]
def baseStart_567941 : Nat := 118140960795 + 567941 * 2 ^ 59
def prefixEnd_567941 : Nat := 4983230072969 + 3 ^ 40 * 567941 * 2
def baseEnd_567941 : Nat := 291626716395267661925593

theorem tailTrace_567941 : CollatzResearch.WordTrace tailWord_567941 prefixEnd_567941 291626716395267661925593 := by
  unfold tailWord_567941
  simp only [CollatzResearch.WordTrace]
  refine ⟨20714510035454228445615677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13809673356969485630410451 20714510035454228445615677)
  ·
    refine ⟨7767941263295335667105879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20714510035454228445615677 7767941263295335667105879)
    ·
      refine ⟨11651911894943003500658819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7767941263295335667105879 11651911894943003500658819)
      ·
        refine ⟨17477867842414505250988229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11651911894943003500658819 17477867842414505250988229)
        ·
          refine ⟨3277100220452719734560293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17477867842414505250988229 3277100220452719734560293)
          ·
            refine ⟨614456291334884950230055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3277100220452719734560293 614456291334884950230055)
            ·
              refine ⟨921684437002327425345083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614456291334884950230055 921684437002327425345083)
              ·
                refine ⟨1382526655503491138017625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921684437002327425345083 1382526655503491138017625)
                ·
                  refine ⟨1036894991627618353513219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1382526655503491138017625 1036894991627618353513219)
                  ·
                    refine ⟨1555342487441427530269829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1036894991627618353513219 1555342487441427530269829)
                    ·
                      refine ⟨291626716395267661925593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1555342487441427530269829 291626716395267661925593)
                      ·
                        rfl

theorem cell23_567941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_567941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567941 prefixEnd_567941 := by exact prefixLift 567941
  have htrace : WordTrace (prefixWord ++ tailWord_567941) baseStart_567941 baseEnd_567941 := by
    simpa [prefixWord, tailWord_567941, baseEnd_567941] using wordTrace_append hprefix tailTrace_567941
  have hstable : (prefixWord ++ tailWord_567941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567941).length < 2 ^ (prefixWord ++ tailWord_567941).sum := by decide
  have hdescent : baseEnd_567941 < baseStart_567941 := by decide
  rcases family_descends (prefixWord ++ tailWord_567941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567954 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_567954 : Nat := 118140960795 + 567954 * 2 ^ 59
def prefixEnd_567954 : Nat := 4983230072969 + 3 ^ 40 * 567954 * 2
def baseEnd_567954 : Nat := 291633391643776111063033

theorem tailTrace_567954 : CollatzResearch.WordTrace tailWord_567954 prefixEnd_567954 291633391643776111063033 := by
  unfold tailWord_567954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178746046101782916459729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13809989456271421110559277 5178746046101782916459729)
  ·
    refine ⟨3884059534576337187344797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5178746046101782916459729 3884059534576337187344797)
    ·
      refine ⟨1456522325466126445254299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3884059534576337187344797 1456522325466126445254299)
      ·
        refine ⟨2184783488199189667881449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1456522325466126445254299 2184783488199189667881449)
        ·
          refine ⟨1638587616149392250911087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2184783488199189667881449 1638587616149392250911087)
          ·
            refine ⟨2457881424224088376366631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638587616149392250911087 2457881424224088376366631)
            ·
              refine ⟨3686822136336132564549947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457881424224088376366631 3686822136336132564549947)
              ·
                refine ⟨5530233204504198846824921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686822136336132564549947 5530233204504198846824921)
                ·
                  refine ⟨4147674903378149135118691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5530233204504198846824921 4147674903378149135118691)
                  ·
                    refine ⟨6221512355067223702678037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4147674903378149135118691 6221512355067223702678037)
                    ·
                      refine ⟨291633391643776111063033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6221512355067223702678037 291633391643776111063033)
                      ·
                        rfl

theorem cell23_567954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_567954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567954 prefixEnd_567954 := by exact prefixLift 567954
  have htrace : WordTrace (prefixWord ++ tailWord_567954) baseStart_567954 baseEnd_567954 := by
    simpa [prefixWord, tailWord_567954, baseEnd_567954] using wordTrace_append hprefix tailTrace_567954
  have hstable : (prefixWord ++ tailWord_567954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567954).length < 2 ^ (prefixWord ++ tailWord_567954).sum := by decide
  have hdescent : baseEnd_567954 < baseStart_567954 := by decide
  rcases family_descends (prefixWord ++ tailWord_567954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_567964 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 8]
def baseStart_567964 : Nat := 118140960795 + 567964 * 2 ^ 59
def prefixEnd_567964 : Nat := 4983230072969 + 3 ^ 40 * 567964 * 2
def baseEnd_567964 : Nat := 32404280716702341326443

theorem tailTrace_567964 : CollatzResearch.WordTrace tailWord_567964 prefixEnd_567964 32404280716702341326443 := by
  unfold tailWord_567964
  simp only [CollatzResearch.WordTrace]
  refine ⟨10357674457185451686851473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13810232609580602249135297 10357674457185451686851473)
  ·
    refine ⟨7768255842889088765138605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10357674457185451686851473 7768255842889088765138605)
    ·
      refine ⟨2913095941083408286926977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7768255842889088765138605 2913095941083408286926977)
      ·
        refine ⟨2184821955812556215195233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2913095941083408286926977 2184821955812556215195233)
        ·
          refine ⟨1638616466859417161396425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2184821955812556215195233 1638616466859417161396425)
          ·
            refine ⟨1228962350144562871047319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1638616466859417161396425 1228962350144562871047319)
            ·
              refine ⟨1843443525216844306570979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228962350144562871047319 1843443525216844306570979)
              ·
                refine ⟨2765165287825266459856469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843443525216844306570979 2765165287825266459856469)
                ·
                  refine ⟨32404280716702341326443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2765165287825266459856469 32404280716702341326443)
                  ·
                    rfl

theorem cell23_567964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_567964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_567964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_567964 prefixEnd_567964 := by exact prefixLift 567964
  have htrace : WordTrace (prefixWord ++ tailWord_567964) baseStart_567964 baseEnd_567964 := by
    simpa [prefixWord, tailWord_567964, baseEnd_567964] using wordTrace_append hprefix tailTrace_567964
  have hstable : (prefixWord ++ tailWord_567964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_567964).length < 2 ^ (prefixWord ++ tailWord_567964).sum := by decide
  have hdescent : baseEnd_567964 < baseStart_567964 := by decide
  rcases family_descends (prefixWord ++ tailWord_567964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568025 : List Nat := [1, 2, 1, 2, 3, 2, 5, 2, 1, 1, 3]
def baseStart_568025 : Nat := 118140960795 + 568025 * 2 ^ 59
def prefixEnd_568025 : Nat := 4983230072969 + 3 ^ 40 * 568025 * 2
def baseEnd_568025 : Nat := 291669848770245333275207

theorem tailTrace_568025 : CollatzResearch.WordTrace tailWord_568025 prefixEnd_568025 291669848770245333275207 := by
  unfold tailWord_568025
  simp only [CollatzResearch.WordTrace]
  refine ⟨20717573767149910791673529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13811715844766607194449019 20717573767149910791673529)
  ·
    refine ⟨15538180325362433093755147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20717573767149910791673529 15538180325362433093755147)
    ·
      refine ⟨23307270488043649640632721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15538180325362433093755147 23307270488043649640632721)
      ·
        refine ⟨17480452866032737230474541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23307270488043649640632721 17480452866032737230474541)
        ·
          refine ⟨6555169824762276461427953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17480452866032737230474541 6555169824762276461427953)
          ·
            refine ⟨4916377368571707346070965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6555169824762276461427953 4916377368571707346070965)
            ·
              refine ⟨460910378303597563694153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4916377368571707346070965 460910378303597563694153)
              ·
                refine ⟨345682783727698172770615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460910378303597563694153 345682783727698172770615)
                ·
                  refine ⟨518524175591547259155923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345682783727698172770615 518524175591547259155923)
                  ·
                    refine ⟨777786263387320888733885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 518524175591547259155923 777786263387320888733885)
                    ·
                      refine ⟨291669848770245333275207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 777786263387320888733885 291669848770245333275207)
                      ·
                        rfl

theorem cell23_568025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 1, 1, 3].length) (baseStart_568025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568025 prefixEnd_568025 := by exact prefixLift 568025
  have htrace : WordTrace (prefixWord ++ tailWord_568025) baseStart_568025 baseEnd_568025 := by
    simpa [prefixWord, tailWord_568025, baseEnd_568025] using wordTrace_append hprefix tailTrace_568025
  have hstable : (prefixWord ++ tailWord_568025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568025).length < 2 ^ (prefixWord ++ tailWord_568025).sum := by decide
  have hdescent : baseEnd_568025 < baseStart_568025 := by decide
  rcases family_descends (prefixWord ++ tailWord_568025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568044 : List Nat := [2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_568044 : Nat := 118140960795 + 568044 * 2 ^ 59
def prefixEnd_568044 : Nat := 4983230072969 + 3 ^ 40 * 568044 * 2
def baseEnd_568044 : Nat := 291679604902680758937619

theorem tailTrace_568044 : CollatzResearch.WordTrace tailWord_568044 prefixEnd_568044 291679604902680758937619 := by
  unfold tailWord_568044
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359133377040538518307593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13812177836054051357743457 10359133377040538518307593)
  ·
    refine ⟨7769350032780403888730695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10359133377040538518307593 7769350032780403888730695)
    ·
      refine ⟨11654025049170605833096043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7769350032780403888730695 11654025049170605833096043)
      ·
        refine ⟨17481037573755908749644065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11654025049170605833096043 17481037573755908749644065)
        ·
          refine ⟨13110778180316931562233049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17481037573755908749644065 13110778180316931562233049)
          ·
            refine ⟨9833083635237698671674787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13110778180316931562233049 9833083635237698671674787)
            ·
              refine ⟨14749625452856548007512181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9833083635237698671674787 14749625452856548007512181)
              ·
                refine ⟨1382777386205301375704267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14749625452856548007512181 1382777386205301375704267)
                ·
                  refine ⟨2074166079307952063556401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382777386205301375704267 2074166079307952063556401)
                  ·
                    refine ⟨1555624559480964047667301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2074166079307952063556401 1555624559480964047667301)
                    ·
                      refine ⟨291679604902680758937619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1555624559480964047667301 291679604902680758937619)
                      ·
                        rfl

theorem cell23_568044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_568044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568044 prefixEnd_568044 := by exact prefixLift 568044
  have htrace : WordTrace (prefixWord ++ tailWord_568044) baseStart_568044 baseEnd_568044 := by
    simpa [prefixWord, tailWord_568044, baseEnd_568044] using wordTrace_append hprefix tailTrace_568044
  have hstable : (prefixWord ++ tailWord_568044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568044).length < 2 ^ (prefixWord ++ tailWord_568044).sum := by decide
  have hdescent : baseEnd_568044 < baseStart_568044 := by decide
  rcases family_descends (prefixWord ++ tailWord_568044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568054 : List Nat := [5, 1, 1, 1, 1, 2, 1, 11]
def baseStart_568054 : Nat := 118140960795 + 568054 * 2 ^ 59
def prefixEnd_568054 : Nat := 4983230072969 + 3 ^ 40 * 568054 * 2
def baseEnd_568054 : Nat := 10803138507749100733799

theorem tailTrace_568054 : CollatzResearch.WordTrace tailWord_568054 prefixEnd_568054 10803138507749100733799 := by
  unfold tailWord_568054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1294914467752803046529951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13812420989363232496319477 1294914467752803046529951)
  ·
    refine ⟨1942371701629204569794927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1294914467752803046529951 1942371701629204569794927)
    ·
      refine ⟨2913557552443806854692391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942371701629204569794927 2913557552443806854692391)
      ·
        refine ⟨4370336328665710282038587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2913557552443806854692391 4370336328665710282038587)
        ·
          refine ⟨6555504492998565423057881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370336328665710282038587 6555504492998565423057881)
          ·
            refine ⟨4916628369748924067293411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6555504492998565423057881 4916628369748924067293411)
            ·
              refine ⟨7374942554623386100940117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4916628369748924067293411 7374942554623386100940117)
              ·
                refine ⟨10803138507749100733799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 7374942554623386100940117 10803138507749100733799)
                ·
                  rfl

theorem cell23_568054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_568054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568054 prefixEnd_568054 := by exact prefixLift 568054
  have htrace : WordTrace (prefixWord ++ tailWord_568054) baseStart_568054 baseEnd_568054 := by
    simpa [prefixWord, tailWord_568054, baseEnd_568054] using wordTrace_append hprefix tailTrace_568054
  have hstable : (prefixWord ++ tailWord_568054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568054).length < 2 ^ (prefixWord ++ tailWord_568054).sum := by decide
  have hdescent : baseEnd_568054 < baseStart_568054 := by decide
  rcases family_descends (prefixWord ++ tailWord_568054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568065 : List Nat := [1, 2, 4, 1, 1, 1, 1, 7, 1, 2, 2]
def baseStart_568065 : Nat := 118140960795 + 568065 * 2 ^ 59
def prefixEnd_568065 : Nat := 4983230072969 + 3 ^ 40 * 568065 * 2
def baseEnd_568065 : Nat := 291690387996425176775023

theorem tailTrace_568065 : CollatzResearch.WordTrace tailWord_568065 prefixEnd_568065 291690387996425176775023 := by
  unfold tailWord_568065
  simp only [CollatzResearch.WordTrace]
  refine ⟨20719032687004997623129649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13812688458003331748753099 20719032687004997623129649)
  ·
    refine ⟨15539274515253748217347237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20719032687004997623129649 15539274515253748217347237)
    ·
      refine ⟨2913613971610077790752607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15539274515253748217347237 2913613971610077790752607)
      ·
        refine ⟨4370420957415116686128911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2913613971610077790752607 4370420957415116686128911)
        ·
          refine ⟨6555631436122675029193367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370420957415116686128911 6555631436122675029193367)
          ·
            refine ⟨9833447154184012543790051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6555631436122675029193367 9833447154184012543790051)
            ·
              refine ⟨14750170731276018815685077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9833447154184012543790051 14750170731276018815685077)
              ·
                refine ⟨345707126514281690992619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14750170731276018815685077 345707126514281690992619)
                ·
                  refine ⟨518560689771422536488929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345707126514281690992619 518560689771422536488929)
                  ·
                    refine ⟨388920517328566902366697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 518560689771422536488929 388920517328566902366697)
                    ·
                      refine ⟨291690387996425176775023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388920517328566902366697 291690387996425176775023)
                      ·
                        rfl

theorem cell23_568065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_568065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568065 prefixEnd_568065 := by exact prefixLift 568065
  have htrace : WordTrace (prefixWord ++ tailWord_568065) baseStart_568065 baseEnd_568065 := by
    simpa [prefixWord, tailWord_568065, baseEnd_568065] using wordTrace_append hprefix tailTrace_568065
  have hstable : (prefixWord ++ tailWord_568065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568065).length < 2 ^ (prefixWord ++ tailWord_568065).sum := by decide
  have hdescent : baseEnd_568065 < baseStart_568065 := by decide
  rcases family_descends (prefixWord ++ tailWord_568065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568081 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 3]
def baseStart_568081 : Nat := 118140960795 + 568081 * 2 ^ 59
def prefixEnd_568081 : Nat := 4983230072969 + 3 ^ 40 * 568081 * 2
def baseEnd_568081 : Nat := 291698603686897114174949

theorem tailTrace_568081 : CollatzResearch.WordTrace tailWord_568081 prefixEnd_568081 291698603686897114174949 := by
  unfold tailWord_568081
  simp only [CollatzResearch.WordTrace]
  refine ⟨20719616254947032355712097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13813077503298021570474731 20719616254947032355712097)
  ·
    refine ⟨15539712191210274266784073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20719616254947032355712097 15539712191210274266784073)
    ·
      refine ⟨11654784143407705700088055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15539712191210274266784073 11654784143407705700088055)
      ·
        refine ⟨17482176215111558550132083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11654784143407705700088055 17482176215111558550132083)
        ·
          refine ⟨26223264322667337825198125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17482176215111558550132083 26223264322667337825198125)
          ·
            refine ⟨9833724121000251684449297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26223264322667337825198125 9833724121000251684449297)
            ·
              refine ⟨7375293090750188763336973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9833724121000251684449297 7375293090750188763336973)
              ·
                refine ⟨2765734909031320786251365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7375293090750188763336973 2765734909031320786251365)
                ·
                  refine ⟨518575295443372647422131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2765734909031320786251365 518575295443372647422131)
                  ·
                    refine ⟨777862943165058971133197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 518575295443372647422131 777862943165058971133197)
                    ·
                      refine ⟨291698603686897114174949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 777862943165058971133197 291698603686897114174949)
                      ·
                        rfl

theorem cell23_568081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_568081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568081 prefixEnd_568081 := by exact prefixLift 568081
  have htrace : WordTrace (prefixWord ++ tailWord_568081) baseStart_568081 baseEnd_568081 := by
    simpa [prefixWord, tailWord_568081, baseEnd_568081] using wordTrace_append hprefix tailTrace_568081
  have hstable : (prefixWord ++ tailWord_568081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568081).length < 2 ^ (prefixWord ++ tailWord_568081).sum := by decide
  have hdescent : baseEnd_568081 < baseStart_568081 := by decide
  rcases family_descends (prefixWord ++ tailWord_568081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568098 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 1, 3, 3]
def baseStart_568098 : Nat := 118140960795 + 568098 * 2 ^ 59
def prefixEnd_568098 : Nat := 4983230072969 + 3 ^ 40 * 568098 * 2
def baseEnd_568098 : Nat := 291707332858023547662371

theorem tailTrace_568098 : CollatzResearch.WordTrace tailWord_568098 prefixEnd_568098 291707332858023547662371 := by
  unfold tailWord_568098
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180059073971361064770237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13813490863923629506053965 5180059073971361064770237)
  ·
    refine ⟨1942522152739260399288839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5180059073971361064770237 1942522152739260399288839)
    ·
      refine ⟨2913783229108890598933259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1942522152739260399288839 2913783229108890598933259)
      ·
        refine ⟨4370674843663335898399889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2913783229108890598933259 4370674843663335898399889)
        ·
          refine ⟨3278006132747501923799917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4370674843663335898399889 3278006132747501923799917)
          ·
            refine ⟨1229252299780313221424969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3278006132747501923799917 1229252299780313221424969)
            ·
              refine ⟨921939224835234916068727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1229252299780313221424969 921939224835234916068727)
              ·
                refine ⟨1382908837252852374103091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921939224835234916068727 1382908837252852374103091)
                ·
                  refine ⟨2074363255879278561154637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1382908837252852374103091 2074363255879278561154637)
                  ·
                    refine ⟨777886220954729460432989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2074363255879278561154637 777886220954729460432989)
                    ·
                      refine ⟨291707332858023547662371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 777886220954729460432989 291707332858023547662371)
                      ·
                        rfl

theorem cell23_568098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_568098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568098 prefixEnd_568098 := by exact prefixLift 568098
  have htrace : WordTrace (prefixWord ++ tailWord_568098) baseStart_568098 baseEnd_568098 := by
    simpa [prefixWord, tailWord_568098, baseEnd_568098] using wordTrace_append hprefix tailTrace_568098
  have hstable : (prefixWord ++ tailWord_568098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568098).length < 2 ^ (prefixWord ++ tailWord_568098).sum := by decide
  have hdescent : baseEnd_568098 < baseStart_568098 := by decide
  rcases family_descends (prefixWord ++ tailWord_568098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568108 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 1, 3, 2]
def baseStart_568108 : Nat := 118140960795 + 568108 * 2 ^ 59
def prefixEnd_568108 : Nat := 4983230072969 + 3 ^ 40 * 568108 * 2
def baseEnd_568108 : Nat := 291712467664568508537325

theorem tailTrace_568108 : CollatzResearch.WordTrace tailWord_568108 prefixEnd_568108 291712467664568508537325 := by
  unfold tailWord_568108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360300512924607983472489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13813734017232810644629985 10360300512924607983472489)
  ·
    refine ⟨7770225384693455987604367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10360300512924607983472489 7770225384693455987604367)
    ·
      refine ⟨11655338077040183981406551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7770225384693455987604367 11655338077040183981406551)
      ·
        refine ⟨17483007115560275972109827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11655338077040183981406551 17483007115560275972109827)
        ·
          refine ⟨26224510673340413958164741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17483007115560275972109827 26224510673340413958164741)
          ·
            refine ⟨4917095751251327617155889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26224510673340413958164741 4917095751251327617155889)
            ·
              refine ⟨3687821813438495712866917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4917095751251327617155889 3687821813438495712866917)
              ·
                refine ⟨691466590019717946162547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3687821813438495712866917 691466590019717946162547)
                ·
                  refine ⟨1037199885029576919243821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691466590019717946162547 1037199885029576919243821)
                  ·
                    refine ⟨388949956886091344716433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1037199885029576919243821 388949956886091344716433)
                    ·
                      refine ⟨291712467664568508537325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 388949956886091344716433 291712467664568508537325)
                      ·
                        rfl

theorem cell23_568108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 3, 2].length) (baseStart_568108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568108 prefixEnd_568108 := by exact prefixLift 568108
  have htrace : WordTrace (prefixWord ++ tailWord_568108) baseStart_568108 baseEnd_568108 := by
    simpa [prefixWord, tailWord_568108, baseEnd_568108] using wordTrace_append hprefix tailTrace_568108
  have hstable : (prefixWord ++ tailWord_568108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568108).length < 2 ^ (prefixWord ++ tailWord_568108).sum := by decide
  have hdescent : baseEnd_568108 < baseStart_568108 := by decide
  rcases family_descends (prefixWord ++ tailWord_568108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568114 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_568114 : Nat := 118140960795 + 568114 * 2 ^ 59
def prefixEnd_568114 : Nat := 4983230072969 + 3 ^ 40 * 568114 * 2
def baseEnd_568114 : Nat := 97238516182831828354099

theorem tailTrace_568114 : CollatzResearch.WordTrace tailWord_568114 prefixEnd_568114 97238516182831828354099 := by
  unfold tailWord_568114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180204965956869747915849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13813879909218319327775597 5180204965956869747915849)
  ·
    refine ⟨3885153724467652310936887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5180204965956869747915849 3885153724467652310936887)
    ·
      refine ⟨5827730586701478466405331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3885153724467652310936887 5827730586701478466405331)
      ·
        refine ⟨8741595880052217699607997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5827730586701478466405331 8741595880052217699607997)
        ·
          refine ⟨3278098455019581637352999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8741595880052217699607997 3278098455019581637352999)
          ·
            refine ⟨4917147682529372456029499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278098455019581637352999 4917147682529372456029499)
            ·
              refine ⟨7375721523794058684044249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4917147682529372456029499 7375721523794058684044249)
              ·
                refine ⟨5531791142845544013033187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7375721523794058684044249 5531791142845544013033187)
                ·
                  refine ⟨8297686714268316019549781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5531791142845544013033187 8297686714268316019549781)
                  ·
                    refine ⟨97238516182831828354099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8297686714268316019549781 97238516182831828354099)
                    ·
                      rfl

theorem cell23_568114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_568114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568114 prefixEnd_568114 := by exact prefixLift 568114
  have htrace : WordTrace (prefixWord ++ tailWord_568114) baseStart_568114 baseEnd_568114 := by
    simpa [prefixWord, tailWord_568114, baseEnd_568114] using wordTrace_append hprefix tailTrace_568114
  have hstable : (prefixWord ++ tailWord_568114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568114).length < 2 ^ (prefixWord ++ tailWord_568114).sum := by decide
  have hdescent : baseEnd_568114 < baseStart_568114 := by decide
  rcases family_descends (prefixWord ++ tailWord_568114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568124 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_568124 : Nat := 118140960795 + 568124 * 2 ^ 59
def prefixEnd_568124 : Nat := 4983230072969 + 3 ^ 40 * 568124 * 2
def baseEnd_568124 : Nat := 291720683355040445937251

theorem tailTrace_568124 : CollatzResearch.WordTrace tailWord_568124 prefixEnd_568124 291720683355040445937251 := by
  unfold tailWord_568124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360592296895625349763713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13814123062527500466351617 10360592296895625349763713)
  ·
    refine ⟨7770444222671719012322785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10360592296895625349763713 7770444222671719012322785)
    ·
      refine ⟨5827833167003789259242089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7770444222671719012322785 5827833167003789259242089)
      ·
        refine ⟨4370874875252841944431567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5827833167003789259242089 4370874875252841944431567)
        ·
          refine ⟨6556312312879262916647351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370874875252841944431567 6556312312879262916647351)
          ·
            refine ⟨9834468469318894374971027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6556312312879262916647351 9834468469318894374971027)
            ·
              refine ⟨14751702703978341562456541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9834468469318894374971027 14751702703978341562456541)
              ·
                refine ⟨5531888513991878085921203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14751702703978341562456541 5531888513991878085921203)
                ·
                  refine ⟨8297832770987817128881805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5531888513991878085921203 8297832770987817128881805)
                  ·
                    refine ⟨3111687289120431423330677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8297832770987817128881805 3111687289120431423330677)
                    ·
                      refine ⟨291720683355040445937251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3111687289120431423330677 291720683355040445937251)
                      ·
                        rfl

theorem cell23_568124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_568124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568124 prefixEnd_568124 := by exact prefixLift 568124
  have htrace : WordTrace (prefixWord ++ tailWord_568124) baseStart_568124 baseEnd_568124 := by
    simpa [prefixWord, tailWord_568124, baseEnd_568124] using wordTrace_append hprefix tailTrace_568124
  have hstable : (prefixWord ++ tailWord_568124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568124).length < 2 ^ (prefixWord ++ tailWord_568124).sum := by decide
  have hdescent : baseEnd_568124 < baseStart_568124 := by decide
  rcases family_descends (prefixWord ++ tailWord_568124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568132 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_568132 : Nat := 118140960795 + 568132 * 2 ^ 59
def prefixEnd_568132 : Nat := 4983230072969 + 3 ^ 40 * 568132 * 2
def baseEnd_568132 : Nat := 291724791200276414637215

theorem tailTrace_568132 : CollatzResearch.WordTrace tailWord_568132 prefixEnd_568132 291724791200276414637215 := by
  unfold tailWord_568132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360738188881134032909325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13814317585174845377212433 10360738188881134032909325)
  ·
    refine ⟨3885276820830425262340997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10360738188881134032909325 3885276820830425262340997)
    ·
      refine ⟨728489403905704736688937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3885276820830425262340997 728489403905704736688937)
      ·
        refine ⟨546367052929278552516703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728489403905704736688937 546367052929278552516703)
        ·
          refine ⟨819550579393917828775055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546367052929278552516703 819550579393917828775055)
          ·
            refine ⟨1229325869090876743162583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819550579393917828775055 1229325869090876743162583)
            ·
              refine ⟨1843988803636315114743875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229325869090876743162583 1843988803636315114743875)
              ·
                refine ⟨2765983205454472672115813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843988803636315114743875 2765983205454472672115813)
                ·
                  refine ⟨518621851022713626021715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2765983205454472672115813 518621851022713626021715)
                  ·
                    refine ⟨777932776534070439032573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 518621851022713626021715 777932776534070439032573)
                    ·
                      refine ⟨291724791200276414637215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 777932776534070439032573 291724791200276414637215)
                      ·
                        rfl

theorem cell23_568132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_568132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568132 prefixEnd_568132 := by exact prefixLift 568132
  have htrace : WordTrace (prefixWord ++ tailWord_568132) baseStart_568132 baseEnd_568132 := by
    simpa [prefixWord, tailWord_568132, baseEnd_568132] using wordTrace_append hprefix tailTrace_568132
  have hstable : (prefixWord ++ tailWord_568132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568132).length < 2 ^ (prefixWord ++ tailWord_568132).sum := by decide
  have hdescent : baseEnd_568132 < baseStart_568132 := by decide
  rcases family_descends (prefixWord ++ tailWord_568132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568144 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 7]
def baseStart_568144 : Nat := 118140960795 + 568144 * 2 ^ 59
def prefixEnd_568144 : Nat := 4983230072969 + 3 ^ 40 * 568144 * 2
def baseEnd_568144 : Nat := 32414550329792263076351

theorem tailTrace_568144 : CollatzResearch.WordTrace tailWord_568144 prefixEnd_568144 32414550329792263076351 := by
  unfold tailWord_568144
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360957026859397057627743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13814609369145862743503657 10360957026859397057627743)
  ·
    refine ⟨15541435540289095586441615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10360957026859397057627743 15541435540289095586441615)
    ·
      refine ⟨23312153310433643379662423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15541435540289095586441615 23312153310433643379662423)
      ·
        refine ⟨34968229965650465069493635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23312153310433643379662423 34968229965650465069493635)
        ·
          refine ⟨52452344948475697604240453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34968229965650465069493635 52452344948475697604240453)
          ·
            refine ⟨9834814677839193300795085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52452344948475697604240453 9834814677839193300795085)
            ·
              refine ⟨3688055504189697487798157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9834814677839193300795085 3688055504189697487798157)
              ·
                refine ⟨1383020814071136557924309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3688055504189697487798157 1383020814071136557924309)
                ·
                  refine ⟨32414550329792263076351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1383020814071136557924309 32414550329792263076351)
                  ·
                    rfl

theorem cell23_568144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 7].length) (baseStart_568144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568144 prefixEnd_568144 := by exact prefixLift 568144
  have htrace : WordTrace (prefixWord ++ tailWord_568144) baseStart_568144 baseEnd_568144 := by
    simpa [prefixWord, tailWord_568144, baseEnd_568144] using wordTrace_append hprefix tailTrace_568144
  have hstable : (prefixWord ++ tailWord_568144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568144).length < 2 ^ (prefixWord ++ tailWord_568144).sum := by decide
  have hdescent : baseEnd_568144 < baseStart_568144 := by decide
  rcases family_descends (prefixWord ++ tailWord_568144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568151 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_568151 : Nat := 118140960795 + 568151 * 2 ^ 59
def prefixEnd_568151 : Nat := 4983230072969 + 3 ^ 40 * 568151 * 2
def baseEnd_568151 : Nat := 291734547332711840299627

theorem tailTrace_568151 : CollatzResearch.WordTrace tailWord_568151 prefixEnd_568151 291734547332711840299627 := by
  unfold tailWord_568151
  simp only [CollatzResearch.WordTrace]
  refine ⟨20722169364693434310760307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13814779576462289540506871 20722169364693434310760307)
  ·
    refine ⟨31083254047040151466140461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20722169364693434310760307 31083254047040151466140461)
    ·
      refine ⟨11656220267640056799802673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31083254047040151466140461 11656220267640056799802673)
      ·
        refine ⟨8742165200730042599852005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11656220267640056799802673 8742165200730042599852005)
        ·
          refine ⟨1639155975136882987472251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8742165200730042599852005 1639155975136882987472251)
          ·
            refine ⟨2458733962705324481208377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1639155975136882987472251 2458733962705324481208377)
            ·
              refine ⟨1844050472028993360906283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458733962705324481208377 1844050472028993360906283)
              ·
                refine ⟨2766075708043490041359425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844050472028993360906283 2766075708043490041359425)
                ·
                  refine ⟨2074556781032617531019569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2766075708043490041359425 2074556781032617531019569)
                  ·
                    refine ⟨1555917585774463148264677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2074556781032617531019569 1555917585774463148264677)
                    ·
                      refine ⟨291734547332711840299627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1555917585774463148264677 291734547332711840299627)
                      ·
                        rfl

theorem cell23_568151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_568151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568151 prefixEnd_568151 := by exact prefixLift 568151
  have htrace : WordTrace (prefixWord ++ tailWord_568151) baseStart_568151 baseEnd_568151 := by
    simpa [prefixWord, tailWord_568151, baseEnd_568151] using wordTrace_append hprefix tailTrace_568151
  have hstable : (prefixWord ++ tailWord_568151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568151).length < 2 ^ (prefixWord ++ tailWord_568151).sum := by decide
  have hdescent : baseEnd_568151 < baseStart_568151 := by decide
  rcases family_descends (prefixWord ++ tailWord_568151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568178 : List Nat := [3, 2, 1, 2, 1, 1, 5, 3, 5]
def baseStart_568178 : Nat := 118140960795 + 568178 * 2 ^ 59
def prefixEnd_568178 : Nat := 4983230072969 + 3 ^ 40 * 568178 * 2
def baseEnd_568178 : Nat := 32416490145598137184667

theorem tailTrace_568178 : CollatzResearch.WordTrace tailWord_568178 prefixEnd_568178 32416490145598137184667 := by
  unfold tailWord_568178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180788533898904480498297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13815436090397078614662125 5180788533898904480498297)
  ·
    refine ⟨3885591400424178360373723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5180788533898904480498297 3885591400424178360373723)
    ·
      refine ⟨5828387100636267540560585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3885591400424178360373723 5828387100636267540560585)
      ·
        refine ⟨4371290325477200655420439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5828387100636267540560585 4371290325477200655420439)
        ·
          refine ⟨6556935488215800983130659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4371290325477200655420439 6556935488215800983130659)
          ·
            refine ⟨9835403232323701474695989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6556935488215800983130659 9835403232323701474695989)
            ·
              refine ⟨922069053030347013252749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9835403232323701474695989 922069053030347013252749)
              ·
                refine ⟨345775894886380129969781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 922069053030347013252749 345775894886380129969781)
                ·
                  refine ⟨32416490145598137184667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345775894886380129969781 32416490145598137184667)
                  ·
                    rfl

theorem cell23_568178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_568178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568178 prefixEnd_568178 := by exact prefixLift 568178
  have htrace : WordTrace (prefixWord ++ tailWord_568178) baseStart_568178 baseEnd_568178 := by
    simpa [prefixWord, tailWord_568178, baseEnd_568178] using wordTrace_append hprefix tailTrace_568178
  have hstable : (prefixWord ++ tailWord_568178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568178).length < 2 ^ (prefixWord ++ tailWord_568178).sum := by decide
  have hdescent : baseEnd_568178 < baseStart_568178 := by decide
  rcases family_descends (prefixWord ++ tailWord_568178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568201 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 5]
def baseStart_568201 : Nat := 118140960795 + 568201 * 2 ^ 59
def prefixEnd_568201 : Nat := 4983230072969 + 3 ^ 40 * 568201 * 2
def baseEnd_568201 : Nat := 291760221365436644674397

theorem tailTrace_568201 : CollatzResearch.WordTrace tailWord_568201 prefixEnd_568201 291760221365436644674397 := by
  unfold tailWord_568201
  simp only [CollatzResearch.WordTrace]
  refine ⟨20723993014512292850080457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13815995343008195233386971 20723993014512292850080457)
  ·
    refine ⟨15542994760884219637560343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20723993014512292850080457 15542994760884219637560343)
    ·
      refine ⟨23314492141326329456340515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15542994760884219637560343 23314492141326329456340515)
      ·
        refine ⟨34971738211989494184510773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23314492141326329456340515 34971738211989494184510773)
        ·
          refine ⟨3278600457374015079797885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34971738211989494184510773 3278600457374015079797885)
          ·
            refine ⟨1229475171515255654924207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3278600457374015079797885 1229475171515255654924207)
            ·
              refine ⟨1844212757272883482386311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229475171515255654924207 1844212757272883482386311)
              ·
                refine ⟨2766319135909325223579467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844212757272883482386311 2766319135909325223579467)
                ·
                  refine ⟨4149478703863987835369201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766319135909325223579467 4149478703863987835369201)
                  ·
                    refine ⟨3112109027897990876526901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4149478703863987835369201 3112109027897990876526901)
                    ·
                      refine ⟨291760221365436644674397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3112109027897990876526901 291760221365436644674397)
                      ·
                        rfl

theorem cell23_568201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_568201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568201 prefixEnd_568201 := by exact prefixLift 568201
  have htrace : WordTrace (prefixWord ++ tailWord_568201) baseStart_568201 baseEnd_568201 := by
    simpa [prefixWord, tailWord_568201, baseEnd_568201] using wordTrace_append hprefix tailTrace_568201
  have hstable : (prefixWord ++ tailWord_568201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568201).length < 2 ^ (prefixWord ++ tailWord_568201).sum := by decide
  have hdescent : baseEnd_568201 < baseStart_568201 := by decide
  rcases family_descends (prefixWord ++ tailWord_568201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568228 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_568228 : Nat := 118140960795 + 568228 * 2 ^ 59
def prefixEnd_568228 : Nat := 4983230072969 + 3 ^ 40 * 568228 * 2
def baseEnd_568228 : Nat := 291774085343108039036773

theorem tailTrace_568228 : CollatzResearch.WordTrace tailWord_568228 prefixEnd_568228 291774085343108039036773 := by
  unfold tailWord_568228
  simp only [CollatzResearch.WordTrace]
  refine ⟨10362488892707238230656669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13816651856942984307542225 10362488892707238230656669)
  ·
    refine ⟨3885933334765214336496251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10362488892707238230656669 3885933334765214336496251)
    ·
      refine ⟨5828900002147821504744377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3885933334765214336496251 5828900002147821504744377)
      ·
        refine ⟨4371675001610866128558283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5828900002147821504744377 4371675001610866128558283)
        ·
          refine ⟨6557512502416299192837425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4371675001610866128558283 6557512502416299192837425)
          ·
            refine ⟨4918134376812224394628069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6557512502416299192837425 4918134376812224394628069)
            ·
              refine ⟨922150195652292073992763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4918134376812224394628069 922150195652292073992763)
              ·
                refine ⟨1383225293478438110989145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922150195652292073992763 1383225293478438110989145)
                ·
                  refine ⟨1037418970108828583241859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1383225293478438110989145 1037418970108828583241859)
                  ·
                    refine ⟨1556128455163242874862789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1037418970108828583241859 1556128455163242874862789)
                    ·
                      refine ⟨291774085343108039036773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1556128455163242874862789 291774085343108039036773)
                      ·
                        rfl

theorem cell23_568228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_568228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568228 prefixEnd_568228 := by exact prefixLift 568228
  have htrace : WordTrace (prefixWord ++ tailWord_568228) baseStart_568228 baseEnd_568228 := by
    simpa [prefixWord, tailWord_568228, baseEnd_568228] using wordTrace_append hprefix tailTrace_568228
  have hstable : (prefixWord ++ tailWord_568228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568228).length < 2 ^ (prefixWord ++ tailWord_568228).sum := by decide
  have hdescent : baseEnd_568228 < baseStart_568228 := by decide
  rcases family_descends (prefixWord ++ tailWord_568228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568248 : List Nat := [2, 1, 2, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_568248 : Nat := 118140960795 + 568248 * 2 ^ 59
def prefixEnd_568248 : Nat := 4983230072969 + 3 ^ 40 * 568248 * 2
def baseEnd_568248 : Nat := 291784354956197960786681

theorem tailTrace_568248 : CollatzResearch.WordTrace tailWord_568248 prefixEnd_568248 291784354956197960786681 := by
  unfold tailWord_568248
  simp only [CollatzResearch.WordTrace]
  refine ⟨10362853622671009938520699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13817138163561346584694265 10362853622671009938520699)
  ·
    refine ⟨15544280434006514907781049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10362853622671009938520699 15544280434006514907781049)
    ·
      refine ⟨11658210325504886180835787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15544280434006514907781049 11658210325504886180835787)
      ·
        refine ⟨17487315488257329271253681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11658210325504886180835787 17487315488257329271253681)
        ·
          refine ⟨13115486616192996953440261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17487315488257329271253681 13115486616192996953440261)
          ·
            refine ⟨2459153740536186928770049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13115486616192996953440261 2459153740536186928770049)
            ·
              refine ⟨1844365305402140196577537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2459153740536186928770049 1844365305402140196577537)
              ·
                refine ⟨1383273979051605147433153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844365305402140196577537 1383273979051605147433153)
                ·
                  refine ⟨1037455484288703860574865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1383273979051605147433153 1037455484288703860574865)
                  ·
                    refine ⟨778091613216527895431149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1037455484288703860574865 778091613216527895431149)
                    ·
                      refine ⟨291784354956197960786681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 778091613216527895431149 291784354956197960786681)
                      ·
                        rfl

theorem cell23_568248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_568248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568248 prefixEnd_568248 := by exact prefixLift 568248
  have htrace : WordTrace (prefixWord ++ tailWord_568248) baseStart_568248 baseEnd_568248 := by
    simpa [prefixWord, tailWord_568248, baseEnd_568248] using wordTrace_append hprefix tailTrace_568248
  have hstable : (prefixWord ++ tailWord_568248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568248).length < 2 ^ (prefixWord ++ tailWord_568248).sum := by decide
  have hdescent : baseEnd_568248 < baseStart_568248 := by decide
  rcases family_descends (prefixWord ++ tailWord_568248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568302 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_568302 : Nat := 118140960795 + 568302 * 2 ^ 59
def prefixEnd_568302 : Nat := 4983230072969 + 3 ^ 40 * 568302 * 2
def baseEnd_568302 : Nat := 32423564767948972167937

theorem tailTrace_568302 : CollatzResearch.WordTrace tailWord_568302 prefixEnd_568302 32423564767948972167937 := by
  unfold tailWord_568302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2590959598393298387438395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13818451191430924733004773 2590959598393298387438395)
  ·
    refine ⟨3886439397589947581157593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2590959598393298387438395 3886439397589947581157593)
    ·
      refine ⟨2914829548192460685868195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3886439397589947581157593 2914829548192460685868195)
      ·
        refine ⟨4372244322288691028802293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914829548192460685868195 4372244322288691028802293)
        ·
          refine ⟨409897905214564783950215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4372244322288691028802293 409897905214564783950215)
          ·
            refine ⟨614846857821847175925323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409897905214564783950215 614846857821847175925323)
            ·
              refine ⟨922270286732770763887985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614846857821847175925323 922270286732770763887985)
              ·
                refine ⟨691702715049578072915989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922270286732770763887985 691702715049578072915989)
                ·
                  refine ⟨32423564767948972167937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 691702715049578072915989 32423564767948972167937)
                  ·
                    rfl

theorem cell23_568302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_568302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568302 prefixEnd_568302 := by exact prefixLift 568302
  have htrace : WordTrace (prefixWord ++ tailWord_568302) baseStart_568302 baseEnd_568302 := by
    simpa [prefixWord, tailWord_568302, baseEnd_568302] using wordTrace_append hprefix tailTrace_568302
  have hstable : (prefixWord ++ tailWord_568302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568302).length < 2 ^ (prefixWord ++ tailWord_568302).sum := by decide
  have hdescent : baseEnd_568302 < baseStart_568302 := by decide
  rcases family_descends (prefixWord ++ tailWord_568302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568328 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 1, 6]
def baseStart_568328 : Nat := 118140960795 + 568328 * 2 ^ 59
def prefixEnd_568328 : Nat := 4983230072969 + 3 ^ 40 * 568328 * 2
def baseEnd_568328 : Nat := 97275144469519215928771

theorem tailTrace_568328 : CollatzResearch.WordTrace tailWord_568328 prefixEnd_568328 97275144469519215928771 := by
  unfold tailWord_568328
  simp only [CollatzResearch.WordTrace]
  refine ⟨10364312542526096769976819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13819083390034795693302425 10364312542526096769976819)
  ·
    refine ⟨15546468813789145154965229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10364312542526096769976819 15546468813789145154965229)
    ·
      refine ⟨5829925805170929433111961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15546468813789145154965229 5829925805170929433111961)
      ·
        refine ⟨4372444353878197074833971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5829925805170929433111961 4372444353878197074833971)
        ·
          refine ⟨6558666530817295612250957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4372444353878197074833971 6558666530817295612250957)
          ·
            refine ⟨2459499949056485854594109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6558666530817295612250957 2459499949056485854594109)
            ·
              refine ⟨922312480896182195472791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2459499949056485854594109 922312480896182195472791)
              ·
                refine ⟨1383468721344273293209187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922312480896182195472791 1383468721344273293209187)
                ·
                  refine ⟨2075203082016409939813781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383468721344273293209187 2075203082016409939813781)
                  ·
                    refine ⟨97275144469519215928771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2075203082016409939813781 97275144469519215928771)
                    ·
                      rfl

theorem cell23_568328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_568328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568328 prefixEnd_568328 := by exact prefixLift 568328
  have htrace : WordTrace (prefixWord ++ tailWord_568328) baseStart_568328 baseEnd_568328 := by
    simpa [prefixWord, tailWord_568328, baseEnd_568328] using wordTrace_append hprefix tailTrace_568328
  have hstable : (prefixWord ++ tailWord_568328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568328).length < 2 ^ (prefixWord ++ tailWord_568328).sum := by decide
  have hdescent : baseEnd_568328 < baseStart_568328 := by decide
  rcases family_descends (prefixWord ++ tailWord_568328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568355 : List Nat := [1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 3]
def baseStart_568355 : Nat := 118140960795 + 568355 * 2 ^ 59
def prefixEnd_568355 : Nat := 4983230072969 + 3 ^ 40 * 568355 * 2
def baseEnd_568355 : Nat := 291839297386229042148689

theorem tailTrace_568355 : CollatzResearch.WordTrace tailWord_568355 prefixEnd_568355 291839297386229042148689 := by
  unfold tailWord_568355
  simp only [CollatzResearch.WordTrace]
  refine ⟨20729609855954377151186519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13819739903969584767457679 20729609855954377151186519)
  ·
    refine ⟨31094414783931565726779779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20729609855954377151186519 31094414783931565726779779)
    ·
      refine ⟨46641622175897348590169669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31094414783931565726779779 46641622175897348590169669)
      ·
        refine ⟨8745304157980752860656813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46641622175897348590169669 8745304157980752860656813)
        ·
          refine ⟨3279489059242782322746305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8745304157980752860656813 3279489059242782322746305)
          ·
            refine ⟨2459616794432086742059729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3279489059242782322746305 2459616794432086742059729)
            ·
              refine ⟨1844712595824065056544797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2459616794432086742059729 1844712595824065056544797)
              ·
                refine ⟨691767223434024396204299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1844712595824065056544797 691767223434024396204299)
                ·
                  refine ⟨1037650835151036594306449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 691767223434024396204299 1037650835151036594306449)
                  ·
                    refine ⟨778238126363277445729837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1037650835151036594306449 778238126363277445729837)
                    ·
                      refine ⟨291839297386229042148689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 778238126363277445729837 291839297386229042148689)
                      ·
                        rfl

theorem cell23_568355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_568355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568355 prefixEnd_568355 := by exact prefixLift 568355
  have htrace : WordTrace (prefixWord ++ tailWord_568355) baseStart_568355 baseEnd_568355 := by
    simpa [prefixWord, tailWord_568355, baseEnd_568355] using wordTrace_append hprefix tailTrace_568355
  have hstable : (prefixWord ++ tailWord_568355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568355).length < 2 ^ (prefixWord ++ tailWord_568355).sum := by decide
  have hdescent : baseEnd_568355 < baseStart_568355 := by decide
  rcases family_descends (prefixWord ++ tailWord_568355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568371 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 2, 7]
def baseStart_568371 : Nat := 118140960795 + 568371 * 2 ^ 59
def prefixEnd_568371 : Nat := 4983230072969 + 3 ^ 40 * 568371 * 2
def baseEnd_568371 : Nat := 97282504358900326516205

theorem tailTrace_568371 : CollatzResearch.WordTrace tailWord_568371 prefixEnd_568371 97282504358900326516205 := by
  unfold tailWord_568371
  simp only [CollatzResearch.WordTrace]
  refine ⟨20730193423896411883768967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13820128949264274589179311 20730193423896411883768967)
  ·
    refine ⟨31095290135844617825653451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20730193423896411883768967 31095290135844617825653451)
    ·
      refine ⟨46642935203766926738480177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31095290135844617825653451 46642935203766926738480177)
      ·
        refine ⟨34982201402825195053860133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46642935203766926738480177 34982201402825195053860133)
        ·
          refine ⟨6559162763029724072598775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34982201402825195053860133 6559162763029724072598775)
          ·
            refine ⟨9838744144544586108898163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6559162763029724072598775 9838744144544586108898163)
            ·
              refine ⟨14758116216816879163347245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9838744144544586108898163 14758116216816879163347245)
              ·
                refine ⟨5534293581306329686255217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14758116216816879163347245 5534293581306329686255217)
                ·
                  refine ⟨4150720185979747264691413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5534293581306329686255217 4150720185979747264691413)
                  ·
                    refine ⟨97282504358900326516205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4150720185979747264691413 97282504358900326516205)
                    ·
                      rfl

theorem cell23_568371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 7].length) (baseStart_568371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568371 prefixEnd_568371 := by exact prefixLift 568371
  have htrace : WordTrace (prefixWord ++ tailWord_568371) baseStart_568371 baseEnd_568371 := by
    simpa [prefixWord, tailWord_568371, baseEnd_568371] using wordTrace_append hprefix tailTrace_568371
  have hstable : (prefixWord ++ tailWord_568371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568371).length < 2 ^ (prefixWord ++ tailWord_568371).sum := by decide
  have hdescent : baseEnd_568371 < baseStart_568371 := by decide
  rcases family_descends (prefixWord ++ tailWord_568371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568406 : List Nat := [5, 2, 2, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_568406 : Nat := 118140960795 + 568406 * 2 ^ 59
def prefixEnd_568406 : Nat := 4983230072969 + 3 ^ 40 * 568406 * 2
def baseEnd_568406 : Nat := 291865484899608342610955

theorem tailTrace_568406 : CollatzResearch.WordTrace tailWord_568406 prefixEnd_568406 291865484899608342610955 := by
  unfold tailWord_568406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295716873673100803830817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13820979985846408574195381 1295716873673100803830817)
  ·
    refine ⟨971787655254825602873113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1295716873673100803830817 971787655254825602873113)
    ·
      refine ⟨728840741441119202154835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 971787655254825602873113 728840741441119202154835)
      ·
        refine ⟨1093261112161678803232253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 728840741441119202154835 1093261112161678803232253)
        ·
          refine ⟨409972917060629551212095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1093261112161678803232253 409972917060629551212095)
          ·
            refine ⟨614959375590944326818143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409972917060629551212095 614959375590944326818143)
            ·
              refine ⟨922439063386416490227215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614959375590944326818143 922439063386416490227215)
              ·
                refine ⟨1383658595079624735340823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922439063386416490227215 1383658595079624735340823)
                ·
                  refine ⟨2075487892619437103011235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1383658595079624735340823 2075487892619437103011235)
                  ·
                    refine ⟨3113231838929155654516853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2075487892619437103011235 3113231838929155654516853)
                    ·
                      refine ⟨291865484899608342610955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3113231838929155654516853 291865484899608342610955)
                      ·
                        rfl

theorem cell23_568406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_568406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568406 prefixEnd_568406 := by exact prefixLift 568406
  have htrace : WordTrace (prefixWord ++ tailWord_568406) baseStart_568406 baseEnd_568406 := by
    simpa [prefixWord, tailWord_568406, baseEnd_568406] using wordTrace_append hprefix tailTrace_568406
  have hstable : (prefixWord ++ tailWord_568406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568406).length < 2 ^ (prefixWord ++ tailWord_568406).sum := by decide
  have hdescent : baseEnd_568406 < baseStart_568406 := by decide
  rcases family_descends (prefixWord ++ tailWord_568406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568428 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_568428 : Nat := 118140960795 + 568428 * 2 ^ 59
def prefixEnd_568428 : Nat := 4983230072969 + 3 ^ 40 * 568428 * 2
def baseEnd_568428 : Nat := 291876781474007256535853

theorem tailTrace_568428 : CollatzResearch.WordTrace tailWord_568428 prefixEnd_568428 291876781474007256535853 := by
  unfold tailWord_568428
  simp only [CollatzResearch.WordTrace]
  refine ⟨10366136192344955309296969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13821514923126607079062625 10366136192344955309296969)
  ·
    refine ⟨7774602144258716481972727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10366136192344955309296969 7774602144258716481972727)
    ·
      refine ⟨11661903216388074722959091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7774602144258716481972727 11661903216388074722959091)
      ·
        refine ⟨17492854824582112084438637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11661903216388074722959091 17492854824582112084438637)
        ·
          refine ⟨6559820559218292031664489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17492854824582112084438637 6559820559218292031664489)
          ·
            refine ⟨4919865419413719023748367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6559820559218292031664489 4919865419413719023748367)
            ·
              refine ⟨7379798129120578535622551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919865419413719023748367 7379798129120578535622551)
              ·
                refine ⟨11069697193680867803433827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7379798129120578535622551 11069697193680867803433827)
                ·
                  refine ⟨16604545790521301705150741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11069697193680867803433827 16604545790521301705150741)
                  ·
                    refine ⟨778338083930686017428941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16604545790521301705150741 778338083930686017428941)
                    ·
                      refine ⟨291876781474007256535853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 778338083930686017428941 291876781474007256535853)
                      ·
                        rfl

theorem cell23_568428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_568428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568428 prefixEnd_568428 := by exact prefixLift 568428
  have htrace : WordTrace (prefixWord ++ tailWord_568428) baseStart_568428 baseEnd_568428 := by
    simpa [prefixWord, tailWord_568428, baseEnd_568428] using wordTrace_append hprefix tailTrace_568428
  have hstable : (prefixWord ++ tailWord_568428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568428).length < 2 ^ (prefixWord ++ tailWord_568428).sum := by decide
  have hdescent : baseEnd_568428 < baseStart_568428 := by decide
  rcases family_descends (prefixWord ++ tailWord_568428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568476 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_568476 : Nat := 118140960795 + 568476 * 2 ^ 59
def prefixEnd_568476 : Nat := 4983230072969 + 3 ^ 40 * 568476 * 2
def baseEnd_568476 : Nat := 291901428545423068735633

theorem tailTrace_568476 : CollatzResearch.WordTrace tailWord_568476 prefixEnd_568476 291901428545423068735633 := by
  unfold tailWord_568476
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367011544258007408170641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13822682059010676544227521 10367011544258007408170641)
  ·
    refine ⟨7775258658193505556127981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10367011544258007408170641 7775258658193505556127981)
    ·
      refine ⟨2915721996822564583547993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7775258658193505556127981 2915721996822564583547993)
      ·
        refine ⟨2186791497616923437660995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2915721996822564583547993 2186791497616923437660995)
        ·
          refine ⟨3280187246425385156491493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2186791497616923437660995 3280187246425385156491493)
          ·
            refine ⟨615035108704759716842155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3280187246425385156491493 615035108704759716842155)
            ·
              refine ⟨922552663057139575263233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615035108704759716842155 922552663057139575263233)
              ·
                refine ⟨691914497292854681447425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922552663057139575263233 691914497292854681447425)
                ·
                  refine ⟨518935872969641011085569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 691914497292854681447425 518935872969641011085569)
                  ·
                    refine ⟨389201904727230758314177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 518935872969641011085569 389201904727230758314177)
                    ·
                      refine ⟨291901428545423068735633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389201904727230758314177 291901428545423068735633)
                      ·
                        rfl

theorem cell23_568476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_568476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568476 prefixEnd_568476 := by exact prefixLift 568476
  have htrace : WordTrace (prefixWord ++ tailWord_568476) baseStart_568476 baseEnd_568476 := by
    simpa [prefixWord, tailWord_568476, baseEnd_568476] using wordTrace_append hprefix tailTrace_568476
  have hstable : (prefixWord ++ tailWord_568476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568476).length < 2 ^ (prefixWord ++ tailWord_568476).sum := by decide
  have hdescent : baseEnd_568476 < baseStart_568476 := by decide
  rcases family_descends (prefixWord ++ tailWord_568476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568482 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 7]
def baseStart_568482 : Nat := 118140960795 + 568482 * 2 ^ 59
def prefixEnd_568482 : Nat := 4983230072969 + 3 ^ 40 * 568482 * 2
def baseEnd_568482 : Nat := 32433834381038893917845

theorem tailTrace_568482 : CollatzResearch.WordTrace tailWord_568482 prefixEnd_568482 32433834381038893917845 := by
  unfold tailWord_568482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5183560481623569460264925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13822827950996185227373133 5183560481623569460264925)
  ·
    refine ⟨1943835180608838547599347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5183560481623569460264925 1943835180608838547599347)
    ·
      refine ⟨2915752770913257821399021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1943835180608838547599347 2915752770913257821399021)
      ·
        refine ⟨1093407289092471683024633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2915752770913257821399021 1093407289092471683024633)
        ·
          refine ⟨820055466819353762268475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1093407289092471683024633 820055466819353762268475)
          ·
            refine ⟨1230083200229030643402713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820055466819353762268475 1230083200229030643402713)
            ·
              refine ⟨922562400171772982552035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1230083200229030643402713 922562400171772982552035)
              ·
                refine ⟨1383843600257659473828053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922562400171772982552035 1383843600257659473828053)
                ·
                  refine ⟨32433834381038893917845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1383843600257659473828053 32433834381038893917845)
                  ·
                    rfl

theorem cell23_568482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_568482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568482 prefixEnd_568482 := by exact prefixLift 568482
  have htrace : WordTrace (prefixWord ++ tailWord_568482) baseStart_568482 baseEnd_568482 := by
    simpa [prefixWord, tailWord_568482, baseEnd_568482] using wordTrace_append hprefix tailTrace_568482
  have hstable : (prefixWord ++ tailWord_568482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568482).length < 2 ^ (prefixWord ++ tailWord_568482).sum := by decide
  have hdescent : baseEnd_568482 < baseStart_568482 := by decide
  rcases family_descends (prefixWord ++ tailWord_568482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568493 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_568493 : Nat := 118140960795 + 568493 * 2 ^ 59
def prefixEnd_568493 : Nat := 4983230072969 + 3 ^ 40 * 568493 * 2
def baseEnd_568493 : Nat := 291910157716549502223055

theorem tailTrace_568493 : CollatzResearch.WordTrace tailWord_568493 prefixEnd_568493 291910157716549502223055 := by
  unfold tailWord_568493
  simp only [CollatzResearch.WordTrace]
  refine ⟨20734643129454426719710133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13823095419636284479806755 20734643129454426719710133)
  ·
    refine ⟨1943872793386352504972825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20734643129454426719710133 1943872793386352504972825)
    ·
      refine ⟨1457904595039764378729619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1943872793386352504972825 1457904595039764378729619)
      ·
        refine ⟨2186856892559646568094429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457904595039764378729619 2186856892559646568094429)
        ·
          refine ⟨820071334709867463035411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2186856892559646568094429 820071334709867463035411)
          ·
            refine ⟨1230107002064801194553117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820071334709867463035411 1230107002064801194553117)
            ·
              refine ⟨461290125774300447957419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1230107002064801194553117 461290125774300447957419)
              ·
                refine ⟨691935188661450671936129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461290125774300447957419 691935188661450671936129)
                ·
                  refine ⟨518951391496088003952097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 691935188661450671936129 518951391496088003952097)
                  ·
                    refine ⟨389213543622066002964073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 518951391496088003952097 389213543622066002964073)
                    ·
                      refine ⟨291910157716549502223055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389213543622066002964073 291910157716549502223055)
                      ·
                        rfl

theorem cell23_568493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_568493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568493 prefixEnd_568493 := by exact prefixLift 568493
  have htrace : WordTrace (prefixWord ++ tailWord_568493) baseStart_568493 baseEnd_568493 := by
    simpa [prefixWord, tailWord_568493, baseEnd_568493] using wordTrace_append hprefix tailTrace_568493
  have hstable : (prefixWord ++ tailWord_568493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568493).length < 2 ^ (prefixWord ++ tailWord_568493).sum := by decide
  have hdescent : baseEnd_568493 < baseStart_568493 := by decide
  rcases family_descends (prefixWord ++ tailWord_568493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568515 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 4, 4, 2]
def baseStart_568515 : Nat := 118140960795 + 568515 * 2 ^ 59
def prefixEnd_568515 : Nat := 4983230072969 + 3 ^ 40 * 568515 * 2
def baseEnd_568515 : Nat := 291921454290948416147953

theorem tailTrace_568515 : CollatzResearch.WordTrace tailWord_568515 prefixEnd_568515 291921454290948416147953 := by
  unfold tailWord_568515
  simp only [CollatzResearch.WordTrace]
  refine ⟨20735445535374724477010999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13823630356916482984673999 20735445535374724477010999)
  ·
    refine ⟨31103168303062086715516499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20735445535374724477010999 31103168303062086715516499)
    ·
      refine ⟨46654752454593130073274749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31103168303062086715516499 46654752454593130073274749)
      ·
        refine ⟨17495532170472423777478031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46654752454593130073274749 17495532170472423777478031)
        ·
          refine ⟨26243298255708635666217047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17495532170472423777478031 26243298255708635666217047)
          ·
            refine ⟨39364947383562953499325571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26243298255708635666217047 39364947383562953499325571)
            ·
              refine ⟨59047421075344430248988357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39364947383562953499325571 59047421075344430248988357)
              ·
                refine ⟨11071391451627080671685317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59047421075344430248988357 11071391451627080671685317)
                ·
                  refine ⟨2075885897180077625940997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11071391451627080671685317 2075885897180077625940997)
                  ·
                    refine ⟨389228605721264554863937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2075885897180077625940997 389228605721264554863937)
                    ·
                      refine ⟨291921454290948416147953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389228605721264554863937 291921454290948416147953)
                      ·
                        rfl

theorem cell23_568515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_568515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568515 prefixEnd_568515 := by exact prefixLift 568515
  have htrace : WordTrace (prefixWord ++ tailWord_568515) baseStart_568515 baseEnd_568515 := by
    simpa [prefixWord, tailWord_568515, baseEnd_568515] using wordTrace_append hprefix tailTrace_568515
  have hstable : (prefixWord ++ tailWord_568515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568515).length < 2 ^ (prefixWord ++ tailWord_568515).sum := by decide
  have hdescent : baseEnd_568515 < baseStart_568515 := by decide
  rcases family_descends (prefixWord ++ tailWord_568515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568516 : List Nat := [2, 3, 3, 1, 4, 1, 1, 3, 5]
def baseStart_568516 : Nat := 118140960795 + 568516 * 2 ^ 59
def prefixEnd_568516 : Nat := 4983230072969 + 3 ^ 40 * 568516 * 2
def baseEnd_568516 : Nat := 32435774196844768026161

theorem tailTrace_568516 : CollatzResearch.WordTrace tailWord_568516 prefixEnd_568516 32435774196844768026161 := by
  unfold tailWord_568516
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367741004185550823898701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13823654672247401098531601 10367741004185550823898701)
  ·
    refine ⟨3887902876569581558962013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10367741004185550823898701 3887902876569581558962013)
    ·
      refine ⟨1457963578713593084610755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3887902876569581558962013 1457963578713593084610755)
      ·
        refine ⟨2186945368070389626916133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1457963578713593084610755 2186945368070389626916133)
        ·
          refine ⟨410052256513198055046775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2186945368070389626916133 410052256513198055046775)
          ·
            refine ⟨615078384769797082570163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410052256513198055046775 615078384769797082570163)
            ·
              refine ⟨922617577154695623855245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615078384769797082570163 922617577154695623855245)
              ·
                refine ⟨345981591433010858945717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 922617577154695623855245 345981591433010858945717)
                ·
                  refine ⟨32435774196844768026161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345981591433010858945717 32435774196844768026161)
                  ·
                    rfl

theorem cell23_568516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_568516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568516 prefixEnd_568516 := by exact prefixLift 568516
  have htrace : WordTrace (prefixWord ++ tailWord_568516) baseStart_568516 baseEnd_568516 := by
    simpa [prefixWord, tailWord_568516, baseEnd_568516] using wordTrace_append hprefix tailTrace_568516
  have hstable : (prefixWord ++ tailWord_568516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568516).length < 2 ^ (prefixWord ++ tailWord_568516).sum := by decide
  have hdescent : baseEnd_568516 < baseStart_568516 := by decide
  rcases family_descends (prefixWord ++ tailWord_568516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568535 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_568535 : Nat := 118140960795 + 568535 * 2 ^ 59
def prefixEnd_568535 : Nat := 4983230072969 + 3 ^ 40 * 568535 * 2
def baseEnd_568535 : Nat := 291931723904038337897861

theorem tailTrace_568535 : CollatzResearch.WordTrace tailWord_568535 prefixEnd_568535 291931723904038337897861 := by
  unfold tailWord_568535
  simp only [CollatzResearch.WordTrace]
  refine ⟨20736174995302267892739059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13824116663534845261826039 20736174995302267892739059)
  ·
    refine ⟨31104262492953401839108589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20736174995302267892739059 31104262492953401839108589)
    ·
      refine ⟨11664098434857525689665721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31104262492953401839108589 11664098434857525689665721)
      ·
        refine ⟨8748073826143144267249291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11664098434857525689665721 8748073826143144267249291)
        ·
          refine ⟨13122110739214716400873937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8748073826143144267249291 13122110739214716400873937)
          ·
            refine ⟨9841583054411037300655453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13122110739214716400873937 9841583054411037300655453)
            ·
              refine ⟨3690593645404138987745795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9841583054411037300655453 3690593645404138987745795)
              ·
                refine ⟨5535890468106208481618693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3690593645404138987745795 5535890468106208481618693)
                ·
                  refine ⟨1037979462769914090303505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5535890468106208481618693 1037979462769914090303505)
                  ·
                    refine ⟨778484597077435567727629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1037979462769914090303505 778484597077435567727629)
                    ·
                      refine ⟨291931723904038337897861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 778484597077435567727629 291931723904038337897861)
                      ·
                        rfl

theorem cell23_568535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_568535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568535 prefixEnd_568535 := by exact prefixLift 568535
  have htrace : WordTrace (prefixWord ++ tailWord_568535) baseStart_568535 baseEnd_568535 := by
    simpa [prefixWord, tailWord_568535, baseEnd_568535] using wordTrace_append hprefix tailTrace_568535
  have hstable : (prefixWord ++ tailWord_568535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568535).length < 2 ^ (prefixWord ++ tailWord_568535).sum := by decide
  have hdescent : baseEnd_568535 < baseStart_568535 := by decide
  rcases family_descends (prefixWord ++ tailWord_568535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568555 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 6]
def baseStart_568555 : Nat := 118140960795 + 568555 * 2 ^ 59
def prefixEnd_568555 : Nat := 4983230072969 + 3 ^ 40 * 568555 * 2
def baseEnd_568555 : Nat := 32437999279680917738641

theorem tailTrace_568555 : CollatzResearch.WordTrace tailWord_568555 prefixEnd_568555 32437999279680917738641 := by
  unfold tailWord_568555
  simp only [CollatzResearch.WordTrace]
  refine ⟨20736904455229811308467119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13824602970153207538978079 20736904455229811308467119)
  ·
    refine ⟨31105356682844716962700679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20736904455229811308467119 31105356682844716962700679)
    ·
      refine ⟨46658035024267075444051019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31105356682844716962700679 46658035024267075444051019)
      ·
        refine ⟨69987052536400613166076529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46658035024267075444051019 69987052536400613166076529)
        ·
          refine ⟨52490289402300459874557397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69987052536400613166076529 52490289402300459874557397)
          ·
            refine ⟨1230241157866417028309939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 52490289402300459874557397 1230241157866417028309939)
            ·
              refine ⟨1845361736799625542464909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1230241157866417028309939 1845361736799625542464909)
              ·
                refine ⟨692010651299859578424341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1845361736799625542464909 692010651299859578424341)
                ·
                  refine ⟨32437999279680917738641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 692010651299859578424341 32437999279680917738641)
                  ·
                    rfl

theorem cell23_568555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 6].length) (baseStart_568555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568555 prefixEnd_568555 := by exact prefixLift 568555
  have htrace : WordTrace (prefixWord ++ tailWord_568555) baseStart_568555 baseEnd_568555 := by
    simpa [prefixWord, tailWord_568555, baseEnd_568555] using wordTrace_append hprefix tailTrace_568555
  have hstable : (prefixWord ++ tailWord_568555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568555).length < 2 ^ (prefixWord ++ tailWord_568555).sum := by decide
  have hdescent : baseEnd_568555 < baseStart_568555 := by decide
  rcases family_descends (prefixWord ++ tailWord_568555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568626 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_568626 : Nat := 118140960795 + 568626 * 2 ^ 59
def prefixEnd_568626 : Nat := 4983230072969 + 3 ^ 40 * 568626 * 2
def baseEnd_568626 : Nat := 291978450643597481859943

theorem tailTrace_568626 : CollatzResearch.WordTrace tailWord_568626 prefixEnd_568626 291978450643597481859943 := by
  unfold tailWord_568626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5184873509493147608575433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13826329358648393622867821 5184873509493147608575433)
  ·
    refine ⟨3888655132119860706431575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5184873509493147608575433 3888655132119860706431575)
    ·
      refine ⟨5832982698179791059647363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3888655132119860706431575 5832982698179791059647363)
      ·
        refine ⟨8749474047269686589471045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5832982698179791059647363 8749474047269686589471045)
        ·
          refine ⟨1640526383863066235525821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8749474047269686589471045 1640526383863066235525821)
          ·
            refine ⟨615197393948649838322183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1640526383863066235525821 615197393948649838322183)
            ·
              refine ⟨922796090922974757483275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615197393948649838322183 922796090922974757483275)
              ·
                refine ⟨1384194136384462136224913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922796090922974757483275 1384194136384462136224913)
                ·
                  refine ⟨1038145602288346602168685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1384194136384462136224913 1038145602288346602168685)
                  ·
                    refine ⟨389304600858129975813257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1038145602288346602168685 389304600858129975813257)
                    ·
                      refine ⟨291978450643597481859943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389304600858129975813257 291978450643597481859943)
                      ·
                        rfl

theorem cell23_568626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_568626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568626 prefixEnd_568626 := by exact prefixLift 568626
  have htrace : WordTrace (prefixWord ++ tailWord_568626) baseStart_568626 baseEnd_568626 := by
    simpa [prefixWord, tailWord_568626, baseEnd_568626] using wordTrace_append hprefix tailTrace_568626
  have hstable : (prefixWord ++ tailWord_568626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568626).length < 2 ^ (prefixWord ++ tailWord_568626).sum := by decide
  have hdescent : baseEnd_568626 < baseStart_568626 := by decide
  rcases family_descends (prefixWord ++ tailWord_568626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568633 : List Nat := [1, 2, 1, 6, 2, 1, 2, 3, 1, 1, 3]
def baseStart_568633 : Nat := 118140960795 + 568633 * 2 ^ 59
def prefixEnd_568633 : Nat := 4983230072969 + 3 ^ 40 * 568633 * 2
def baseEnd_568633 : Nat := 291982045008178954472411

theorem tailTrace_568633 : CollatzResearch.WordTrace tailWord_568633 prefixEnd_568633 291982045008178954472411 := by
  unfold tailWord_568633
  simp only [CollatzResearch.WordTrace]
  refine ⟨20739749348947230629806553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13826499565964820419871035 20739749348947230629806553)
  ·
    refine ⟨15554812011710422972354915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20739749348947230629806553 15554812011710422972354915)
    ·
      refine ⟨23332218017565634458532373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15554812011710422972354915 23332218017565634458532373)
      ·
        refine ⟨1093697719573389115243705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23332218017565634458532373 1093697719573389115243705)
        ·
          refine ⟨820273289680041836432779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1093697719573389115243705 820273289680041836432779)
          ·
            refine ⟨1230409934520062754649169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820273289680041836432779 1230409934520062754649169)
            ·
              refine ⟨922807450890047065986877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1230409934520062754649169 922807450890047065986877)
              ·
                refine ⟨346052794083767649745079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 922807450890047065986877 346052794083767649745079)
                ·
                  refine ⟨519079191125651474617619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346052794083767649745079 519079191125651474617619)
                  ·
                    refine ⟨778618786688477211926429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 519079191125651474617619 778618786688477211926429)
                    ·
                      refine ⟨291982045008178954472411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 778618786688477211926429 291982045008178954472411)
                      ·
                        rfl

theorem cell23_568633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_568633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568633 prefixEnd_568633 := by exact prefixLift 568633
  have htrace : WordTrace (prefixWord ++ tailWord_568633) baseStart_568633 baseEnd_568633 := by
    simpa [prefixWord, tailWord_568633, baseEnd_568633] using wordTrace_append hprefix tailTrace_568633
  have hstable : (prefixWord ++ tailWord_568633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568633).length < 2 ^ (prefixWord ++ tailWord_568633).sum := by decide
  have hdescent : baseEnd_568633 < baseStart_568633 := by decide
  rcases family_descends (prefixWord ++ tailWord_568633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568639 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 1, 1, 4]
def baseStart_568639 : Nat := 118140960795 + 568639 * 2 ^ 59
def prefixEnd_568639 : Nat := 4983230072969 + 3 ^ 40 * 568639 * 2
def baseEnd_568639 : Nat := 291985125892105930997383

theorem tailTrace_568639 : CollatzResearch.WordTrace tailWord_568639 prefixEnd_568639 291985125892105930997383 := by
  unfold tailWord_568639
  simp only [CollatzResearch.WordTrace]
  refine ⟨20739968186925493654524971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13826645457950329103016647 20739968186925493654524971)
  ·
    refine ⟨31109952280388240481787457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20739968186925493654524971 31109952280388240481787457)
    ·
      refine ⟨23332464210291180361340593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31109952280388240481787457 23332464210291180361340593)
      ·
        refine ⟨17499348157718385271005445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23332464210291180361340593 17499348157718385271005445)
        ·
          refine ⟨3281127779572197238313521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17499348157718385271005445 3281127779572197238313521)
          ·
            refine ⟨2460845834679147928735141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3281127779572197238313521 2460845834679147928735141)
            ·
              refine ⟨461408594002340236637839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2460845834679147928735141 461408594002340236637839)
              ·
                refine ⟨692112891003510354956759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461408594002340236637839 692112891003510354956759)
                ·
                  refine ⟨1038169336505265532435139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692112891003510354956759 1038169336505265532435139)
                  ·
                    refine ⟨1557254004757898298652709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1038169336505265532435139 1557254004757898298652709)
                    ·
                      refine ⟨291985125892105930997383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1557254004757898298652709 291985125892105930997383)
                      ·
                        rfl

theorem cell23_568639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_568639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568639 prefixEnd_568639 := by exact prefixLift 568639
  have htrace : WordTrace (prefixWord ++ tailWord_568639) baseStart_568639 baseEnd_568639 := by
    simpa [prefixWord, tailWord_568639, baseEnd_568639] using wordTrace_append hprefix tailTrace_568639
  have hstable : (prefixWord ++ tailWord_568639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568639).length < 2 ^ (prefixWord ++ tailWord_568639).sum := by decide
  have hdescent : baseEnd_568639 < baseStart_568639 := by decide
  rcases family_descends (prefixWord ++ tailWord_568639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568656 : List Nat := [2, 1, 1, 1, 1, 5, 1, 6, 1, 2, 2]
def baseStart_568656 : Nat := 118140960795 + 568656 * 2 ^ 59
def prefixEnd_568656 : Nat := 4983230072969 + 3 ^ 40 * 568656 * 2
def baseEnd_568656 : Nat := 291993855063232364484805

theorem tailTrace_568656 : CollatzResearch.WordTrace tailWord_568656 prefixEnd_568656 291993855063232364484805 := by
  unfold tailWord_568656
  simp only [CollatzResearch.WordTrace]
  refine ⟨10370294113931952778946911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13827058818575937038595881 10370294113931952778946911)
  ·
    refine ⟨15555441170897929168420367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10370294113931952778946911 15555441170897929168420367)
    ·
      refine ⟨23333161756346893752630551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15555441170897929168420367 23333161756346893752630551)
      ·
        refine ⟨34999742634520340628945827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23333161756346893752630551 34999742634520340628945827)
        ·
          refine ⟨52499613951780510943418741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34999742634520340628945827 52499613951780510943418741)
          ·
            refine ⟨4921838807979422900945507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52499613951780510943418741 4921838807979422900945507)
            ·
              refine ⟨7382758211969134351418261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4921838807979422900945507 7382758211969134351418261)
              ·
                refine ⟨346066791186053172722731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7382758211969134351418261 346066791186053172722731)
                ·
                  refine ⟨519100186779079759084097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346066791186053172722731 519100186779079759084097)
                  ·
                    refine ⟨389325140084309819313073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 519100186779079759084097 389325140084309819313073)
                    ·
                      refine ⟨291993855063232364484805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389325140084309819313073 291993855063232364484805)
                      ·
                        rfl

theorem cell23_568656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 2, 2].length) (baseStart_568656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568656 prefixEnd_568656 := by exact prefixLift 568656
  have htrace : WordTrace (prefixWord ++ tailWord_568656) baseStart_568656 baseEnd_568656 := by
    simpa [prefixWord, tailWord_568656, baseEnd_568656] using wordTrace_append hprefix tailTrace_568656
  have hstable : (prefixWord ++ tailWord_568656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568656).length < 2 ^ (prefixWord ++ tailWord_568656).sum := by decide
  have hdescent : baseEnd_568656 < baseStart_568656 := by decide
  rcases family_descends (prefixWord ++ tailWord_568656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568679 : List Nat := [1, 1, 5, 1, 4, 2, 2, 7]
def baseStart_568679 : Nat := 118140960795 + 568679 * 2 ^ 59
def prefixEnd_568679 : Nat := 4983230072969 + 3 ^ 40 * 568679 * 2
def baseEnd_568679 : Nat := 10815024634010584240637

theorem tailTrace_568679 : CollatzResearch.WordTrace tailWord_568679 prefixEnd_568679 10815024634010584240637 := by
  unfold tailWord_568679
  simp only [CollatzResearch.WordTrace]
  refine ⟨20741427106780580485981091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13827618071187053657320727 20741427106780580485981091)
  ·
    refine ⟨31112140660170870728971637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20741427106780580485981091 31112140660170870728971637)
    ·
      refine ⟨2916763186891019130841091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31112140660170870728971637 2916763186891019130841091)
      ·
        refine ⟨4375144780336528696261637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916763186891019130841091 4375144780336528696261637)
        ·
          refine ⟨820339646313099130549057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4375144780336528696261637 820339646313099130549057)
          ·
            refine ⟨615254734734824347911793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 820339646313099130549057 615254734734824347911793)
            ·
              refine ⟨461441051051118260933845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615254734734824347911793 461441051051118260933845)
              ·
                refine ⟨10815024634010584240637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 461441051051118260933845 10815024634010584240637)
                ·
                  rfl

theorem cell23_568679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 7].length) (baseStart_568679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568679 prefixEnd_568679 := by exact prefixLift 568679
  have htrace : WordTrace (prefixWord ++ tailWord_568679) baseStart_568679 baseEnd_568679 := by
    simpa [prefixWord, tailWord_568679, baseEnd_568679] using wordTrace_append hprefix tailTrace_568679
  have hstable : (prefixWord ++ tailWord_568679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568679).length < 2 ^ (prefixWord ++ tailWord_568679).sum := by decide
  have hdescent : baseEnd_568679 < baseStart_568679 := by decide
  rcases family_descends (prefixWord ++ tailWord_568679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568699 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 1, 3, 2]
def baseStart_568699 : Nat := 118140960795 + 568699 * 2 ^ 59
def prefixEnd_568699 : Nat := 4983230072969 + 3 ^ 40 * 568699 * 2
def baseEnd_568699 : Nat := 292015934731375696247107

theorem tailTrace_568699 : CollatzResearch.WordTrace tailWord_568699 prefixEnd_568699 292015934731375696247107 := by
  unfold tailWord_568699
  simp only [CollatzResearch.WordTrace]
  refine ⟨20742156566708123901709151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13828104377805415934472767 20742156566708123901709151)
  ·
    refine ⟨31113234850062185852563727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20742156566708123901709151 31113234850062185852563727)
    ·
      refine ⟨46669852275093278778845591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31113234850062185852563727 46669852275093278778845591)
      ·
        refine ⟨70004778412639918168268387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46669852275093278778845591 70004778412639918168268387)
        ·
          refine ⟨105007167618959877252402581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70004778412639918168268387 105007167618959877252402581)
          ·
            refine ⟨4922210982138744246206371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105007167618959877252402581 4922210982138744246206371)
            ·
              refine ⟨7383316473208116369309557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922210982138744246206371 7383316473208116369309557)
              ·
                refine ⟨692185919363260909622771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7383316473208116369309557 692185919363260909622771)
                ·
                  refine ⟨1038278879044891364434157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692185919363260909622771 1038278879044891364434157)
                  ·
                    refine ⟨389354579641834261662809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1038278879044891364434157 389354579641834261662809)
                    ·
                      refine ⟨292015934731375696247107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389354579641834261662809 292015934731375696247107)
                      ·
                        rfl

theorem cell23_568699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 3, 2].length) (baseStart_568699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568699 prefixEnd_568699 := by exact prefixLift 568699
  have htrace : WordTrace (prefixWord ++ tailWord_568699) baseStart_568699 baseEnd_568699 := by
    simpa [prefixWord, tailWord_568699, baseEnd_568699] using wordTrace_append hprefix tailTrace_568699
  have hstable : (prefixWord ++ tailWord_568699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568699).length < 2 ^ (prefixWord ++ tailWord_568699).sum := by decide
  have hdescent : baseEnd_568699 < baseStart_568699 := by decide
  rcases family_descends (prefixWord ++ tailWord_568699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568715 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 5]
def baseStart_568715 : Nat := 118140960795 + 568715 * 2 ^ 59
def prefixEnd_568715 : Nat := 4983230072969 + 3 ^ 40 * 568715 * 2
def baseEnd_568715 : Nat := 292024150421847633647033

theorem tailTrace_568715 : CollatzResearch.WordTrace tailWord_568715 prefixEnd_568715 292024150421847633647033 := by
  unfold tailWord_568715
  simp only [CollatzResearch.WordTrace]
  refine ⟨20742740134650158634291599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13828493423100105756194399 20742740134650158634291599)
  ·
    refine ⟨31114110201975237951437399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20742740134650158634291599 31114110201975237951437399)
    ·
      refine ⟨46671165302962856927156099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31114110201975237951437399 46671165302962856927156099)
      ·
        refine ⟨70006747954444285390734149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46671165302962856927156099 70006747954444285390734149)
        ·
          refine ⟨13126265241458303510762653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70006747954444285390734149 13126265241458303510762653)
          ·
            refine ⟨4922349465546863816535995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13126265241458303510762653 4922349465546863816535995)
            ·
              refine ⟨7383524198320295724803993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922349465546863816535995 7383524198320295724803993)
              ·
                refine ⟨5537643148740221793602995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7383524198320295724803993 5537643148740221793602995)
                ·
                  refine ⟨8306464723110332690404493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5537643148740221793602995 8306464723110332690404493)
                  ·
                    refine ⟨3114924271166374758901685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8306464723110332690404493 3114924271166374758901685)
                    ·
                      refine ⟨292024150421847633647033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3114924271166374758901685 292024150421847633647033)
                      ·
                        rfl

theorem cell23_568715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_568715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568715 prefixEnd_568715 := by exact prefixLift 568715
  have htrace : WordTrace (prefixWord ++ tailWord_568715) baseStart_568715 baseEnd_568715 := by
    simpa [prefixWord, tailWord_568715, baseEnd_568715] using wordTrace_append hprefix tailTrace_568715
  have hstable : (prefixWord ++ tailWord_568715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568715).length < 2 ^ (prefixWord ++ tailWord_568715).sum := by decide
  have hdescent : baseEnd_568715 < baseStart_568715 := by decide
  rcases family_descends (prefixWord ++ tailWord_568715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568733 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_568733 : Nat := 118140960795 + 568733 * 2 ^ 59
def prefixEnd_568733 : Nat := 4983230072969 + 3 ^ 40 * 568733 * 2
def baseEnd_568733 : Nat := 292033393073628563221951

theorem tailTrace_568733 : CollatzResearch.WordTrace tailWord_568733 prefixEnd_568733 292033393073628563221951 := by
  unfold tailWord_568733
  simp only [CollatzResearch.WordTrace]
  refine ⟨20743396648584947708446853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13828931099056631805631235 20743396648584947708446853)
  ·
    refine ⟨3889386871609677695333785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20743396648584947708446853 3889386871609677695333785)
    ·
      refine ⟨2917040153707258271500339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3889386871609677695333785 2917040153707258271500339)
      ·
        refine ⟨4375560230560887407250509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2917040153707258271500339 4375560230560887407250509)
        ·
          refine ⟨1640835086460332777718941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4375560230560887407250509 1640835086460332777718941)
          ·
            refine ⟨615313157422624791644603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1640835086460332777718941 615313157422624791644603)
            ·
              refine ⟨922969736133937187466905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615313157422624791644603 922969736133937187466905)
              ·
                refine ⟨692227302100452890600179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922969736133937187466905 692227302100452890600179)
                ·
                  refine ⟨1038340953150679335900269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692227302100452890600179 1038340953150679335900269)
                  ·
                    refine ⟨389377857431504750962601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1038340953150679335900269 389377857431504750962601)
                    ·
                      refine ⟨292033393073628563221951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389377857431504750962601 292033393073628563221951)
                      ·
                        rfl

theorem cell23_568733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_568733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568733 prefixEnd_568733 := by exact prefixLift 568733
  have htrace : WordTrace (prefixWord ++ tailWord_568733) baseStart_568733 baseEnd_568733 := by
    simpa [prefixWord, tailWord_568733, baseEnd_568733] using wordTrace_append hprefix tailTrace_568733
  have hstable : (prefixWord ++ tailWord_568733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568733).length < 2 ^ (prefixWord ++ tailWord_568733).sum := by decide
  have hdescent : baseEnd_568733 < baseStart_568733 := by decide
  rcases family_descends (prefixWord ++ tailWord_568733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568749 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_568749 : Nat := 118140960795 + 568749 * 2 ^ 59
def prefixEnd_568749 : Nat := 4983230072969 + 3 ^ 40 * 568749 * 2
def baseEnd_568749 : Nat := 292041608764100500621877

theorem tailTrace_568749 : CollatzResearch.WordTrace tailWord_568749 prefixEnd_568749 292041608764100500621877 := by
  unfold tailWord_568749
  simp only [CollatzResearch.WordTrace]
  refine ⟨20743980216526982441029301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13829320144351321627352867 20743980216526982441029301)
  ·
    refine ⟨1944748145299404603846497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20743980216526982441029301 1944748145299404603846497)
    ·
      refine ⟨1458561108974553452884873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1944748145299404603846497 1458561108974553452884873)
      ·
        refine ⟨1093920831730915089663655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1458561108974553452884873 1093920831730915089663655)
        ·
          refine ⟨1640881247596372634495483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093920831730915089663655 1640881247596372634495483)
          ·
            refine ⟨2461321871394558951743225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640881247596372634495483 2461321871394558951743225)
            ·
              refine ⟨1845991403545919213807419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2461321871394558951743225 1845991403545919213807419)
              ·
                refine ⟨2768987105318878820711129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845991403545919213807419 2768987105318878820711129)
                ·
                  refine ⟨2076740328989159115533347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2768987105318878820711129 2076740328989159115533347)
                  ·
                    refine ⟨3115110493483738673300021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2076740328989159115533347 3115110493483738673300021)
                    ·
                      refine ⟨292041608764100500621877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3115110493483738673300021 292041608764100500621877)
                      ·
                        rfl

theorem cell23_568749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_568749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568749 prefixEnd_568749 := by exact prefixLift 568749
  have htrace : WordTrace (prefixWord ++ tailWord_568749) baseStart_568749 baseEnd_568749 := by
    simpa [prefixWord, tailWord_568749, baseEnd_568749] using wordTrace_append hprefix tailTrace_568749
  have hstable : (prefixWord ++ tailWord_568749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568749).length < 2 ^ (prefixWord ++ tailWord_568749).sum := by decide
  have hdescent : baseEnd_568749 < baseStart_568749 := by decide
  rcases family_descends (prefixWord ++ tailWord_568749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568782 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_568782 : Nat := 118140960795 + 568782 * 2 ^ 59
def prefixEnd_568782 : Nat := 4983230072969 + 3 ^ 40 * 568782 * 2
def baseEnd_568782 : Nat := 97352851208566290503075

theorem tailTrace_568782 : CollatzResearch.WordTrace tailWord_568782 prefixEnd_568782 97352851208566290503075 := by
  unfold tailWord_568782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2593147978175928634622575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13830122550271619384653733 2593147978175928634622575)
  ·
    refine ⟨3889721967263892951933863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2593147978175928634622575 3889721967263892951933863)
    ·
      refine ⟨5834582950895839427900795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3889721967263892951933863 5834582950895839427900795)
      ·
        refine ⟨8751874426343759141851193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5834582950895839427900795 8751874426343759141851193)
        ·
          refine ⟨6563905819757819356388395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8751874426343759141851193 6563905819757819356388395)
          ·
            refine ⟨9845858729636729034582593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6563905819757819356388395 9845858729636729034582593)
            ·
              refine ⟨7384394047227546775936945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9845858729636729034582593 7384394047227546775936945)
              ·
                refine ⟨5538295535420660081952709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7384394047227546775936945 5538295535420660081952709)
                ·
                  refine ⟨1038430412891373765366133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5538295535420660081952709 1038430412891373765366133)
                  ·
                    refine ⟨97352851208566290503075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1038430412891373765366133 97352851208566290503075)
                    ·
                      rfl

theorem cell23_568782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_568782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568782 prefixEnd_568782 := by exact prefixLift 568782
  have htrace : WordTrace (prefixWord ++ tailWord_568782) baseStart_568782 baseEnd_568782 := by
    simpa [prefixWord, tailWord_568782, baseEnd_568782] using wordTrace_append hprefix tailTrace_568782
  have hstable : (prefixWord ++ tailWord_568782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568782).length < 2 ^ (prefixWord ++ tailWord_568782).sum := by decide
  have hdescent : baseEnd_568782 < baseStart_568782 := by decide
  rcases family_descends (prefixWord ++ tailWord_568782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568789 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_568789 : Nat := 118140960795 + 568789 * 2 ^ 59
def prefixEnd_568789 : Nat := 4983230072969 + 3 ^ 40 * 568789 * 2
def baseEnd_568789 : Nat := 292062147990280344121693

theorem tailTrace_568789 : CollatzResearch.WordTrace tailWord_568789 prefixEnd_568789 292062147990280344121693 := by
  unfold tailWord_568789
  simp only [CollatzResearch.WordTrace]
  refine ⟨20745439136382069272485421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13830292757588046181656947 20745439136382069272485421)
  ·
    refine ⟨7779539676143275977182033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20745439136382069272485421 7779539676143275977182033)
    ·
      refine ⟨5834654757107456982886525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7779539676143275977182033 5834654757107456982886525)
      ·
        refine ⟨2187995533915296368582447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5834654757107456982886525 2187995533915296368582447)
        ·
          refine ⟨3281993300872944552873671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2187995533915296368582447 3281993300872944552873671)
          ·
            refine ⟨4922989951309416829310507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3281993300872944552873671 4922989951309416829310507)
            ·
              refine ⟨7384484926964125243965761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4922989951309416829310507 7384484926964125243965761)
              ·
                refine ⟨5538363695223093932974321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7384484926964125243965761 5538363695223093932974321)
                ·
                  refine ⟨4153772771417320449730741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5538363695223093932974321 4153772771417320449730741)
                  ·
                    refine ⟨389416197320373792162257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4153772771417320449730741 389416197320373792162257)
                    ·
                      refine ⟨292062147990280344121693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389416197320373792162257 292062147990280344121693)
                      ·
                        rfl

theorem cell23_568789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_568789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568789 prefixEnd_568789 := by exact prefixLift 568789
  have htrace : WordTrace (prefixWord ++ tailWord_568789) baseStart_568789 baseEnd_568789 := by
    simpa [prefixWord, tailWord_568789, baseEnd_568789] using wordTrace_append hprefix tailTrace_568789
  have hstable : (prefixWord ++ tailWord_568789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568789).length < 2 ^ (prefixWord ++ tailWord_568789).sum := by decide
  have hdescent : baseEnd_568789 < baseStart_568789 := by decide
  rcases family_descends (prefixWord ++ tailWord_568789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568795 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 6, 8]
def baseStart_568795 : Nat := 118140960795 + 568795 * 2 ^ 59
def prefixEnd_568795 : Nat := 4983230072969 + 3 ^ 40 * 568795 * 2
def baseEnd_568795 : Nat := 97355076291402440215555

theorem tailTrace_568795 : CollatzResearch.WordTrace tailWord_568795 prefixEnd_568795 97355076291402440215555 := by
  unfold tailWord_568795
  simp only [CollatzResearch.WordTrace]
  refine ⟨20745657974360332297203839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13830438649573554864802559 20745657974360332297203839)
  ·
    refine ⟨31118486961540498445805759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20745657974360332297203839 31118486961540498445805759)
    ·
      refine ⟨46677730442310747668708639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31118486961540498445805759 46677730442310747668708639)
      ·
        refine ⟨70016595663466121503062959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46677730442310747668708639 70016595663466121503062959)
        ·
          refine ⟨105024893495199182254594439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70016595663466121503062959 105024893495199182254594439)
          ·
            refine ⟨157537340242798773381891659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105024893495199182254594439 157537340242798773381891659)
            ·
              refine ⟨236306010364198160072837489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157537340242798773381891659 236306010364198160072837489)
              ·
                refine ⟨177229507773148620054628117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236306010364198160072837489 177229507773148620054628117)
                ·
                  refine ⟨8307633176866341565060693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 177229507773148620054628117 8307633176866341565060693)
                  ·
                    refine ⟨97355076291402440215555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8307633176866341565060693 97355076291402440215555)
                    ·
                      rfl

theorem cell23_568795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 8].length) (baseStart_568795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568795 prefixEnd_568795 := by exact prefixLift 568795
  have htrace : WordTrace (prefixWord ++ tailWord_568795) baseStart_568795 baseEnd_568795 := by
    simpa [prefixWord, tailWord_568795, baseEnd_568795] using wordTrace_append hprefix tailTrace_568795
  have hstable : (prefixWord ++ tailWord_568795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568795).length < 2 ^ (prefixWord ++ tailWord_568795).sum := by decide
  have hdescent : baseEnd_568795 < baseStart_568795 := by decide
  rcases family_descends (prefixWord ++ tailWord_568795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568829 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_568829 : Nat := 118140960795 + 568829 * 2 ^ 59
def prefixEnd_568829 : Nat := 4983230072969 + 3 ^ 40 * 568829 * 2
def baseEnd_568829 : Nat := 97360895738820062540503

theorem tailTrace_568829 : CollatzResearch.WordTrace tailWord_568829 prefixEnd_568829 97360895738820062540503 := by
  unfold tailWord_568829
  simp only [CollatzResearch.WordTrace]
  refine ⟨20746898056237156103941541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13831265370824770735961027 20746898056237156103941541)
  ·
    refine ⟨3890043385544466769489039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20746898056237156103941541 3890043385544466769489039)
    ·
      refine ⟨5835065078316700154233559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890043385544466769489039 5835065078316700154233559)
      ·
        refine ⟨8752597617475050231350339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5835065078316700154233559 8752597617475050231350339)
        ·
          refine ⟨13128896426212575347025509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8752597617475050231350339 13128896426212575347025509)
          ·
            refine ⟨2461668079914857877567283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13128896426212575347025509 2461668079914857877567283)
            ·
              refine ⟨3692502119872286816350925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2461668079914857877567283 3692502119872286816350925)
              ·
                refine ⟨1384688294952107556131597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3692502119872286816350925 1384688294952107556131597)
                ·
                  refine ⟨519258110607040333549349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1384688294952107556131597 519258110607040333549349)
                  ·
                    refine ⟨97360895738820062540503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 519258110607040333549349 97360895738820062540503)
                    ·
                      rfl

theorem cell23_568829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_568829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568829 prefixEnd_568829 := by exact prefixLift 568829
  have htrace : WordTrace (prefixWord ++ tailWord_568829) baseStart_568829 baseEnd_568829 := by
    simpa [prefixWord, tailWord_568829, baseEnd_568829] using wordTrace_append hprefix tailTrace_568829
  have hstable : (prefixWord ++ tailWord_568829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568829).length < 2 ^ (prefixWord ++ tailWord_568829).sum := by decide
  have hdescent : baseEnd_568829 < baseStart_568829 := by decide
  rcases family_descends (prefixWord ++ tailWord_568829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568839 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_568839 : Nat := 118140960795 + 568839 * 2 ^ 59
def prefixEnd_568839 : Nat := 4983230072969 + 3 ^ 40 * 568839 * 2
def baseEnd_568839 : Nat := 292087822023005148496463

theorem tailTrace_568839 : CollatzResearch.WordTrace tailWord_568839 prefixEnd_568839 292087822023005148496463 := by
  unfold tailWord_568839
  simp only [CollatzResearch.WordTrace]
  refine ⟨20747262786200927811805571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13831508524133951874537047 20747262786200927811805571)
  ·
    refine ⟨31120894179301391717708357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20747262786200927811805571 31120894179301391717708357)
    ·
      refine ⟨5835167658619010947070317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31120894179301391717708357 5835167658619010947070317)
      ·
        refine ⟨2188187871982129105151369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5835167658619010947070317 2188187871982129105151369)
        ·
          refine ⟨1641140903986596828863527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188187871982129105151369 1641140903986596828863527)
          ·
            refine ⟨2461711355979895243295291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641140903986596828863527 2461711355979895243295291)
            ·
              refine ⟨3692567033969842864942937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2461711355979895243295291 3692567033969842864942937)
              ·
                refine ⟨2769425275477382148707203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3692567033969842864942937 2769425275477382148707203)
                ·
                  refine ⟨4154137913216073223060805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2769425275477382148707203 4154137913216073223060805)
                  ·
                    refine ⟨778900858728013729323901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4154137913216073223060805 778900858728013729323901)
                    ·
                      refine ⟨292087822023005148496463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 778900858728013729323901 292087822023005148496463)
                      ·
                        rfl

theorem cell23_568839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_568839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568839 prefixEnd_568839 := by exact prefixLift 568839
  have htrace : WordTrace (prefixWord ++ tailWord_568839) baseStart_568839 baseEnd_568839 := by
    simpa [prefixWord, tailWord_568839, baseEnd_568839] using wordTrace_append hprefix tailTrace_568839
  have hstable : (prefixWord ++ tailWord_568839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568839).length < 2 ^ (prefixWord ++ tailWord_568839).sum := by decide
  have hdescent : baseEnd_568839 < baseStart_568839 := by decide
  rcases family_descends (prefixWord ++ tailWord_568839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568882 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_568882 : Nat := 118140960795 + 568882 * 2 ^ 59
def prefixEnd_568882 : Nat := 4983230072969 + 3 ^ 40 * 568882 * 2
def baseEnd_568882 : Nat := 292109901691148480258765

theorem tailTrace_568882 : CollatzResearch.WordTrace tailWord_568882 prefixEnd_568882 292109901691148480258765 := by
  unfold tailWord_568882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5187207781261286538905225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13832554083363430770413933 5187207781261286538905225)
  ·
    refine ⟨3890405835945964904178919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5187207781261286538905225 3890405835945964904178919)
    ·
      refine ⟨5835608753918947356268379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890405835945964904178919 5835608753918947356268379)
      ·
        refine ⟨8753413130878421034402569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5835608753918947356268379 8753413130878421034402569)
        ·
          refine ⟨6565059848158815775801927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8753413130878421034402569 6565059848158815775801927)
          ·
            refine ⟨9847589772238223663702891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565059848158815775801927 9847589772238223663702891)
            ·
              refine ⟨14771384658357335495554337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9847589772238223663702891 14771384658357335495554337)
              ·
                refine ⟨11078538493768001621665753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14771384658357335495554337 11078538493768001621665753)
                ·
                  refine ⟨8308903870326001216249315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11078538493768001621665753 8308903870326001216249315)
                  ·
                    refine ⟨12463355805489001824373973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8308903870326001216249315 12463355805489001824373973)
                    ·
                      refine ⟨292109901691148480258765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12463355805489001824373973 292109901691148480258765)
                      ·
                        rfl

theorem cell23_568882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_568882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568882 prefixEnd_568882 := by exact prefixLift 568882
  have htrace : WordTrace (prefixWord ++ tailWord_568882) baseStart_568882 baseEnd_568882 := by
    simpa [prefixWord, tailWord_568882, baseEnd_568882] using wordTrace_append hprefix tailTrace_568882
  have hstable : (prefixWord ++ tailWord_568882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568882).length < 2 ^ (prefixWord ++ tailWord_568882).sum := by decide
  have hdescent : baseEnd_568882 < baseStart_568882 := by decide
  rcases family_descends (prefixWord ++ tailWord_568882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568893 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 6]
def baseStart_568893 : Nat := 118140960795 + 568893 * 2 ^ 59
def prefixEnd_568893 : Nat := 4983230072969 + 3 ^ 40 * 568893 * 2
def baseEnd_568893 : Nat := 32457283330927548580135

theorem tailTrace_568893 : CollatzResearch.WordTrace tailWord_568893 prefixEnd_568893 32457283330927548580135 := by
  unfold tailWord_568893
  simp only [CollatzResearch.WordTrace]
  refine ⟨20749232328005295034271333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13832821552003530022847555 20749232328005295034271333)
  ·
    refine ⟨3890481061500992818925875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20749232328005295034271333 3890481061500992818925875)
    ·
      refine ⟨5835721592251489228388813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890481061500992818925875 5835721592251489228388813)
      ·
        refine ⟨2188395597094308460645805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5835721592251489228388813 2188395597094308460645805)
        ·
          refine ⟨820648348910365672742177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2188395597094308460645805 820648348910365672742177)
          ·
            refine ⟨615486261682774254556633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 820648348910365672742177 615486261682774254556633)
            ·
              refine ⟨461614696262080690917475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615486261682774254556633 461614696262080690917475)
              ·
                refine ⟨692422044393121036376213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 461614696262080690917475 692422044393121036376213)
                ·
                  refine ⟨32457283330927548580135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 692422044393121036376213 32457283330927548580135)
                  ·
                    rfl

theorem cell23_568893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_568893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568893 prefixEnd_568893 := by exact prefixLift 568893
  have htrace : WordTrace (prefixWord ++ tailWord_568893) baseStart_568893 baseEnd_568893 := by
    simpa [prefixWord, tailWord_568893, baseEnd_568893] using wordTrace_append hprefix tailTrace_568893
  have hstable : (prefixWord ++ tailWord_568893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568893).length < 2 ^ (prefixWord ++ tailWord_568893).sum := by decide
  have hdescent : baseEnd_568893 < baseStart_568893 := by decide
  rcases family_descends (prefixWord ++ tailWord_568893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568919 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 1, 6]
def baseStart_568919 : Nat := 118140960795 + 568919 * 2 ^ 59
def prefixEnd_568919 : Nat := 4983230072969 + 3 ^ 40 * 568919 * 2
def baseEnd_568919 : Nat := 97376300158454945165365

theorem tailTrace_568919 : CollatzResearch.WordTrace tailWord_568919 prefixEnd_568919 97376300158454945165365 := by
  unfold tailWord_568919
  simp only [CollatzResearch.WordTrace]
  refine ⟨20750180625911101474717811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13833453750607400983145207 20750180625911101474717811)
  ·
    refine ⟨31125270938866652212076717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20750180625911101474717811 31125270938866652212076717)
    ·
      refine ⟨11671976602074994579528769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31125270938866652212076717 11671976602074994579528769)
      ·
        refine ⟨8753982451556245934646577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11671976602074994579528769 8753982451556245934646577)
        ·
          refine ⟨6565486838667184450984933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8753982451556245934646577 6565486838667184450984933)
          ·
            refine ⟨1231028782250097084559675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6565486838667184450984933 1231028782250097084559675)
            ·
              refine ⟨1846543173375145626839513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231028782250097084559675 1846543173375145626839513)
              ·
                refine ⟨1384907380031359220129635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846543173375145626839513 1384907380031359220129635)
                ·
                  refine ⟨2077361070047038830194453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1384907380031359220129635 2077361070047038830194453)
                  ·
                    refine ⟨97376300158454945165365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2077361070047038830194453 97376300158454945165365)
                    ·
                      rfl

theorem cell23_568919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_568919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568919 prefixEnd_568919 := by exact prefixLift 568919
  have htrace : WordTrace (prefixWord ++ tailWord_568919) baseStart_568919 baseEnd_568919 := by
    simpa [prefixWord, tailWord_568919, baseEnd_568919] using wordTrace_append hprefix tailTrace_568919
  have hstable : (prefixWord ++ tailWord_568919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568919).length < 2 ^ (prefixWord ++ tailWord_568919).sum := by decide
  have hdescent : baseEnd_568919 < baseStart_568919 := by decide
  rcases family_descends (prefixWord ++ tailWord_568919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568932 : List Nat := [2, 3, 1, 1, 2, 14]
def baseStart_568932 : Nat := 118140960795 + 568932 * 2 ^ 59
def prefixEnd_568932 : Nat := 4983230072969 + 3 ^ 40 * 568932 * 2
def baseEnd_568932 : Nat := 1202204015324581418245

theorem tailTrace_568932 : CollatzResearch.WordTrace tailWord_568932 prefixEnd_568932 1202204015324581418245 := by
  unfold tailWord_568932
  simp only [CollatzResearch.WordTrace]
  refine ⟨10375327387432002347470525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13833769849909336463294033 10375327387432002347470525)
  ·
    refine ⟨3890747770287000880301447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10375327387432002347470525 3890747770287000880301447)
    ·
      refine ⟨5836121655430501320452171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890747770287000880301447 5836121655430501320452171)
      ·
        refine ⟨8754182483145751980678257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5836121655430501320452171 8754182483145751980678257)
        ·
          refine ⟨6565636862359313985508693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8754182483145751980678257 6565636862359313985508693)
          ·
            refine ⟨1202204015324581418245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 6565636862359313985508693 1202204015324581418245)
            ·
              rfl

theorem cell23_568932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 14].length) (baseStart_568932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568932 prefixEnd_568932 := by exact prefixLift 568932
  have htrace : WordTrace (prefixWord ++ tailWord_568932) baseStart_568932 baseEnd_568932 := by
    simpa [prefixWord, tailWord_568932, baseEnd_568932] using wordTrace_append hprefix tailTrace_568932
  have hstable : (prefixWord ++ tailWord_568932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568932).length < 2 ^ (prefixWord ++ tailWord_568932).sum := by decide
  have hdescent : baseEnd_568932 < baseStart_568932 := by decide
  rcases family_descends (prefixWord ++ tailWord_568932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568946 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_568946 : Nat := 118140960795 + 568946 * 2 ^ 59
def prefixEnd_568946 : Nat := 4983230072969 + 3 ^ 40 * 568946 * 2
def baseEnd_568946 : Nat := 292142764453036229858471

theorem tailTrace_568946 : CollatzResearch.WordTrace tailWord_568946 prefixEnd_568946 292142764453036229858471 := by
  unfold tailWord_568946
  simp only [CollatzResearch.WordTrace]
  refine ⟨5187791349203321271487673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13834110264542190057300461 5187791349203321271487673)
  ·
    refine ⟨3890843511902490953615755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5187791349203321271487673 3890843511902490953615755)
    ·
      refine ⟨5836265267853736430423633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3890843511902490953615755 5836265267853736430423633)
      ·
        refine ⟨4377198950890302322817725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5836265267853736430423633 4377198950890302322817725)
        ·
          refine ⟨1641449606583863371056647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4377198950890302322817725 1641449606583863371056647)
          ·
            refine ⟨2462174409875795056584971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641449606583863371056647 2462174409875795056584971)
            ·
              refine ⟨3693261614813692584877457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462174409875795056584971 3693261614813692584877457)
              ·
                refine ⟨2769946211110269438658093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3693261614813692584877457 2769946211110269438658093)
                ·
                  refine ⟨1038729829166351039496785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2769946211110269438658093 1038729829166351039496785)
                  ·
                    refine ⟨779047371874763279622589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1038729829166351039496785 779047371874763279622589)
                    ·
                      refine ⟨292142764453036229858471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 779047371874763279622589 292142764453036229858471)
                      ·
                        rfl

theorem cell23_568946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_568946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568946 prefixEnd_568946 := by exact prefixLift 568946
  have htrace : WordTrace (prefixWord ++ tailWord_568946) baseStart_568946 baseEnd_568946 := by
    simpa [prefixWord, tailWord_568946, baseEnd_568946] using wordTrace_append hprefix tailTrace_568946
  have hstable : (prefixWord ++ tailWord_568946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568946).length < 2 ^ (prefixWord ++ tailWord_568946).sum := by decide
  have hdescent : baseEnd_568946 < baseStart_568946 := by decide
  rcases family_descends (prefixWord ++ tailWord_568946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568980 : List Nat := [2, 4, 2, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_568980 : Nat := 118140960795 + 568980 * 2 ^ 59
def prefixEnd_568980 : Nat := 4983230072969 + 3 ^ 40 * 568980 * 2
def baseEnd_568980 : Nat := 292160222795289096833315

theorem tailTrace_568980 : CollatzResearch.WordTrace tailWord_568980 prefixEnd_568980 292160222795289096833315 := by
  unfold tailWord_568980
  simp only [CollatzResearch.WordTrace]
  refine ⟨10376202739345054446344197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13834936985793405928458929 10376202739345054446344197)
  ·
    refine ⟨1945538013627197708689537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10376202739345054446344197 1945538013627197708689537)
    ·
      refine ⟨1459153510220398281517153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1945538013627197708689537 1459153510220398281517153)
      ·
        refine ⟨1094365132665298711137865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1459153510220398281517153 1094365132665298711137865)
        ·
          refine ⟨820773849498974033353399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1094365132665298711137865 820773849498974033353399)
          ·
            refine ⟨1231160774248461050030099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820773849498974033353399 1231160774248461050030099)
            ·
              refine ⟨1846741161372691575045149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231160774248461050030099 1846741161372691575045149)
              ·
                refine ⟨692527935514759340641931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1846741161372691575045149 692527935514759340641931)
                ·
                  refine ⟨1038791903272139010962897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692527935514759340641931 1038791903272139010962897)
                  ·
                    refine ⟨779093927454104258222173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1038791903272139010962897 779093927454104258222173)
                    ·
                      refine ⟨292160222795289096833315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 779093927454104258222173 292160222795289096833315)
                      ·
                        rfl

theorem cell23_568980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_568980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568980 prefixEnd_568980 := by exact prefixLift 568980
  have htrace : WordTrace (prefixWord ++ tailWord_568980) baseStart_568980 baseEnd_568980 := by
    simpa [prefixWord, tailWord_568980, baseEnd_568980] using wordTrace_append hprefix tailTrace_568980
  have hstable : (prefixWord ++ tailWord_568980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568980).length < 2 ^ (prefixWord ++ tailWord_568980).sum := by decide
  have hdescent : baseEnd_568980 < baseStart_568980 := by decide
  rcases family_descends (prefixWord ++ tailWord_568980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_568993 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 3]
def baseStart_568993 : Nat := 118140960795 + 568993 * 2 ^ 59
def prefixEnd_568993 : Nat := 4983230072969 + 3 ^ 40 * 568993 * 2
def baseEnd_568993 : Nat := 292166898043797545970755

theorem tailTrace_568993 : CollatzResearch.WordTrace tailWord_568993 prefixEnd_568993 292166898043797545970755 := by
  unfold tailWord_568993
  simp only [CollatzResearch.WordTrace]
  refine ⟨20752879627643012112911633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13835253085095341408607755 20752879627643012112911633)
  ·
    refine ⟨15564659720732259084683725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20752879627643012112911633 15564659720732259084683725)
    ·
      refine ⟨5836747395274597156756397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15564659720732259084683725 5836747395274597156756397)
      ·
        refine ⟨2188780273227973933783649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5836747395274597156756397 2188780273227973933783649)
        ·
          refine ⟨1641585204920980450337737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188780273227973933783649 1641585204920980450337737)
          ·
            refine ⟨1231188903690735337753303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641585204920980450337737 1231188903690735337753303)
            ·
              refine ⟨1846783355536103006629955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231188903690735337753303 1846783355536103006629955)
              ·
                refine ⟨2770175033304154509944933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1846783355536103006629955 2770175033304154509944933)
                ·
                  refine ⟨519407818744528970614675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2770175033304154509944933 519407818744528970614675)
                  ·
                    refine ⟨779111728116793455922013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 519407818744528970614675 779111728116793455922013)
                    ·
                      refine ⟨292166898043797545970755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 779111728116793455922013 292166898043797545970755)
                      ·
                        rfl

theorem cell23_568993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_568993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_568993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_568993 prefixEnd_568993 := by exact prefixLift 568993
  have htrace : WordTrace (prefixWord ++ tailWord_568993) baseStart_568993 baseEnd_568993 := by
    simpa [prefixWord, tailWord_568993, baseEnd_568993] using wordTrace_append hprefix tailTrace_568993
  have hstable : (prefixWord ++ tailWord_568993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_568993).length < 2 ^ (prefixWord ++ tailWord_568993).sum := by decide
  have hdescent : baseEnd_568993 < baseStart_568993 := by decide
  rcases family_descends (prefixWord ++ tailWord_568993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569019 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 3]
def baseStart_569019 : Nat := 118140960795 + 569019 * 2 ^ 59
def prefixEnd_569019 : Nat := 4983230072969 + 3 ^ 40 * 569019 * 2
def baseEnd_569019 : Nat := 292180248540814444245635

theorem tailTrace_569019 : CollatzResearch.WordTrace tailWord_569019 prefixEnd_569019 292180248540814444245635 := by
  unfold tailWord_569019
  simp only [CollatzResearch.WordTrace]
  refine ⟨20753827925548818553358111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13835885283699212368905407 20753827925548818553358111)
  ·
    refine ⟨31130741888323227830037167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20753827925548818553358111 31130741888323227830037167)
    ·
      refine ⟨46696112832484841745055751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31130741888323227830037167 46696112832484841745055751)
      ·
        refine ⟨70044169248727262617583627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46696112832484841745055751 70044169248727262617583627)
        ·
          refine ⟨105066253873090893926375441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70044169248727262617583627 105066253873090893926375441)
          ·
            refine ⟨78799690404818170444781581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105066253873090893926375441 78799690404818170444781581)
            ·
              refine ⟨29549883901806813916793093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78799690404818170444781581 29549883901806813916793093)
              ·
                refine ⟨5540603231588777609398705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29549883901806813916793093 5540603231588777609398705)
                ·
                  refine ⟨4155452423691583207049029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5540603231588777609398705 4155452423691583207049029)
                  ·
                    refine ⟨779147329442171851321693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4155452423691583207049029 779147329442171851321693)
                    ·
                      refine ⟨292180248540814444245635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 779147329442171851321693 292180248540814444245635)
                      ·
                        rfl

theorem cell23_569019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 3].length) (baseStart_569019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569019 prefixEnd_569019 := by exact prefixLift 569019
  have htrace : WordTrace (prefixWord ++ tailWord_569019) baseStart_569019 baseEnd_569019 := by
    simpa [prefixWord, tailWord_569019, baseEnd_569019] using wordTrace_append hprefix tailTrace_569019
  have hstable : (prefixWord ++ tailWord_569019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569019).length < 2 ^ (prefixWord ++ tailWord_569019).sum := by decide
  have hdescent : baseEnd_569019 < baseStart_569019 := by decide
  rcases family_descends (prefixWord ++ tailWord_569019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569020 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_569020 : Nat := 118140960795 + 569020 * 2 ^ 59
def prefixEnd_569020 : Nat := 4983230072969 + 3 ^ 40 * 569020 * 2
def baseEnd_569020 : Nat := 292180762021468940333131

theorem tailTrace_569020 : CollatzResearch.WordTrace tailWord_569020 prefixEnd_569020 292180762021468940333131 := by
  unfold tailWord_569020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10376932199272597862072257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13835909599030130482763009 10376932199272597862072257)
  ·
    refine ⟨7782699149454448396554193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10376932199272597862072257 7782699149454448396554193)
    ·
      refine ⟨5837024362090836297415645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7782699149454448396554193 5837024362090836297415645)
      ·
        refine ⟨2188884135784063611530867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5837024362090836297415645 2188884135784063611530867)
        ·
          refine ⟨3283326203676095417296301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188884135784063611530867 3283326203676095417296301)
          ·
            refine ⟨1231247326378535781486113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3283326203676095417296301 1231247326378535781486113)
            ·
              refine ⟨923435494783901836114585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231247326378535781486113 923435494783901836114585)
              ·
                refine ⟨692576621087926377085939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923435494783901836114585 692576621087926377085939)
                ·
                  refine ⟨1038864931631889565628909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692576621087926377085939 1038864931631889565628909)
                  ·
                    refine ⟨389574349361958587110841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1038864931631889565628909 389574349361958587110841)
                    ·
                      refine ⟨292180762021468940333131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389574349361958587110841 292180762021468940333131)
                      ·
                        rfl

theorem cell23_569020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_569020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569020 prefixEnd_569020 := by exact prefixLift 569020
  have htrace : WordTrace (prefixWord ++ tailWord_569020) baseStart_569020 baseEnd_569020 := by
    simpa [prefixWord, tailWord_569020, baseEnd_569020] using wordTrace_append hprefix tailTrace_569020
  have hstable : (prefixWord ++ tailWord_569020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569020).length < 2 ^ (prefixWord ++ tailWord_569020).sum := by decide
  have hdescent : baseEnd_569020 < baseStart_569020 := by decide
  rcases family_descends (prefixWord ++ tailWord_569020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569037 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_569037 : Nat := 118140960795 + 569037 * 2 ^ 59
def prefixEnd_569037 : Nat := 4983230072969 + 3 ^ 40 * 569037 * 2
def baseEnd_569037 : Nat := 292189491192595373820553

theorem tailTrace_569037 : CollatzResearch.WordTrace tailWord_569037 prefixEnd_569037 292189491192595373820553 := by
  unfold tailWord_569037
  simp only [CollatzResearch.WordTrace]
  refine ⟨20754484439483607627513365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13836322959655738418342243 20754484439483607627513365)
  ·
    refine ⟨972866458100794107539689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20754484439483607627513365 972866458100794107539689)
    ·
      refine ⟨729649843575595580654767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 972866458100794107539689 729649843575595580654767)
      ·
        refine ⟨1094474765363393370982151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 729649843575595580654767 1094474765363393370982151)
        ·
          refine ⟨1641712148045090056473227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094474765363393370982151 1641712148045090056473227)
          ·
            refine ⟨2462568222067635084709841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641712148045090056473227 2462568222067635084709841)
            ·
              refine ⟨1846926166550726313532381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462568222067635084709841 1846926166550726313532381)
              ·
                refine ⟨692597312456522367574643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1846926166550726313532381 692597312456522367574643)
                ·
                  refine ⟨1038895968684783551361965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692597312456522367574643 1038895968684783551361965)
                  ·
                    refine ⟨389585988256793831760737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1038895968684783551361965 389585988256793831760737)
                    ·
                      refine ⟨292189491192595373820553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389585988256793831760737 292189491192595373820553)
                      ·
                        rfl

theorem cell23_569037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_569037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569037 prefixEnd_569037 := by exact prefixLift 569037
  have htrace : WordTrace (prefixWord ++ tailWord_569037) baseStart_569037 baseEnd_569037 := by
    simpa [prefixWord, tailWord_569037, baseEnd_569037] using wordTrace_append hprefix tailTrace_569037
  have hstable : (prefixWord ++ tailWord_569037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569037).length < 2 ^ (prefixWord ++ tailWord_569037).sum := by decide
  have hdescent : baseEnd_569037 < baseStart_569037 := by decide
  rcases family_descends (prefixWord ++ tailWord_569037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569056 : List Nat := [2, 1, 1, 3, 1, 2, 2, 6, 5]
def baseStart_569056 : Nat := 118140960795 + 569056 * 2 ^ 59
def prefixEnd_569056 : Nat := 4983230072969 + 3 ^ 40 * 569056 * 2
def baseEnd_569056 : Nat := 32466583036114533275885

theorem tailTrace_569056 : CollatzResearch.WordTrace tailWord_569056 prefixEnd_569056 32466583036114533275885 := by
  unfold tailWord_569056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10377588713207386936227511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13836784950943182581636681 10377588713207386936227511)
  ·
    refine ⟨15566383069811080404341267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10377588713207386936227511 15566383069811080404341267)
    ·
      refine ⟨23349574604716620606511901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15566383069811080404341267 23349574604716620606511901)
      ·
        refine ⟨8756090476768732727441963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23349574604716620606511901 8756090476768732727441963)
        ·
          refine ⟨13134135715153099091162945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8756090476768732727441963 13134135715153099091162945)
          ·
            refine ⟨9850601786364824318372209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13134135715153099091162945 9850601786364824318372209)
            ·
              refine ⟨7387951339773618238779157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9850601786364824318372209 7387951339773618238779157)
              ·
                refine ⟨346310219051888354942773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7387951339773618238779157 346310219051888354942773)
                ·
                  refine ⟨32466583036114533275885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 346310219051888354942773 32466583036114533275885)
                  ·
                    rfl

theorem cell23_569056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 5].length) (baseStart_569056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569056 prefixEnd_569056 := by exact prefixLift 569056
  have htrace : WordTrace (prefixWord ++ tailWord_569056) baseStart_569056 baseEnd_569056 := by
    simpa [prefixWord, tailWord_569056, baseEnd_569056] using wordTrace_append hprefix tailTrace_569056
  have hstable : (prefixWord ++ tailWord_569056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569056).length < 2 ^ (prefixWord ++ tailWord_569056).sum := by decide
  have hdescent : baseEnd_569056 < baseStart_569056 := by decide
  rcases family_descends (prefixWord ++ tailWord_569056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569066 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_569066 : Nat := 118140960795 + 569066 * 2 ^ 59
def prefixEnd_569066 : Nat := 4983230072969 + 3 ^ 40 * 569066 * 2
def baseEnd_569066 : Nat := 292204382131575760357919

theorem tailTrace_569066 : CollatzResearch.WordTrace tailWord_569066 prefixEnd_569066 292204382131575760357919 := by
  unfold tailWord_569066
  simp only [CollatzResearch.WordTrace]
  refine ⟨5188885539094636395079763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13837028104252363720212701 5188885539094636395079763)
  ·
    refine ⟨7783328308641954592619645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5188885539094636395079763 7783328308641954592619645)
    ·
      refine ⟨2918748115740732972232367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7783328308641954592619645 2918748115740732972232367)
      ·
        refine ⟨4378122173611099458348551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918748115740732972232367 4378122173611099458348551)
        ·
          refine ⟨6567183260416649187522827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4378122173611099458348551 6567183260416649187522827)
          ·
            refine ⟨9850774890624973781284241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6567183260416649187522827 9850774890624973781284241)
            ·
              refine ⟨7388081167968730335963181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9850774890624973781284241 7388081167968730335963181)
              ·
                refine ⟨2770530437988273875986193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7388081167968730335963181 2770530437988273875986193)
                ·
                  refine ⟨2077897828491205406989645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2770530437988273875986193 2077897828491205406989645)
                  ·
                    refine ⟨779211685684202027621117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2077897828491205406989645 779211685684202027621117)
                    ·
                      refine ⟨292204382131575760357919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 779211685684202027621117 292204382131575760357919)
                      ·
                        rfl

theorem cell23_569066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_569066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569066 prefixEnd_569066 := by exact prefixLift 569066
  have htrace : WordTrace (prefixWord ++ tailWord_569066) baseStart_569066 baseEnd_569066 := by
    simpa [prefixWord, tailWord_569066, baseEnd_569066] using wordTrace_append hprefix tailTrace_569066
  have hstable : (prefixWord ++ tailWord_569066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569066).length < 2 ^ (prefixWord ++ tailWord_569066).sum := by decide
  have hdescent : baseEnd_569066 < baseStart_569066 := by decide
  rcases family_descends (prefixWord ++ tailWord_569066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569140 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_569140 : Nat := 118140960795 + 569140 * 2 ^ 59
def prefixEnd_569140 : Nat := 4983230072969 + 3 ^ 40 * 569140 * 2
def baseEnd_569140 : Nat := 292242379700008470832579

theorem tailTrace_569140 : CollatzResearch.WordTrace tailWord_569140 prefixEnd_569140 292242379700008470832579 := by
  unfold tailWord_569140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10379120579055228109256437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13838827438740304145675249 10379120579055228109256437)
  ·
    refine ⟨973042554286427635242791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10379120579055228109256437 973042554286427635242791)
    ·
      refine ⟨1459563831429641452864187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 973042554286427635242791 1459563831429641452864187)
      ·
        refine ⟨2189345747144462179296281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459563831429641452864187 2189345747144462179296281)
        ·
          refine ⟨1642009310358346634472211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2189345747144462179296281 1642009310358346634472211)
          ·
            refine ⟨2463013965537519951708317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642009310358346634472211 2463013965537519951708317)
            ·
              refine ⟨923630237076569981890619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2463013965537519951708317 923630237076569981890619)
              ·
                refine ⟨1385445355614854972835929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923630237076569981890619 1385445355614854972835929)
                ·
                  refine ⟨1039084016711141229626947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1385445355614854972835929 1039084016711141229626947)
                  ·
                    refine ⟨1558626025066711844440421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1039084016711141229626947 1558626025066711844440421)
                    ·
                      refine ⟨292242379700008470832579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1558626025066711844440421 292242379700008470832579)
                      ·
                        rfl

theorem cell23_569140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_569140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569140 prefixEnd_569140 := by exact prefixLift 569140
  have htrace : WordTrace (prefixWord ++ tailWord_569140) baseStart_569140 baseEnd_569140 := by
    simpa [prefixWord, tailWord_569140, baseEnd_569140] using wordTrace_append hprefix tailTrace_569140
  have hstable : (prefixWord ++ tailWord_569140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569140).length < 2 ^ (prefixWord ++ tailWord_569140).sum := by decide
  have hdescent : baseEnd_569140 < baseStart_569140 := by decide
  rcases family_descends (prefixWord ++ tailWord_569140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569183 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 1, 5, 2]
def baseStart_569183 : Nat := 118140960795 + 569183 * 2 ^ 59
def prefixEnd_569183 : Nat := 4983230072969 + 3 ^ 40 * 569183 * 2
def baseEnd_569183 : Nat := 292264459368151802594881

theorem tailTrace_569183 : CollatzResearch.WordTrace tailWord_569183 prefixEnd_569183 292264459368151802594881 := by
  unfold tailWord_569183
  simp only [CollatzResearch.WordTrace]
  refine ⟨20759809496954674562328203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13839872997969783041552135 20759809496954674562328203)
  ·
    refine ⟨31139714245432011843492305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20759809496954674562328203 31139714245432011843492305)
    ·
      refine ⟨23354785684074008882619229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31139714245432011843492305 23354785684074008882619229)
      ·
        refine ⟨8758044631527753330982211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23354785684074008882619229 8758044631527753330982211)
        ·
          refine ⟨13137066947291629996473317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8758044631527753330982211 13137066947291629996473317)
          ·
            refine ⟨2463200052617180624338747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13137066947291629996473317 2463200052617180624338747)
            ·
              refine ⟨3694800078925770936508121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2463200052617180624338747 3694800078925770936508121)
              ·
                refine ⟨2771100059194328202381091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3694800078925770936508121 2771100059194328202381091)
                ·
                  refine ⟨4156650088791492303571637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2771100059194328202381091 4156650088791492303571637)
                  ·
                    refine ⟨389685945824202403459841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4156650088791492303571637 389685945824202403459841)
                    ·
                      refine ⟨292264459368151802594881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389685945824202403459841 292264459368151802594881)
                      ·
                        rfl

theorem cell23_569183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_569183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569183 prefixEnd_569183 := by exact prefixLift 569183
  have htrace : WordTrace (prefixWord ++ tailWord_569183) baseStart_569183 baseEnd_569183 := by
    simpa [prefixWord, tailWord_569183, baseEnd_569183] using wordTrace_append hprefix tailTrace_569183
  have hstable : (prefixWord ++ tailWord_569183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569183).length < 2 ^ (prefixWord ++ tailWord_569183).sum := by decide
  have hdescent : baseEnd_569183 < baseStart_569183 := by decide
  rcases family_descends (prefixWord ++ tailWord_569183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569224 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_569224 : Nat := 118140960795 + 569224 * 2 ^ 59
def prefixEnd_569224 : Nat := 4983230072969 + 3 ^ 40 * 569224 * 2
def baseEnd_569224 : Nat := 292285512074986142182193

theorem tailTrace_569224 : CollatzResearch.WordTrace tailWord_569224 prefixEnd_569224 292285512074986142182193 := by
  unfold tailWord_569224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10380652444903069282285363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13840869926537425709713817 10380652444903069282285363)
  ·
    refine ⟨15570978667354603923428045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10380652444903069282285363 15570978667354603923428045)
    ·
      refine ⟨5839117000257976471285517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15570978667354603923428045 5839117000257976471285517)
      ·
        refine ⟨2189668875096741176732069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5839117000257976471285517 2189668875096741176732069)
        ·
          refine ⟨410562914080638970637263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2189668875096741176732069 410562914080638970637263)
          ·
            refine ⟨615844371120958455955895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 410562914080638970637263 615844371120958455955895)
            ·
              refine ⟨923766556681437683933843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615844371120958455955895 923766556681437683933843)
              ·
                refine ⟨1385649835022156525900765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923766556681437683933843 1385649835022156525900765)
                ·
                  refine ⟨519618688133308697212787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1385649835022156525900765 519618688133308697212787)
                  ·
                    refine ⟨779428032199963045819181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 519618688133308697212787 779428032199963045819181)
                    ·
                      refine ⟨292285512074986142182193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 779428032199963045819181 292285512074986142182193)
                      ·
                        rfl

theorem cell23_569224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_569224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569224 prefixEnd_569224 := by exact prefixLift 569224
  have htrace : WordTrace (prefixWord ++ tailWord_569224) baseStart_569224 baseEnd_569224 := by
    simpa [prefixWord, tailWord_569224, baseEnd_569224] using wordTrace_append hprefix tailTrace_569224
  have hstable : (prefixWord ++ tailWord_569224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569224).length < 2 ^ (prefixWord ++ tailWord_569224).sum := by decide
  have hdescent : baseEnd_569224 < baseStart_569224 := by decide
  rcases family_descends (prefixWord ++ tailWord_569224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569247 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 4]
def baseStart_569247 : Nat := 118140960795 + 569247 * 2 ^ 59
def prefixEnd_569247 : Nat := 4983230072969 + 3 ^ 40 * 569247 * 2
def baseEnd_569247 : Nat := 292297322130039552194587

theorem tailTrace_569247 : CollatzResearch.WordTrace tailWord_569247 prefixEnd_569247 292297322130039552194587 := by
  unfold tailWord_569247
  simp only [CollatzResearch.WordTrace]
  refine ⟨20762143768722813492657995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13841429179148542328438663 20762143768722813492657995)
  ·
    refine ⟨31143215653084220238986993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20762143768722813492657995 31143215653084220238986993)
    ·
      refine ⟨23357411739813165179240245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31143215653084220238986993 23357411739813165179240245)
      ·
        refine ⟨2189757350607484235553773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23357411739813165179240245 2189757350607484235553773)
        ·
          refine ⟨821159006477806588332665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2189757350607484235553773 821159006477806588332665)
          ·
            refine ⟨615869254858354941249499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821159006477806588332665 615869254858354941249499)
            ·
              refine ⟨923803882287532411874249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615869254858354941249499 923803882287532411874249)
              ·
                refine ⟨692852911715649308905687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923803882287532411874249 692852911715649308905687)
                ·
                  refine ⟨1039279367573473963358531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 692852911715649308905687 1039279367573473963358531)
                  ·
                    refine ⟨1558919051360210945037797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1039279367573473963358531 1558919051360210945037797)
                    ·
                      refine ⟨292297322130039552194587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1558919051360210945037797 292297322130039552194587)
                      ·
                        rfl

theorem cell23_569247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_569247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569247 prefixEnd_569247 := by exact prefixLift 569247
  have htrace : WordTrace (prefixWord ++ tailWord_569247) baseStart_569247 baseEnd_569247 := by
    simpa [prefixWord, tailWord_569247, baseEnd_569247] using wordTrace_append hprefix tailTrace_569247
  have hstable : (prefixWord ++ tailWord_569247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569247).length < 2 ^ (prefixWord ++ tailWord_569247).sum := by decide
  have hdescent : baseEnd_569247 < baseStart_569247 := by decide
  rcases family_descends (prefixWord ++ tailWord_569247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569263 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 3]
def baseStart_569263 : Nat := 118140960795 + 569263 * 2 ^ 59
def prefixEnd_569263 : Nat := 4983230072969 + 3 ^ 40 * 569263 * 2
def baseEnd_569263 : Nat := 292305537820511489594513

theorem tailTrace_569263 : CollatzResearch.WordTrace tailWord_569263 prefixEnd_569263 292305537820511489594513 := by
  unfold tailWord_569263
  simp only [CollatzResearch.WordTrace]
  refine ⟨20762727336664848225240443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13841818224443232150160295 20762727336664848225240443)
  ·
    refine ⟨31144091004997272337860665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20762727336664848225240443 31144091004997272337860665)
    ·
      refine ⟨23358068253747954253395499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31144091004997272337860665 23358068253747954253395499)
      ·
        refine ⟨35037102380621931380093249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23358068253747954253395499 35037102380621931380093249)
        ·
          refine ⟨26277826785466448535069937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35037102380621931380093249 26277826785466448535069937)
          ·
            refine ⟨19708370089099836401302453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26277826785466448535069937 19708370089099836401302453)
            ·
              refine ⟨1847659695853109662622105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19708370089099836401302453 1847659695853109662622105)
              ·
                refine ⟨1385744771889832246966579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1847659695853109662622105 1385744771889832246966579)
                ·
                  refine ⟨2078617157834748370449869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385744771889832246966579 2078617157834748370449869)
                  ·
                    refine ⟨779481434188030638918701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2078617157834748370449869 779481434188030638918701)
                    ·
                      refine ⟨292305537820511489594513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 779481434188030638918701 292305537820511489594513)
                      ·
                        rfl

theorem cell23_569263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_569263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569263 prefixEnd_569263 := by exact prefixLift 569263
  have htrace : WordTrace (prefixWord ++ tailWord_569263) baseStart_569263 baseEnd_569263 := by
    simpa [prefixWord, tailWord_569263, baseEnd_569263] using wordTrace_append hprefix tailTrace_569263
  have hstable : (prefixWord ++ tailWord_569263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569263).length < 2 ^ (prefixWord ++ tailWord_569263).sum := by decide
  have hdescent : baseEnd_569263 < baseStart_569263 := by decide
  rcases family_descends (prefixWord ++ tailWord_569263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569266 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 4, 7]
def baseStart_569266 : Nat := 118140960795 + 569266 * 2 ^ 59
def prefixEnd_569266 : Nat := 4983230072969 + 3 ^ 40 * 569266 * 2
def baseEnd_569266 : Nat := 97435692754158325952333

theorem tailTrace_569266 : CollatzResearch.WordTrace tailWord_569266 prefixEnd_569266 97435692754158325952333 := by
  unfold tailWord_569266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190709188913494934399913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13841891170435986491733101 5190709188913494934399913)
  ·
    refine ⟨3893031891685121200799935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5190709188913494934399913 3893031891685121200799935)
    ·
      refine ⟨5839547837527681801199903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3893031891685121200799935 5839547837527681801199903)
      ·
        refine ⟨8759321756291522701799855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5839547837527681801199903 8759321756291522701799855)
        ·
          refine ⟨13138982634437284052699783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8759321756291522701799855 13138982634437284052699783)
          ·
            refine ⟨19708473951655926079049675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13138982634437284052699783 19708473951655926079049675)
            ·
              refine ⟨29562710927483889118574513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19708473951655926079049675 29562710927483889118574513)
              ·
                refine ⟨22172033195612916838930885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29562710927483889118574513 22172033195612916838930885)
                ·
                  refine ⟨4157256224177421907299541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22172033195612916838930885 4157256224177421907299541)
                  ·
                    refine ⟨97435692754158325952333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4157256224177421907299541 97435692754158325952333)
                    ·
                      rfl

theorem cell23_569266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_569266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569266 prefixEnd_569266 := by exact prefixLift 569266
  have htrace : WordTrace (prefixWord ++ tailWord_569266) baseStart_569266 baseEnd_569266 := by
    simpa [prefixWord, tailWord_569266, baseEnd_569266] using wordTrace_append hprefix tailTrace_569266
  have hstable : (prefixWord ++ tailWord_569266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569266).length < 2 ^ (prefixWord ++ tailWord_569266).sum := by decide
  have hdescent : baseEnd_569266 < baseStart_569266 := by decide
  rcases family_descends (prefixWord ++ tailWord_569266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569290 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_569290 : Nat := 118140960795 + 569290 * 2 ^ 59
def prefixEnd_569290 : Nat := 4983230072969 + 3 ^ 40 * 569290 * 2
def baseEnd_569290 : Nat := 292319401798182883956889

theorem tailTrace_569290 : CollatzResearch.WordTrace tailWord_569290 prefixEnd_569290 292319401798182883956889 := by
  unfold tailWord_569290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5190928026891757959118331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13842474738378021224315549 5190928026891757959118331)
  ·
    refine ⟨7786392040337636938677497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5190928026891757959118331 7786392040337636938677497)
    ·
      refine ⟨5839794030253227704008123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7786392040337636938677497 5839794030253227704008123)
      ·
        refine ⟨8759691045379841556012185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5839794030253227704008123 8759691045379841556012185)
        ·
          refine ⟨6569768284034881167009139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8759691045379841556012185 6569768284034881167009139)
          ·
            refine ⟨9854652426052321750513709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6569768284034881167009139 9854652426052321750513709)
            ·
              refine ⟨3695494659769620656442641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9854652426052321750513709 3695494659769620656442641)
              ·
                refine ⟨2771620994827215492331981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3695494659769620656442641 2771620994827215492331981)
                ·
                  refine ⟨1039357873060205809624493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2771620994827215492331981 1039357873060205809624493)
                  ·
                    refine ⟨389759202397577178609185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1039357873060205809624493 389759202397577178609185)
                    ·
                      refine ⟨292319401798182883956889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389759202397577178609185 292319401798182883956889)
                      ·
                        rfl

theorem cell23_569290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_569290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569290 prefixEnd_569290 := by exact prefixLift 569290
  have htrace : WordTrace (prefixWord ++ tailWord_569290) baseStart_569290 baseEnd_569290 := by
    simpa [prefixWord, tailWord_569290, baseEnd_569290] using wordTrace_append hprefix tailTrace_569290
  have hstable : (prefixWord ++ tailWord_569290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569290).length < 2 ^ (prefixWord ++ tailWord_569290).sum := by decide
  have hdescent : baseEnd_569290 < baseStart_569290 := by decide
  rcases family_descends (prefixWord ++ tailWord_569290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569296 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 1, 8]
def baseStart_569296 : Nat := 118140960795 + 569296 * 2 ^ 59
def prefixEnd_569296 : Nat := 4983230072969 + 3 ^ 40 * 569296 * 2
def baseEnd_569296 : Nat := 97440827560703286827287

theorem tailTrace_569296 : CollatzResearch.WordTrace tailWord_569296 prefixEnd_569296 97440827560703286827287 := by
  unfold tailWord_569296
  simp only [CollatzResearch.WordTrace]
  refine ⟨10381965472772647430595871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13842620630363529907461161 10381965472772647430595871)
  ·
    refine ⟨15572948209158971145893807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10381965472772647430595871 15572948209158971145893807)
    ·
      refine ⟨23359422313738456718840711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15572948209158971145893807 23359422313738456718840711)
      ·
        refine ⟨35039133470607685078261067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23359422313738456718840711 35039133470607685078261067)
        ·
          refine ⟨52558700205911527617391601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35039133470607685078261067 52558700205911527617391601)
          ·
            refine ⟨39419025154433645713043701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52558700205911527617391601 39419025154433645713043701)
            ·
              refine ⟨3695533608228154285597847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39419025154433645713043701 3695533608228154285597847)
              ·
                refine ⟨5543300412342231428396771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3695533608228154285597847 5543300412342231428396771)
                ·
                  refine ⟨8314950618513347142595157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5543300412342231428396771 8314950618513347142595157)
                  ·
                    refine ⟨97440827560703286827287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8314950618513347142595157 97440827560703286827287)
                    ·
                      rfl

theorem cell23_569296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_569296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569296 prefixEnd_569296 := by exact prefixLift 569296
  have htrace : WordTrace (prefixWord ++ tailWord_569296) baseStart_569296 baseEnd_569296 := by
    simpa [prefixWord, tailWord_569296, baseEnd_569296] using wordTrace_append hprefix tailTrace_569296
  have hstable : (prefixWord ++ tailWord_569296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569296).length < 2 ^ (prefixWord ++ tailWord_569296).sum := by decide
  have hdescent : baseEnd_569296 < baseStart_569296 := by decide
  rcases family_descends (prefixWord ++ tailWord_569296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569337 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 4, 2, 2]
def baseStart_569337 : Nat := 118140960795 + 569337 * 2 ^ 59
def prefixEnd_569337 : Nat := 4983230072969 + 3 ^ 40 * 569337 * 2
def baseEnd_569337 : Nat := 292343535388944200069173

theorem tailTrace_569337 : CollatzResearch.WordTrace tailWord_569337 prefixEnd_569337 292343535388944200069173 := by
  unfold tailWord_569337
  simp only [CollatzResearch.WordTrace]
  refine ⟨20765426338396758863434265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13843617558931172575622843 20765426338396758863434265)
  ·
    refine ⟨15574069753797569147575699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20765426338396758863434265 15574069753797569147575699)
    ·
      refine ⟨23361104630696353721363549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15574069753797569147575699 23361104630696353721363549)
      ·
        refine ⟨8760414236511132645511331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23361104630696353721363549 8760414236511132645511331)
        ·
          refine ⟨13140621354766698968266997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8760414236511132645511331 13140621354766698968266997)
          ·
            refine ⟨1231933252009378028275031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13140621354766698968266997 1231933252009378028275031)
            ·
              refine ⟨1847899878014067042412547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231933252009378028275031 1847899878014067042412547)
              ·
                refine ⟨2771849817021100563618821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1847899878014067042412547 2771849817021100563618821)
                ·
                  refine ⟨519721840691456355678529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2771849817021100563618821 519721840691456355678529)
                  ·
                    refine ⟨389791380518592266758897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 519721840691456355678529 389791380518592266758897)
                    ·
                      refine ⟨292343535388944200069173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389791380518592266758897 292343535388944200069173)
                      ·
                        rfl

theorem cell23_569337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_569337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569337 prefixEnd_569337 := by exact prefixLift 569337
  have htrace : WordTrace (prefixWord ++ tailWord_569337) baseStart_569337 baseEnd_569337 := by
    simpa [prefixWord, tailWord_569337, baseEnd_569337] using wordTrace_append hprefix tailTrace_569337
  have hstable : (prefixWord ++ tailWord_569337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569337).length < 2 ^ (prefixWord ++ tailWord_569337).sum := by decide
  have hdescent : baseEnd_569337 < baseStart_569337 := by decide
  rcases family_descends (prefixWord ++ tailWord_569337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569354 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_569354 : Nat := 118140960795 + 569354 * 2 ^ 59
def prefixEnd_569354 : Nat := 4983230072969 + 3 ^ 40 * 569354 * 2
def baseEnd_569354 : Nat := 292352264560070633556595

theorem tailTrace_569354 : CollatzResearch.WordTrace tailWord_569354 prefixEnd_569354 292352264560070633556595 := by
  unfold tailWord_569354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5191511594833792691700779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13844030919556780511202077 5191511594833792691700779)
  ·
    refine ⟨7787267392250689037551169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5191511594833792691700779 7787267392250689037551169)
    ·
      refine ⟨5840450544188016778163377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7787267392250689037551169 5840450544188016778163377)
      ·
        refine ⟨4380337908141012583622533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5840450544188016778163377 4380337908141012583622533)
        ·
          refine ⟨821313357776439859429225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4380337908141012583622533 821313357776439859429225)
          ·
            refine ⟨615985018332329894571919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 821313357776439859429225 615985018332329894571919)
            ·
              refine ⟨923977527498494841857879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 615985018332329894571919 923977527498494841857879)
              ·
                refine ⟨1385966291247742262786819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923977527498494841857879 1385966291247742262786819)
                ·
                  refine ⟨2078949436871613394180229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1385966291247742262786819 2078949436871613394180229)
                  ·
                    refine ⟨389803019413427511408793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2078949436871613394180229 389803019413427511408793)
                    ·
                      refine ⟨292352264560070633556595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 389803019413427511408793 292352264560070633556595)
                      ·
                        rfl

theorem cell23_569354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_569354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569354 prefixEnd_569354 := by exact prefixLift 569354
  have htrace : WordTrace (prefixWord ++ tailWord_569354) baseStart_569354 baseEnd_569354 := by
    simpa [prefixWord, tailWord_569354, baseEnd_569354] using wordTrace_append hprefix tailTrace_569354
  have hstable : (prefixWord ++ tailWord_569354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569354).length < 2 ^ (prefixWord ++ tailWord_569354).sum := by decide
  have hdescent : baseEnd_569354 < baseStart_569354 := by decide
  rcases family_descends (prefixWord ++ tailWord_569354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569390 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_569390 : Nat := 118140960795 + 569390 * 2 ^ 59
def prefixEnd_569390 : Nat := 4983230072969 + 3 ^ 40 * 569390 * 2
def baseEnd_569390 : Nat := 97456916621210830902143

theorem tailTrace_569390 : CollatzResearch.WordTrace tailWord_569390 prefixEnd_569390 97456916621210830902143 := by
  unfold tailWord_569390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2595919925900593614389203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13844906271469832610075749 2595919925900593614389203)
  ·
    refine ⟨3893879888850890421583805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2595919925900593614389203 3893879888850890421583805)
    ·
      refine ⟨1460204958319083908093927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3893879888850890421583805 1460204958319083908093927)
      ·
        refine ⟨2190307437478625862140891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460204958319083908093927 2190307437478625862140891)
        ·
          refine ⟨3285461156217938793211337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190307437478625862140891 3285461156217938793211337)
          ·
            refine ⟨2464095867163454094908503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3285461156217938793211337 2464095867163454094908503)
            ·
              refine ⟨3696143800745181142362755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464095867163454094908503 3696143800745181142362755)
              ·
                refine ⟨5544215701117771713544133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696143800745181142362755 5544215701117771713544133)
                ·
                  refine ⟨1039540443959582196289525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5544215701117771713544133 1039540443959582196289525)
                  ·
                    refine ⟨97456916621210830902143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1039540443959582196289525 97456916621210830902143)
                    ·
                      rfl

theorem cell23_569390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_569390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569390 prefixEnd_569390 := by exact prefixLift 569390
  have htrace : WordTrace (prefixWord ++ tailWord_569390) baseStart_569390 baseEnd_569390 := by
    simpa [prefixWord, tailWord_569390, baseEnd_569390] using wordTrace_append hprefix tailTrace_569390
  have hstable : (prefixWord ++ tailWord_569390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569390).length < 2 ^ (prefixWord ++ tailWord_569390).sum := by decide
  have hdescent : baseEnd_569390 < baseStart_569390 := by decide
  rcases family_descends (prefixWord ++ tailWord_569390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569400 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_569400 : Nat := 118140960795 + 569400 * 2 ^ 59
def prefixEnd_569400 : Nat := 4983230072969 + 3 ^ 40 * 569400 * 2
def baseEnd_569400 : Nat := 292375884670177453581383

theorem tailTrace_569400 : CollatzResearch.WordTrace tailWord_569400 prefixEnd_569400 292375884670177453581383 := by
  unfold tailWord_569400
  simp only [CollatzResearch.WordTrace]
  refine ⟨10383862068584260311488827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13845149424779013748651769 10383862068584260311488827)
  ·
    refine ⟨15575793102876390467233241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10383862068584260311488827 15575793102876390467233241)
    ·
      refine ⟨11681844827157292850424931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15575793102876390467233241 11681844827157292850424931)
      ·
        refine ⟨17522767240735939275637397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11681844827157292850424931 17522767240735939275637397)
        ·
          refine ⟨821379714409497153545503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17522767240735939275637397 821379714409497153545503)
          ·
            refine ⟨1232069571614245730318255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821379714409497153545503 1232069571614245730318255)
            ·
              refine ⟨1848104357421368595477383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232069571614245730318255 1848104357421368595477383)
              ·
                refine ⟨2772156536132052893216075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848104357421368595477383 2772156536132052893216075)
                ·
                  refine ⟨4158234804198079339824113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2772156536132052893216075 4158234804198079339824113)
                  ·
                    refine ⟨3118676103148559504868085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4158234804198079339824113 3118676103148559504868085)
                    ·
                      refine ⟨292375884670177453581383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3118676103148559504868085 292375884670177453581383)
                      ·
                        rfl

theorem cell23_569400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_569400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569400 prefixEnd_569400 := by exact prefixLift 569400
  have htrace : WordTrace (prefixWord ++ tailWord_569400) baseStart_569400 baseEnd_569400 := by
    simpa [prefixWord, tailWord_569400, baseEnd_569400] using wordTrace_append hprefix tailTrace_569400
  have hstable : (prefixWord ++ tailWord_569400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569400).length < 2 ^ (prefixWord ++ tailWord_569400).sum := by decide
  have hdescent : baseEnd_569400 < baseStart_569400 := by decide
  rcases family_descends (prefixWord ++ tailWord_569400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569420 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_569420 : Nat := 118140960795 + 569420 * 2 ^ 59
def prefixEnd_569420 : Nat := 4983230072969 + 3 ^ 40 * 569420 * 2
def baseEnd_569420 : Nat := 97462051427755791777097

theorem tailTrace_569420 : CollatzResearch.WordTrace tailWord_569420 prefixEnd_569420 97462051427755791777097 := by
  unfold tailWord_569420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10384226798548032019352857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13845635731397376025803809 10384226798548032019352857)
  ·
    refine ⟨7788170098911024014514643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10384226798548032019352857 7788170098911024014514643)
    ·
      refine ⟨11682255148366536021771965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7788170098911024014514643 11682255148366536021771965)
      ·
        refine ⟨4380845680637451008164487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11682255148366536021771965 4380845680637451008164487)
        ·
          refine ⟨6571268520956176512246731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4380845680637451008164487 6571268520956176512246731)
          ·
            refine ⟨9856902781434264768370097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6571268520956176512246731 9856902781434264768370097)
            ·
              refine ⟨7392677086075698576277573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9856902781434264768370097 7392677086075698576277573)
              ·
                refine ⟨1386126953639193483052045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7392677086075698576277573 1386126953639193483052045)
                ·
                  refine ⟨519797607614697556144517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1386126953639193483052045 519797607614697556144517)
                  ·
                    refine ⟨97462051427755791777097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 519797607614697556144517 97462051427755791777097)
                    ·
                      rfl

theorem cell23_569420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_569420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569420 prefixEnd_569420 := by exact prefixLift 569420
  have htrace : WordTrace (prefixWord ++ tailWord_569420) baseStart_569420 baseEnd_569420 := by
    simpa [prefixWord, tailWord_569420, baseEnd_569420] using wordTrace_append hprefix tailTrace_569420
  have hstable : (prefixWord ++ tailWord_569420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569420).length < 2 ^ (prefixWord ++ tailWord_569420).sum := by decide
  have hdescent : baseEnd_569420 < baseStart_569420 := by decide
  rcases family_descends (prefixWord ++ tailWord_569420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569454 : List Nat := [4, 1, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_569454 : Nat := 118140960795 + 569454 * 2 ^ 59
def prefixEnd_569454 : Nat := 4983230072969 + 3 ^ 40 * 569454 * 2
def baseEnd_569454 : Nat := 97467870875173414102045

theorem tailTrace_569454 : CollatzResearch.WordTrace tailWord_569454 prefixEnd_569454 97467870875173414102045 := by
  unfold tailWord_569454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2596211709871610980680427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13846462452648591896962277 2596211709871610980680427)
  ·
    refine ⟨3894317564807416471020641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2596211709871610980680427 3894317564807416471020641)
    ·
      refine ⟨2920738173605562353265481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3894317564807416471020641 2920738173605562353265481)
      ·
        refine ⟨2190553630204171764949111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2920738173605562353265481 2190553630204171764949111)
        ·
          refine ⟨3285830445306257647423667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190553630204171764949111 3285830445306257647423667)
          ·
            refine ⟨4928745667959386471135501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3285830445306257647423667 4928745667959386471135501)
            ·
              refine ⟨1848279625484769926675813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4928745667959386471135501 1848279625484769926675813)
              ·
                refine ⟨346552429778394361251715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1848279625484769926675813 346552429778394361251715)
                ·
                  refine ⟨519828644667591541877573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 346552429778394361251715 519828644667591541877573)
                  ·
                    refine ⟨97467870875173414102045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 519828644667591541877573 97467870875173414102045)
                    ·
                      rfl

theorem cell23_569454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_569454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569454 prefixEnd_569454 := by exact prefixLift 569454
  have htrace : WordTrace (prefixWord ++ tailWord_569454) baseStart_569454 baseEnd_569454 := by
    simpa [prefixWord, tailWord_569454, baseEnd_569454] using wordTrace_append hprefix tailTrace_569454
  have hstable : (prefixWord ++ tailWord_569454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569454).length < 2 ^ (prefixWord ++ tailWord_569454).sum := by decide
  have hdescent : baseEnd_569454 < baseStart_569454 := by decide
  rcases family_descends (prefixWord ++ tailWord_569454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569477 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 3]
def baseStart_569477 : Nat := 118140960795 + 569477 * 2 ^ 59
def prefixEnd_569477 : Nat := 4983230072969 + 3 ^ 40 * 569477 * 2
def baseEnd_569477 : Nat := 292415422680573652318529

theorem tailTrace_569477 : CollatzResearch.WordTrace tailWord_569477 prefixEnd_569477 292415422680573652318529 := by
  unfold tailWord_569477
  simp only [CollatzResearch.WordTrace]
  refine ⟨20770532557889562773530685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13847021705259708515687123 20770532557889562773530685)
  ·
    refine ⟨7788949709208586040074007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20770532557889562773530685 7788949709208586040074007)
    ·
      refine ⟨11683424563812879060111011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7788949709208586040074007 11683424563812879060111011)
      ·
        refine ⟨17525136845719318590166517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11683424563812879060111011 17525136845719318590166517)
        ·
          refine ⟨1642981579286186117828111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17525136845719318590166517 1642981579286186117828111)
          ·
            refine ⟨2464472368929279176742167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1642981579286186117828111 2464472368929279176742167)
            ·
              refine ⟨3696708553393918765113251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464472368929279176742167 3696708553393918765113251)
              ·
                refine ⟨5545062830090878147669877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696708553393918765113251 5545062830090878147669877)
                ·
                  refine ⟨519849640321019826344051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5545062830090878147669877 519849640321019826344051)
                  ·
                    refine ⟨779774460481529739516077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 519849640321019826344051 779774460481529739516077)
                    ·
                      refine ⟨292415422680573652318529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 779774460481529739516077 292415422680573652318529)
                      ·
                        rfl

theorem cell23_569477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_569477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569477 prefixEnd_569477 := by exact prefixLift 569477
  have htrace : WordTrace (prefixWord ++ tailWord_569477) baseStart_569477 baseEnd_569477 := by
    simpa [prefixWord, tailWord_569477, baseEnd_569477] using wordTrace_append hprefix tailTrace_569477
  have hstable : (prefixWord ++ tailWord_569477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569477).length < 2 ^ (prefixWord ++ tailWord_569477).sum := by decide
  have hdescent : baseEnd_569477 < baseStart_569477 := by decide
  rcases family_descends (prefixWord ++ tailWord_569477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569511 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_569511 : Nat := 118140960795 + 569511 * 2 ^ 59
def prefixEnd_569511 : Nat := 4983230072969 + 3 ^ 40 * 569511 * 2
def baseEnd_569511 : Nat := 292432881022826519293373

theorem tailTrace_569511 : CollatzResearch.WordTrace tailWord_569511 prefixEnd_569511 292432881022826519293373 := by
  unfold tailWord_569511
  simp only [CollatzResearch.WordTrace]
  refine ⟨20771772639766386580268387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13847848426510924386845591 20771772639766386580268387)
  ·
    refine ⟨31157658959649579870402581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20771772639766386580268387 31157658959649579870402581)
    ·
      refine ⟨1460515263733574056425121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31157658959649579870402581 1460515263733574056425121)
      ·
        refine ⟨1095386447800180542318841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1460515263733574056425121 1095386447800180542318841)
        ·
          refine ⟨821539835850135406739131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095386447800180542318841 821539835850135406739131)
          ·
            refine ⟨1232309753775203110108697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821539835850135406739131 1232309753775203110108697)
            ·
              refine ⟨924232315331402332581523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232309753775203110108697 924232315331402332581523)
              ·
                refine ⟨1386348472997103498872285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924232315331402332581523 1386348472997103498872285)
                ·
                  refine ⟨519880677373913812077107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1386348472997103498872285 519880677373913812077107)
                  ·
                    refine ⟨779821016060870718115661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 519880677373913812077107 779821016060870718115661)
                    ·
                      refine ⟨292432881022826519293373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 779821016060870718115661 292432881022826519293373)
                      ·
                        rfl

theorem cell23_569511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_569511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569511 prefixEnd_569511 := by exact prefixLift 569511
  have htrace : WordTrace (prefixWord ++ tailWord_569511) baseStart_569511 baseEnd_569511 := by
    simpa [prefixWord, tailWord_569511, baseEnd_569511] using wordTrace_append hprefix tailTrace_569511
  have hstable : (prefixWord ++ tailWord_569511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569511).length < 2 ^ (prefixWord ++ tailWord_569511).sum := by decide
  have hdescent : baseEnd_569511 < baseStart_569511 := by decide
  rcases family_descends (prefixWord ++ tailWord_569511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569523 : List Nat := [1, 1, 1, 2, 3, 2, 1, 12]
def baseStart_569523 : Nat := 118140960795 + 569523 * 2 ^ 59
def prefixEnd_569523 : Nat := 4983230072969 + 3 ^ 40 * 569523 * 2
def baseEnd_569523 : Nat := 10831075658914091568271

theorem tailTrace_569523 : CollatzResearch.WordTrace tailWord_569523 prefixEnd_569523 10831075658914091568271 := by
  unfold tailWord_569523
  simp only [CollatzResearch.WordTrace]
  refine ⟨20772210315722912629705223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13848140210481941753136815 20772210315722912629705223)
  ·
    refine ⟨31158315473584368944557835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20772210315722912629705223 31158315473584368944557835)
    ·
      refine ⟨46737473210376553416836753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31158315473584368944557835 46737473210376553416836753)
      ·
        refine ⟨35053104907782415062627565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46737473210376553416836753 35053104907782415062627565)
        ·
          refine ⟨13144914340418405648485337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35053104907782415062627565 13144914340418405648485337)
          ·
            refine ⟨9858685755313804236364003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13144914340418405648485337 9858685755313804236364003)
            ·
              refine ⟨14788028632970706354546005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9858685755313804236364003 14788028632970706354546005)
              ·
                refine ⟨10831075658914091568271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 14788028632970706354546005 10831075658914091568271)
                ·
                  rfl

theorem cell23_569523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 12].length) (baseStart_569523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569523 prefixEnd_569523 := by exact prefixLift 569523
  have htrace : WordTrace (prefixWord ++ tailWord_569523) baseStart_569523 baseEnd_569523 := by
    simpa [prefixWord, tailWord_569523, baseEnd_569523] using wordTrace_append hprefix tailTrace_569523
  have hstable : (prefixWord ++ tailWord_569523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569523).length < 2 ^ (prefixWord ++ tailWord_569523).sum := by decide
  have hdescent : baseEnd_569523 < baseStart_569523 := by decide
  rcases family_descends (prefixWord ++ tailWord_569523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569527 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 1, 6]
def baseStart_569527 : Nat := 118140960795 + 569527 * 2 ^ 59
def prefixEnd_569527 : Nat := 4983230072969 + 3 ^ 40 * 569527 * 2
def baseEnd_569527 : Nat := 97480365571099485564433

theorem tailTrace_569527 : CollatzResearch.WordTrace tailWord_569527 prefixEnd_569527 97480365571099485564433 := by
  unfold tailWord_569527
  simp only [CollatzResearch.WordTrace]
  refine ⟨20772356207708421312850835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13848237471805614208567223 20772356207708421312850835)
  ·
    refine ⟨31158534311562631969276253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20772356207708421312850835 31158534311562631969276253)
    ·
      refine ⟨11684450366835986988478595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31158534311562631969276253 11684450366835986988478595)
      ·
        refine ⟨17526675550253980482717893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11684450366835986988478595 17526675550253980482717893)
        ·
          refine ⟨3286251665672621340509605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17526675550253980482717893 3286251665672621340509605)
          ·
            refine ⟨616172187313616501345551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3286251665672621340509605 616172187313616501345551)
            ·
              refine ⟨924258280970424752018327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 616172187313616501345551 924258280970424752018327)
              ·
                refine ⟨1386387421455637128027491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924258280970424752018327 1386387421455637128027491)
                ·
                  refine ⟨2079581132183455692041237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1386387421455637128027491 2079581132183455692041237)
                  ·
                    refine ⟨97480365571099485564433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2079581132183455692041237 97480365571099485564433)
                    ·
                      rfl

theorem cell23_569527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_569527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569527 prefixEnd_569527 := by exact prefixLift 569527
  have htrace : WordTrace (prefixWord ++ tailWord_569527) baseStart_569527 baseEnd_569527 := by
    simpa [prefixWord, tailWord_569527, baseEnd_569527] using wordTrace_append hprefix tailTrace_569527
  have hstable : (prefixWord ++ tailWord_569527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569527).length < 2 ^ (prefixWord ++ tailWord_569527).sum := by decide
  have hdescent : baseEnd_569527 < baseStart_569527 := by decide
  rcases family_descends (prefixWord ++ tailWord_569527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_569554 : List Nat := [3, 2, 2, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_569554 : Nat := 118140960795 + 569554 * 2 ^ 59
def prefixEnd_569554 : Nat := 4983230072969 + 3 ^ 40 * 569554 * 2
def baseEnd_569554 : Nat := 292454960690969851055675

theorem tailTrace_569554 : CollatzResearch.WordTrace tailWord_569554 prefixEnd_569554 292454960690969851055675 := by
  unfold tailWord_569554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193335244652651231020929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13848893985740403282722477 5193335244652651231020929)
  ·
    refine ⟨3895001433489488423265697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5193335244652651231020929 3895001433489488423265697)
    ·
      refine ⟨2921251075117116317449273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3895001433489488423265697 2921251075117116317449273)
      ·
        refine ⟨2190938306337837238086955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2921251075117116317449273 2190938306337837238086955)
        ·
          refine ⟨3286407459506755857130433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190938306337837238086955 3286407459506755857130433)
          ·
            refine ⟨2464805594630066892847825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3286407459506755857130433 2464805594630066892847825)
            ·
              refine ⟨1848604195972550169635869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2464805594630066892847825 1848604195972550169635869)
              ·
                refine ⟨693226573489706313613451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1848604195972550169635869 693226573489706313613451)
                ·
                  refine ⟨1039839860234559470420177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 693226573489706313613451 1039839860234559470420177)
                  ·
                    refine ⟨779879895175919602815133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1039839860234559470420177 779879895175919602815133)
                    ·
                      refine ⟨292454960690969851055675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 779879895175919602815133 292454960690969851055675)
                      ·
                        rfl

theorem cell23_569554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_569554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_569554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_569554 prefixEnd_569554 := by exact prefixLift 569554
  have htrace : WordTrace (prefixWord ++ tailWord_569554) baseStart_569554 baseEnd_569554 := by
    simpa [prefixWord, tailWord_569554, baseEnd_569554] using wordTrace_append hprefix tailTrace_569554
  have hstable : (prefixWord ++ tailWord_569554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_569554).length < 2 ^ (prefixWord ++ tailWord_569554).sum := by decide
  have hdescent : baseEnd_569554 < baseStart_569554 := by decide
  rcases family_descends (prefixWord ++ tailWord_569554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
