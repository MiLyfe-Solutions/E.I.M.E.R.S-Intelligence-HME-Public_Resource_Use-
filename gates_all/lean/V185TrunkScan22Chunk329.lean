import V185TrunkScan22Chunk328

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2934903 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 3, 5]
def baseStart_2934903 : Nat := 118140960795 + 2934903 * 2 ^ 59
def prefixEnd_2934903 : Nat := 4983230072969 + 3 ^ 40 * 2934903 * 2
def baseEnd_2934903 : Nat := 1004677275548423941476755

theorem tailTrace_2934903 : CollatzResearch.WordTrace tailWord_2934903 prefixEnd_2934903 1004677275548423941476755 := by
  unfold tailWord_2934903
  simp only [CollatzResearch.WordTrace]
  refine ⟨107044706486355147371633363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71363137657570098247755575 107044706486355147371633363)
  ·
    refine ⟨160567059729532721057450045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107044706486355147371633363 160567059729532721057450045)
    ·
      refine ⟨60212647398574770396543767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160567059729532721057450045 60212647398574770396543767)
      ·
        refine ⟨90318971097862155594815651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60212647398574770396543767 90318971097862155594815651)
        ·
          refine ⟨135478456646793233392223477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90318971097862155594815651 135478456646793233392223477)
          ·
            refine ⟨12701105310636865630520951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135478456646793233392223477 12701105310636865630520951)
            ·
              refine ⟨19051657965955298445781427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12701105310636865630520951 19051657965955298445781427)
              ·
                refine ⟨28577486948932947668672141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19051657965955298445781427 28577486948932947668672141)
                ·
                  refine ⟨10716557605849855375752053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28577486948932947668672141 10716557605849855375752053)
                  ·
                    refine ⟨1004677275548423941476755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10716557605849855375752053 1004677275548423941476755)
                    ·
                      rfl

theorem cell22_2934903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_2934903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934903 prefixEnd_2934903 := by exact prefixLift 2934903
  have htrace : WordTrace (prefixWord ++ tailWord_2934903) baseStart_2934903 baseEnd_2934903 := by
    simpa [prefixWord, tailWord_2934903, baseEnd_2934903] using wordTrace_append hprefix tailTrace_2934903
  have hstable : (prefixWord ++ tailWord_2934903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934903).length < 2 ^ (prefixWord ++ tailWord_2934903).sum := by decide
  have hdescent : baseEnd_2934903 < baseStart_2934903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934922 : List Nat := [3, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_2934922 : Nat := 118140960795 + 2934922 * 2 ^ 59
def prefixEnd_2934922 : Nat := 4983230072969 + 3 ^ 40 * 2934922 * 2
def baseEnd_2934922 : Nat := 334894593212238075083899

theorem tailTrace_2934922 : CollatzResearch.WordTrace tailWord_2934922 prefixEnd_2934922 334894593212238075083899 := by
  unfold tailWord_2934922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26761349868321578404143755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71363599648857542411050013 26761349868321578404143755)
  ·
    refine ⟨40142024802482367606215633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26761349868321578404143755 40142024802482367606215633)
    ·
      refine ⟨30106518601861775704661725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40142024802482367606215633 30106518601861775704661725)
      ·
        refine ⟨11289944475698165889248147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30106518601861775704661725 11289944475698165889248147)
        ·
          refine ⟨16934916713547248833872221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11289944475698165889248147 16934916713547248833872221)
          ·
            refine ⟨6350593767580218312702083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16934916713547248833872221 6350593767580218312702083)
            ·
              refine ⟨9525890651370327469053125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6350593767580218312702083 9525890651370327469053125)
              ·
                refine ⟨1786104497131936400447461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9525890651370327469053125 1786104497131936400447461)
                ·
                  refine ⟨334894593212238075083899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786104497131936400447461 334894593212238075083899)
                  ·
                    rfl

theorem cell22_2934922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_2934922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934922 prefixEnd_2934922 := by exact prefixLift 2934922
  have htrace : WordTrace (prefixWord ++ tailWord_2934922) baseStart_2934922 baseEnd_2934922 := by
    simpa [prefixWord, tailWord_2934922, baseEnd_2934922] using wordTrace_append hprefix tailTrace_2934922
  have hstable : (prefixWord ++ tailWord_2934922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934922).length < 2 ^ (prefixWord ++ tailWord_2934922).sum := by decide
  have hdescent : baseEnd_2934922 < baseStart_2934922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934958 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2934958 : Nat := 118140960795 + 2934958 * 2 ^ 59
def prefixEnd_2934958 : Nat := 4983230072969 + 3 ^ 40 * 2934958 * 2
def baseEnd_2934958 : Nat := 1004696103172422131351587

theorem tailTrace_2934958 : CollatzResearch.WordTrace tailWord_2934958 prefixEnd_2934958 1004696103172422131351587 := by
  unfold tailWord_2934958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13380839062644486470610691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71364475000770594509923685 13380839062644486470610691)
  ·
    refine ⟨20071258593966729705916037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13380839062644486470610691 20071258593966729705916037)
    ·
      refine ⟨3763360986368761819859257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20071258593966729705916037 3763360986368761819859257)
      ·
        refine ⟨2822520739776571364894443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3763360986368761819859257 2822520739776571364894443)
        ·
          refine ⟨4233781109664857047341665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822520739776571364894443 4233781109664857047341665)
          ·
            refine ⟨3175335832248642785506249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4233781109664857047341665 3175335832248642785506249)
            ·
              refine ⟨2381501874186482089129687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3175335832248642785506249 2381501874186482089129687)
              ·
                refine ⟨3572252811279723133694531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381501874186482089129687 3572252811279723133694531)
                ·
                  refine ⟨5358379216919584700541797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572252811279723133694531 5358379216919584700541797)
                  ·
                    refine ⟨1004696103172422131351587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5358379216919584700541797 1004696103172422131351587)
                    ·
                      rfl

theorem cell22_2934958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2934958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2934958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2934958 prefixEnd_2934958 := by exact prefixLift 2934958
  have htrace : WordTrace (prefixWord ++ tailWord_2934958) baseStart_2934958 baseEnd_2934958 := by
    simpa [prefixWord, tailWord_2934958, baseEnd_2934958] using wordTrace_append hprefix tailTrace_2934958
  have hstable : (prefixWord ++ tailWord_2934958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934958).length < 2 ^ (prefixWord ++ tailWord_2934958).sum := by decide
  have hdescent : baseEnd_2934958 < baseStart_2934958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935016 : List Nat := [2, 1, 4, 1, 2, 4, 1, 3, 1, 3]
def baseStart_2935016 : Nat := 118140960795 + 2935016 * 2 ^ 59
def prefixEnd_2935016 : Nat := 4983230072969 + 3 ^ 40 * 2935016 * 2
def baseEnd_2935016 : Nat := 1004715957757729313401409

theorem tailTrace_2935016 : CollatzResearch.WordTrace tailWord_2935016 prefixEnd_2935016 1004715957757729313401409 := by
  unfold tailWord_2935016
  simp only [CollatzResearch.WordTrace]
  refine ⟨53524413967472883835248451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71365885289963845113664601 53524413967472883835248451)
  ·
    refine ⟨80286620951209325752872677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53524413967472883835248451 80286620951209325752872677)
    ·
      refine ⟨15053741428351748578663627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80286620951209325752872677 15053741428351748578663627)
      ·
        refine ⟨22580612142527622867995441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15053741428351748578663627 22580612142527622867995441)
        ·
          refine ⟨16935459106895717150996581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22580612142527622867995441 16935459106895717150996581)
          ·
            refine ⟨3175398582542946965811859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16935459106895717150996581 3175398582542946965811859)
            ·
              refine ⟨4763097873814420448717789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175398582542946965811859 4763097873814420448717789)
              ·
                refine ⟨1786161702680407668269171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4763097873814420448717789 1786161702680407668269171)
                ·
                  refine ⟨2679242554020611502403757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786161702680407668269171 2679242554020611502403757)
                  ·
                    refine ⟨1004715957757729313401409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2679242554020611502403757 1004715957757729313401409)
                    ·
                      rfl

theorem cell22_2935016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_2935016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935016 prefixEnd_2935016 := by exact prefixLift 2935016
  have htrace : WordTrace (prefixWord ++ tailWord_2935016) baseStart_2935016 baseEnd_2935016 := by
    simpa [prefixWord, tailWord_2935016, baseEnd_2935016] using wordTrace_append hprefix tailTrace_2935016
  have hstable : (prefixWord ++ tailWord_2935016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935016).length < 2 ^ (prefixWord ++ tailWord_2935016).sum := by decide
  have hdescent : baseEnd_2935016 < baseStart_2935016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935040 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 6]
def baseStart_2935040 : Nat := 118140960795 + 2935040 * 2 ^ 59
def prefixEnd_2935040 : Nat := 4983230072969 + 3 ^ 40 * 2935040 * 2
def baseEnd_2935040 : Nat := 334908057816067083600445

theorem tailTrace_2935040 : CollatzResearch.WordTrace tailWord_2935040 prefixEnd_2935040 334908057816067083600445 := by
  unfold tailWord_2935040
  simp only [CollatzResearch.WordTrace]
  refine ⟨53524851643429409884685287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71366468857905879846247049 53524851643429409884685287)
  ·
    refine ⟨80287277465144114827027931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53524851643429409884685287 80287277465144114827027931)
    ·
      refine ⟨120430916197716172240541897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80287277465144114827027931 120430916197716172240541897)
      ·
        refine ⟨90323187148287129180406423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120430916197716172240541897 90323187148287129180406423)
        ·
          refine ⟨135484780722430693770609635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90323187148287129180406423 135484780722430693770609635)
          ·
            refine ⟨203227171083646040655914453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135484780722430693770609635 203227171083646040655914453)
            ·
              refine ⟨4763136822272954077872995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 203227171083646040655914453 4763136822272954077872995)
              ·
                refine ⟨7144705233409431116809493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763136822272954077872995 7144705233409431116809493)
                ·
                  refine ⟨334908057816067083600445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7144705233409431116809493 334908057816067083600445)
                  ·
                    rfl

theorem cell22_2935040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_2935040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935040 prefixEnd_2935040 := by exact prefixLift 2935040
  have htrace : WordTrace (prefixWord ++ tailWord_2935040) baseStart_2935040 baseEnd_2935040 := by
    simpa [prefixWord, tailWord_2935040, baseEnd_2935040] using wordTrace_append hprefix tailTrace_2935040
  have hstable : (prefixWord ++ tailWord_2935040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935040).length < 2 ^ (prefixWord ++ tailWord_2935040).sum := by decide
  have hdescent : baseEnd_2935040 < baseStart_2935040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935072 : List Nat := [2, 1, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_2935072 : Nat := 118140960795 + 2935072 * 2 ^ 59
def prefixEnd_2935072 : Nat := 4983230072969 + 3 ^ 40 * 2935072 * 2
def baseEnd_2935072 : Nat := 1004735127702163834001237

theorem tailTrace_2935072 : CollatzResearch.WordTrace tailWord_2935072 prefixEnd_2935072 1004735127702163834001237 := by
  unfold tailWord_2935072
  simp only [CollatzResearch.WordTrace]
  refine ⟨53525435211371444617267735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71367246948495259489690313 53525435211371444617267735)
  ·
    refine ⟨80288152817057166925901603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53525435211371444617267735 80288152817057166925901603)
    ·
      refine ⟨120432229225585750388852405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80288152817057166925901603 120432229225585750388852405)
      ·
        refine ⟨11290521489898664098954913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120432229225585750388852405 11290521489898664098954913)
        ·
          refine ⟨8467891117423998074216185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11290521489898664098954913 8467891117423998074216185)
          ·
            refine ⟨6350918338067998555662139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8467891117423998074216185 6350918338067998555662139)
            ·
              refine ⟨9526377507101997833493209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6350918338067998555662139 9526377507101997833493209)
              ·
                refine ⟨7144783130326498375119907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9526377507101997833493209 7144783130326498375119907)
                ·
                  refine ⟨10717174695489747562679861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7144783130326498375119907 10717174695489747562679861)
                  ·
                    refine ⟨1004735127702163834001237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10717174695489747562679861 1004735127702163834001237)
                    ·
                      rfl

theorem cell22_2935072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_2935072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935072 prefixEnd_2935072 := by exact prefixLift 2935072
  have htrace : WordTrace (prefixWord ++ tailWord_2935072) baseStart_2935072 baseEnd_2935072 := by
    simpa [prefixWord, tailWord_2935072, baseEnd_2935072] using wordTrace_append hprefix tailTrace_2935072
  have hstable : (prefixWord ++ tailWord_2935072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935072).length < 2 ^ (prefixWord ++ tailWord_2935072).sum := by decide
  have hdescent : baseEnd_2935072 < baseStart_2935072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935102 : List Nat := [4, 2, 1, 2, 1, 2, 3, 7]
def baseStart_2935102 : Nat := 118140960795 + 2935102 * 2 ^ 59
def prefixEnd_2935102 : Nat := 4983230072969 + 3 ^ 40 * 2935102 * 2
def baseEnd_2935102 : Nat := 111638377479472639527905

theorem tailTrace_2935102 : CollatzResearch.WordTrace tailWord_2935102 prefixEnd_2935102 111638377479472639527905 := by
  unfold tailWord_2935102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13381495576579275544765945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71367976408422802905418373 13381495576579275544765945)
  ·
    refine ⟨10036121682434456658574459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13381495576579275544765945 10036121682434456658574459)
    ·
      refine ⟨15054182523651684987861689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10036121682434456658574459 15054182523651684987861689)
      ·
        refine ⟨11290636892738763740896267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15054182523651684987861689 11290636892738763740896267)
        ·
          refine ⟨16935955339108145611344401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11290636892738763740896267 16935955339108145611344401)
          ·
            refine ⟨12701966504331109208508301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16935955339108145611344401 12701966504331109208508301)
            ·
              refine ⟨4763237439124165953190613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12701966504331109208508301 4763237439124165953190613)
              ·
                refine ⟨111638377479472639527905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4763237439124165953190613 111638377479472639527905)
                ·
                  rfl

theorem cell22_2935102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_2935102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935102 prefixEnd_2935102 := by exact prefixLift 2935102
  have htrace : WordTrace (prefixWord ++ tailWord_2935102) baseStart_2935102 baseEnd_2935102 := by
    simpa [prefixWord, tailWord_2935102, baseEnd_2935102] using wordTrace_append hprefix tailTrace_2935102
  have hstable : (prefixWord ++ tailWord_2935102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935102).length < 2 ^ (prefixWord ++ tailWord_2935102).sum := by decide
  have hdescent : baseEnd_2935102 < baseStart_2935102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935130 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_2935130 : Nat := 118140960795 + 2935130 * 2 ^ 59
def prefixEnd_2935130 : Nat := 4983230072969 + 3 ^ 40 * 2935130 * 2
def baseEnd_2935130 : Nat := 334918327429157005350353

theorem tailTrace_2935130 : CollatzResearch.WordTrace tailWord_2935130 prefixEnd_2935130 334918327429157005350353 := by
  unfold tailWord_2935130
  simp only [CollatzResearch.WordTrace]
  refine ⟨26763246464133191285036711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71368657237688510093431229 26763246464133191285036711)
  ·
    refine ⟨40144869696199786927555067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26763246464133191285036711 40144869696199786927555067)
    ·
      refine ⟨60217304544299680391332601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40144869696199786927555067 60217304544299680391332601)
      ·
        refine ⟨45162978408224760293499451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60217304544299680391332601 45162978408224760293499451)
        ·
          refine ⟨67744467612337140440249177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45162978408224760293499451 67744467612337140440249177)
          ·
            refine ⟨50808350709252855330186883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67744467612337140440249177 50808350709252855330186883)
            ·
              refine ⟨76212526063879282995280325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50808350709252855330186883 76212526063879282995280325)
              ·
                refine ⟨14289848636977365561615061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76212526063879282995280325 14289848636977365561615061)
                ·
                  refine ⟨334918327429157005350353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14289848636977365561615061 334918327429157005350353)
                  ·
                    rfl

theorem cell22_2935130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_2935130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935130 prefixEnd_2935130 := by exact prefixLift 2935130
  have htrace : WordTrace (prefixWord ++ tailWord_2935130) baseStart_2935130 baseEnd_2935130 := by
    simpa [prefixWord, tailWord_2935130, baseEnd_2935130] using wordTrace_append hprefix tailTrace_2935130
  have hstable : (prefixWord ++ tailWord_2935130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935130).length < 2 ^ (prefixWord ++ tailWord_2935130).sum := by decide
  have hdescent : baseEnd_2935130 < baseStart_2935130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935145 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_2935145 : Nat := 118140960795 + 2935145 * 2 ^ 59
def prefixEnd_2935145 : Nat := 4983230072969 + 3 ^ 40 * 2935145 * 2
def baseEnd_2935145 : Nat := 1004760117094015976926013

theorem tailTrace_2935145 : CollatzResearch.WordTrace tailWord_2935145 prefixEnd_2935145 1004760117094015976926013 := by
  unfold tailWord_2935145
  simp only [CollatzResearch.WordTrace]
  refine ⟨107053532951478422701942889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71369021967652281801295259 107053532951478422701942889)
  ·
    refine ⟨80290149713608817026457167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107053532951478422701942889 80290149713608817026457167)
    ·
      refine ⟨120435224570413225539685751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80290149713608817026457167 120435224570413225539685751)
      ·
        refine ⟨180652836855619838309528627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120435224570413225539685751 180652836855619838309528627)
        ·
          refine ⟨270979255283429757464292941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180652836855619838309528627 270979255283429757464292941)
          ·
            refine ⟨101617220731286159049109853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270979255283429757464292941 101617220731286159049109853)
            ·
              refine ⟨38106457774232309643416195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101617220731286159049109853 38106457774232309643416195)
              ·
                refine ⟨57159686661348464465124293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38106457774232309643416195 57159686661348464465124293)
                ·
                  refine ⟨10717441249002837087210805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57159686661348464465124293 10717441249002837087210805)
                  ·
                    refine ⟨1004760117094015976926013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10717441249002837087210805 1004760117094015976926013)
                    ·
                      rfl

theorem cell22_2935145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_2935145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935145 prefixEnd_2935145 := by exact prefixLift 2935145
  have htrace : WordTrace (prefixWord ++ tailWord_2935145) baseStart_2935145 baseEnd_2935145 := by
    simpa [prefixWord, tailWord_2935145, baseEnd_2935145] using wordTrace_append hprefix tailTrace_2935145
  have hstable : (prefixWord ++ tailWord_2935145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935145).length < 2 ^ (prefixWord ++ tailWord_2935145).sum := by decide
  have hdescent : baseEnd_2935145 < baseStart_2935145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935194 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_2935194 : Nat := 118140960795 + 2935194 * 2 ^ 59
def prefixEnd_2935194 : Nat := 4983230072969 + 3 ^ 40 * 2935194 * 2
def baseEnd_2935194 : Nat := 1004776890795396182450863

theorem tailTrace_2935194 : CollatzResearch.WordTrace tailWord_2935194 prefixEnd_2935194 1004776890795396182450863 := by
  unfold tailWord_2935194
  simp only [CollatzResearch.WordTrace]
  refine ⟨26763830032075226017619159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71370213418867269380317757 26763830032075226017619159)
  ·
    refine ⟨40145745048112839026428739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26763830032075226017619159 40145745048112839026428739)
    ·
      refine ⟨60218617572169258539643109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40145745048112839026428739 60218617572169258539643109)
      ·
        refine ⟨11290990794781735976183083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60218617572169258539643109 11290990794781735976183083)
        ·
          refine ⟨16936486192172603964274625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11290990794781735976183083 16936486192172603964274625)
          ·
            refine ⟨12702364644129452973205969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16936486192172603964274625 12702364644129452973205969)
            ·
              refine ⟨9526773483097089729904477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12702364644129452973205969 9526773483097089729904477)
              ·
                refine ⟨3572540056161408648714179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9526773483097089729904477 3572540056161408648714179)
                ·
                  refine ⟨5358810084242112973071269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572540056161408648714179 5358810084242112973071269)
                  ·
                    refine ⟨1004776890795396182450863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5358810084242112973071269 1004776890795396182450863)
                    ·
                      rfl

theorem cell22_2935194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_2935194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935194 prefixEnd_2935194 := by exact prefixLift 2935194
  have htrace : WordTrace (prefixWord ++ tailWord_2935194) baseStart_2935194 baseEnd_2935194 := by
    simpa [prefixWord, tailWord_2935194, baseEnd_2935194] using wordTrace_append hprefix tailTrace_2935194
  have hstable : (prefixWord ++ tailWord_2935194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935194).length < 2 ^ (prefixWord ++ tailWord_2935194).sum := by decide
  have hdescent : baseEnd_2935194 < baseStart_2935194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935239 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 2, 4]
def baseStart_2935239 : Nat := 118140960795 + 2935239 * 2 ^ 59
def prefixEnd_2935239 : Nat := 4983230072969 + 3 ^ 40 * 2935239 * 2
def baseEnd_2935239 : Nat := 1004792295215031065075725

theorem tailTrace_2935239 : CollatzResearch.WordTrace tailWord_2935239 prefixEnd_2935239 1004792295215031065075725 := by
  unfold tailWord_2935239
  simp only [CollatzResearch.WordTrace]
  refine ⟨107056961413137876755864771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71371307608758584503909847 107056961413137876755864771)
  ·
    refine ⟨160585442119706815133797157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107056961413137876755864771 160585442119706815133797157)
    ·
      refine ⟨30109770397445027837586967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160585442119706815133797157 30109770397445027837586967)
      ·
        refine ⟨45164655596167541756380451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30109770397445027837586967 45164655596167541756380451)
        ·
          refine ⟨67746983394251312634570677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45164655596167541756380451 67746983394251312634570677)
          ·
            refine ⟨6351279693211060559491001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67746983394251312634570677 6351279693211060559491001)
            ·
              refine ⟨4763459769908295419618251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6351279693211060559491001 4763459769908295419618251)
              ·
                refine ⟨7145189654862443129427377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763459769908295419618251 7145189654862443129427377)
                ·
                  refine ⟨5358892241146832347070533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7145189654862443129427377 5358892241146832347070533)
                  ·
                    refine ⟨1004792295215031065075725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5358892241146832347070533 1004792295215031065075725)
                    ·
                      rfl

theorem cell22_2935239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_2935239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935239 prefixEnd_2935239 := by exact prefixLift 2935239
  have htrace : WordTrace (prefixWord ++ tailWord_2935239) baseStart_2935239 baseEnd_2935239 := by
    simpa [prefixWord, tailWord_2935239, baseEnd_2935239] using wordTrace_append hprefix tailTrace_2935239
  have hstable : (prefixWord ++ tailWord_2935239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935239).length < 2 ^ (prefixWord ++ tailWord_2935239).sum := by decide
  have hdescent : baseEnd_2935239 < baseStart_2935239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935286 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_2935286 : Nat := 118140960795 + 2935286 * 2 ^ 59
def prefixEnd_2935286 : Nat := 4983230072969 + 3 ^ 40 * 2935286 * 2
def baseEnd_2935286 : Nat := 1004808384275538609150581

theorem tailTrace_2935286 : CollatzResearch.WordTrace tailWord_2935286 prefixEnd_2935286 1004808384275538609150581 := by
  unfold tailWord_2935286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6691167227747975236426607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71372450429311735855217141 6691167227747975236426607)
  ·
    refine ⟨10036750841621962854639911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6691167227747975236426607 10036750841621962854639911)
    ·
      refine ⟨15055126262432944281959867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10036750841621962854639911 15055126262432944281959867)
      ·
        refine ⟨22582689393649416422939801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15055126262432944281959867 22582689393649416422939801)
        ·
          refine ⟨16937017045237062317204851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22582689393649416422939801 16937017045237062317204851)
          ·
            refine ⟨25405525567855593475807277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16937017045237062317204851 25405525567855593475807277)
            ·
              refine ⟨9527072087945847553427729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25405525567855593475807277 9527072087945847553427729)
              ·
                refine ⟨7145304065959385665070797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9527072087945847553427729 7145304065959385665070797)
                ·
                  refine ⟨2679489024734769624401549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7145304065959385665070797 2679489024734769624401549)
                  ·
                    refine ⟨1004808384275538609150581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2679489024734769624401549 1004808384275538609150581)
                    ·
                      rfl

theorem cell22_2935286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_2935286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935286 prefixEnd_2935286 := by exact prefixLift 2935286
  have htrace : WordTrace (prefixWord ++ tailWord_2935286) baseStart_2935286 baseEnd_2935286 := by
    simpa [prefixWord, tailWord_2935286, baseEnd_2935286] using wordTrace_append hprefix tailTrace_2935286
  have hstable : (prefixWord ++ tailWord_2935286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935286).length < 2 ^ (prefixWord ++ tailWord_2935286).sum := by decide
  have hdescent : baseEnd_2935286 < baseStart_2935286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935316 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2935316 : Nat := 118140960795 + 2935316 * 2 ^ 59
def prefixEnd_2935316 : Nat := 4983230072969 + 3 ^ 40 * 2935316 * 2
def baseEnd_2935316 : Nat := 334939551296209510300163

theorem tailTrace_2935316 : CollatzResearch.WordTrace tailWord_2935316 prefixEnd_2935316 334939551296209510300163 := by
  unfold tailWord_2935316
  simp only [CollatzResearch.WordTrace]
  refine ⟨53529884916929459453208901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71373179889239279270945201 53529884916929459453208901)
  ·
    refine ⟨10036853421924273647476669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53529884916929459453208901 10036853421924273647476669)
    ·
      refine ⟨3763820033221602617803751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10036853421924273647476669 3763820033221602617803751)
      ·
        refine ⟨5645730049832403926705627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3763820033221602617803751 5645730049832403926705627)
        ·
          refine ⟨8468595074748605890058441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5645730049832403926705627 8468595074748605890058441)
          ·
            refine ⟨6351446306061454417543831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8468595074748605890058441 6351446306061454417543831)
            ·
              refine ⟨9527169459092181626315747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6351446306061454417543831 9527169459092181626315747)
              ·
                refine ⟨14290754188638272439473621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9527169459092181626315747 14290754188638272439473621)
                ·
                  refine ⟨334939551296209510300163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14290754188638272439473621 334939551296209510300163)
                  ·
                    rfl

theorem cell22_2935316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2935316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935316 prefixEnd_2935316 := by exact prefixLift 2935316
  have htrace : WordTrace (prefixWord ++ tailWord_2935316) baseStart_2935316 baseEnd_2935316 := by
    simpa [prefixWord, tailWord_2935316, baseEnd_2935316] using wordTrace_append hprefix tailTrace_2935316
  have hstable : (prefixWord ++ tailWord_2935316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935316).length < 2 ^ (prefixWord ++ tailWord_2935316).sum := by decide
  have hdescent : baseEnd_2935316 < baseStart_2935316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935359 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 6, 3]
def baseStart_2935359 : Nat := 118140960795 + 2935359 * 2 ^ 59
def prefixEnd_2935359 : Nat := 4983230072969 + 3 ^ 40 * 2935359 * 2
def baseEnd_2935359 : Nat := 1004833373667390752075357

theorem tailTrace_2935359 : CollatzResearch.WordTrace tailWord_2935359 prefixEnd_2935359 1004833373667390752075357 := by
  unfold tailWord_2935359
  simp only [CollatzResearch.WordTrace]
  refine ⟨107061338172703137250233131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71374225448468758166822087 107061338172703137250233131)
  ·
    refine ⟨160592007259054705875349697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107061338172703137250233131 160592007259054705875349697)
    ·
      refine ⟨120444005444291029406512273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160592007259054705875349697 120444005444291029406512273)
      ·
        refine ⟨90333004083218272054884205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120444005444291029406512273 90333004083218272054884205)
        ·
          refine ⟨33874876531206852020581577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90333004083218272054884205 33874876531206852020581577)
          ·
            refine ⟨25406157398405139015436183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33874876531206852020581577 25406157398405139015436183)
            ·
              refine ⟨38109236097607708523154275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25406157398405139015436183 38109236097607708523154275)
              ·
                refine ⟨57163854146411562784731413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38109236097607708523154275 57163854146411562784731413)
                ·
                  refine ⟨2679555663113042005534285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57163854146411562784731413 2679555663113042005534285)
                  ·
                    refine ⟨1004833373667390752075357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2679555663113042005534285 1004833373667390752075357)
                    ·
                      rfl

theorem cell22_2935359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_2935359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935359 prefixEnd_2935359 := by exact prefixLift 2935359
  have htrace : WordTrace (prefixWord ++ tailWord_2935359) baseStart_2935359 baseEnd_2935359 := by
    simpa [prefixWord, tailWord_2935359, baseEnd_2935359] using wordTrace_append hprefix tailTrace_2935359
  have hstable : (prefixWord ++ tailWord_2935359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935359).length < 2 ^ (prefixWord ++ tailWord_2935359).sum := by decide
  have hdescent : baseEnd_2935359 < baseStart_2935359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935374 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_2935374 : Nat := 118140960795 + 2935374 * 2 ^ 59
def prefixEnd_2935374 : Nat := 4983230072969 + 3 ^ 40 * 2935374 * 2
def baseEnd_2935374 : Nat := 1004838508473935712950311

theorem tailTrace_2935374 : CollatzResearch.WordTrace tailWord_2935374 prefixEnd_2935374 1004838508473935712950311 := by
  unfold tailWord_2935374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13382735658456099351503647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71374590178432529874686117 13382735658456099351503647)
  ·
    refine ⟨20074103487684149027255471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13382735658456099351503647 20074103487684149027255471)
    ·
      refine ⟨30111155231526223540883207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20074103487684149027255471 30111155231526223540883207)
      ·
        refine ⟨45166732847289335311324811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30111155231526223540883207 45166732847289335311324811)
        ·
          refine ⟨67750099270934002966987217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45166732847289335311324811 67750099270934002966987217)
          ·
            refine ⟨50812574453200502225240413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67750099270934002966987217 50812574453200502225240413)
            ·
              refine ⟨19054715419950188334465155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50812574453200502225240413 19054715419950188334465155)
              ·
                refine ⟨28582073129925282501697733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19054715419950188334465155 28582073129925282501697733)
                ·
                  refine ⟨5359138711860990469068325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28582073129925282501697733 5359138711860990469068325)
                  ·
                    refine ⟨1004838508473935712950311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5359138711860990469068325 1004838508473935712950311)
                    ·
                      rfl

theorem cell22_2935374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_2935374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935374 prefixEnd_2935374 := by exact prefixLift 2935374
  have htrace : WordTrace (prefixWord ++ tailWord_2935374) baseStart_2935374 baseEnd_2935374 := by
    simpa [prefixWord, tailWord_2935374, baseEnd_2935374] using wordTrace_append hprefix tailTrace_2935374
  have hstable : (prefixWord ++ tailWord_2935374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935374).length < 2 ^ (prefixWord ++ tailWord_2935374).sum := by decide
  have hdescent : baseEnd_2935374 < baseStart_2935374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935378 : List Nat := [3, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_2935378 : Nat := 118140960795 + 2935378 * 2 ^ 59
def prefixEnd_2935378 : Nat := 4983230072969 + 3 ^ 40 * 2935378 * 2
def baseEnd_2935378 : Nat := 334946625918560345283433

theorem tailTrace_2935378 : CollatzResearch.WordTrace tailWord_2935378 prefixEnd_2935378 334946625918560345283433 := by
  unfold tailWord_2935378
  simp only [CollatzResearch.WordTrace]
  refine ⟨26765507789908575873793697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71374687439756202330116525 26765507789908575873793697)
  ·
    refine ⟨20074130842431431905345273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26765507789908575873793697 20074130842431431905345273)
    ·
      refine ⟨15055598131823573929008955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20074130842431431905345273 15055598131823573929008955)
      ·
        refine ⟨22583397197735360893513433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15055598131823573929008955 22583397197735360893513433)
        ·
          refine ⟨16937547898301520670135075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22583397197735360893513433 16937547898301520670135075)
          ·
            refine ⟨25406321847452281005202613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16937547898301520670135075 25406321847452281005202613)
            ·
              refine ⟨2381842673198651344237745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25406321847452281005202613 2381842673198651344237745)
              ·
                refine ⟨1786382004898988508178309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2381842673198651344237745 1786382004898988508178309)
                ·
                  refine ⟨334946625918560345283433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786382004898988508178309 334946625918560345283433)
                  ·
                    rfl

theorem cell22_2935378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_2935378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935378 prefixEnd_2935378 := by exact prefixLift 2935378
  have htrace : WordTrace (prefixWord ++ tailWord_2935378) baseStart_2935378 baseEnd_2935378 := by
    simpa [prefixWord, tailWord_2935378, baseEnd_2935378] using wordTrace_append hprefix tailTrace_2935378
  have hstable : (prefixWord ++ tailWord_2935378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935378).length < 2 ^ (prefixWord ++ tailWord_2935378).sum := by decide
  have hdescent : baseEnd_2935378 < baseStart_2935378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935393 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 2, 3]
def baseStart_2935393 : Nat := 118140960795 + 2935393 * 2 ^ 59
def prefixEnd_2935393 : Nat := 4983230072969 + 3 ^ 40 * 2935393 * 2
def baseEnd_2935393 : Nat := 1004845012562225996725253

theorem tailTrace_2935393 : CollatzResearch.WordTrace tailWord_2935393 prefixEnd_2935393 1004845012562225996725253 := by
  unfold tailWord_2935393
  simp only [CollatzResearch.WordTrace]
  refine ⟨107062578254579961056970833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71375052169719974037980555 107062578254579961056970833)
  ·
    refine ⟨80296933690934970792728125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107062578254579961056970833 80296933690934970792728125)
    ·
      refine ⟨30111350134100614047273047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80296933690934970792728125 30111350134100614047273047)
      ·
        refine ⟨45167025201150921070909571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30111350134100614047273047 45167025201150921070909571)
        ·
          refine ⟨67750537801726381606364357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45167025201150921070909571 67750537801726381606364357)
          ·
            refine ⟨12703225837823696551193317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67750537801726381606364357 12703225837823696551193317)
            ·
              refine ⟨2381854844591943103348747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12703225837823696551193317 2381854844591943103348747)
              ·
                refine ⟨3572782266887914655023121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381854844591943103348747 3572782266887914655023121)
                ·
                  refine ⟨2679586700165935991267341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3572782266887914655023121 2679586700165935991267341)
                  ·
                    refine ⟨1004845012562225996725253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2679586700165935991267341 1004845012562225996725253)
                    ·
                      rfl

theorem cell22_2935393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_2935393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935393 prefixEnd_2935393 := by exact prefixLift 2935393
  have htrace : WordTrace (prefixWord ++ tailWord_2935393) baseStart_2935393 baseEnd_2935393 := by
    simpa [prefixWord, tailWord_2935393, baseEnd_2935393] using wordTrace_append hprefix tailTrace_2935393
  have hstable : (prefixWord ++ tailWord_2935393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935393).length < 2 ^ (prefixWord ++ tailWord_2935393).sum := by decide
  have hdescent : baseEnd_2935393 < baseStart_2935393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935449 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_2935449 : Nat := 118140960795 + 2935449 * 2 ^ 59
def prefixEnd_2935449 : Nat := 4983230072969 + 3 ^ 40 * 2935449 * 2
def baseEnd_2935449 : Nat := 1004864182506660517325081

theorem tailTrace_2935449 : CollatzResearch.WordTrace tailWord_2935449 prefixEnd_2935449 1004864182506660517325081 := by
  unfold tailWord_2935449
  simp only [CollatzResearch.WordTrace]
  refine ⟨107064620742377082621009401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71376413828251388414006267 107064620742377082621009401)
  ·
    refine ⟨80298465556782811965757051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107064620742377082621009401 80298465556782811965757051)
    ·
      refine ⟨120447698335174217948635577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80298465556782811965757051 120447698335174217948635577)
      ·
        refine ⟨90335773751380663461476683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120447698335174217948635577 90335773751380663461476683)
        ·
          refine ⟨135503660627070995192215025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90335773751380663461476683 135503660627070995192215025)
          ·
            refine ⟨101627745470303246394161269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135503660627070995192215025 101627745470303246394161269)
            ·
              refine ⟨9527601137840929349452619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101627745470303246394161269 9527601137840929349452619)
              ·
                refine ⟨14291401706761394024178929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9527601137840929349452619 14291401706761394024178929)
                ·
                  refine ⟨10718551280071045518134197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14291401706761394024178929 10718551280071045518134197)
                  ·
                    refine ⟨1004864182506660517325081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10718551280071045518134197 1004864182506660517325081)
                    ·
                      rfl

theorem cell22_2935449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_2935449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935449 prefixEnd_2935449 := by exact prefixLift 2935449
  have htrace : WordTrace (prefixWord ++ tailWord_2935449) baseStart_2935449 baseEnd_2935449 := by
    simpa [prefixWord, tailWord_2935449, baseEnd_2935449] using wordTrace_append hprefix tailTrace_2935449
  have hstable : (prefixWord ++ tailWord_2935449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935449).length < 2 ^ (prefixWord ++ tailWord_2935449).sum := by decide
  have hdescent : baseEnd_2935449 < baseStart_2935449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935496 : List Nat := [2, 1, 3, 1, 2, 4, 2, 1, 6]
def baseStart_2935496 : Nat := 118140960795 + 2935496 * 2 ^ 59
def prefixEnd_2935496 : Nat := 4983230072969 + 3 ^ 40 * 2935496 * 2
def baseEnd_2935496 : Nat := 334960090522389353799979

theorem tailTrace_2935496 : CollatzResearch.WordTrace tailWord_2935496 prefixEnd_2935496 334960090522389353799979 := by
  unfold tailWord_2935496
  simp only [CollatzResearch.WordTrace]
  refine ⟨53533167486603404823985171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71377556648804539765313561 53533167486603404823985171)
  ·
    refine ⟨80299751229905107235977757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53533167486603404823985171 80299751229905107235977757)
    ·
      refine ⟨30112406711214415213491659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80299751229905107235977757 30112406711214415213491659)
      ·
        refine ⟨45168610066821622820237489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30112406711214415213491659 45168610066821622820237489)
        ·
          refine ⟨33876457550116217115178117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45168610066821622820237489 33876457550116217115178117)
          ·
            refine ⟨6351835790646790709095897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33876457550116217115178117 6351835790646790709095897)
            ·
              refine ⟨4763876842985093031821923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6351835790646790709095897 4763876842985093031821923)
              ·
                refine ⟨7145815264477639547732885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763876842985093031821923 7145815264477639547732885)
                ·
                  refine ⟨334960090522389353799979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7145815264477639547732885 334960090522389353799979)
                  ·
                    rfl

theorem cell22_2935496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_2935496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935496 prefixEnd_2935496 := by exact prefixLift 2935496
  have htrace : WordTrace (prefixWord ++ tailWord_2935496) baseStart_2935496 baseEnd_2935496 := by
    simpa [prefixWord, tailWord_2935496, baseEnd_2935496] using wordTrace_append hprefix tailTrace_2935496
  have hstable : (prefixWord ++ tailWord_2935496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935496).length < 2 ^ (prefixWord ++ tailWord_2935496).sum := by decide
  have hdescent : baseEnd_2935496 < baseStart_2935496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935511 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 1, 5]
def baseStart_2935511 : Nat := 118140960795 + 2935511 * 2 ^ 59
def prefixEnd_2935511 : Nat := 4983230072969 + 3 ^ 40 * 2935511 * 2
def baseEnd_2935511 : Nat := 1004885406373713022274891

theorem tailTrace_2935511 : CollatzResearch.WordTrace tailWord_2935511 prefixEnd_2935511 1004885406373713022274891 := by
  unfold tailWord_2935511
  simp only [CollatzResearch.WordTrace]
  refine ⟨107066882068152467209766387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71377921378768311473177591 107066882068152467209766387)
  ·
    refine ⟨160600323102228700814649581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107066882068152467209766387 160600323102228700814649581)
    ·
      refine ⟨60225121163335762805493593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160600323102228700814649581 60225121163335762805493593)
      ·
        refine ⟨45168840872501822104120195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60225121163335762805493593 45168840872501822104120195)
        ·
          refine ⟨67753261308752733156180293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45168840872501822104120195 67753261308752733156180293)
          ·
            refine ⟨12703736495391137466783805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67753261308752733156180293 12703736495391137466783805)
            ·
              refine ⟨4763901185771676550043927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12703736495391137466783805 4763901185771676550043927)
              ·
                refine ⟨7145851778657514825065891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763901185771676550043927 7145851778657514825065891)
                ·
                  refine ⟨10718777667986272237598837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7145851778657514825065891 10718777667986272237598837)
                  ·
                    refine ⟨1004885406373713022274891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10718777667986272237598837 1004885406373713022274891)
                    ·
                      rfl

theorem cell22_2935511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_2935511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935511 prefixEnd_2935511 := by exact prefixLift 2935511
  have htrace : WordTrace (prefixWord ++ tailWord_2935511) baseStart_2935511 baseEnd_2935511 := by
    simpa [prefixWord, tailWord_2935511, baseEnd_2935511] using wordTrace_append hprefix tailTrace_2935511
  have hstable : (prefixWord ++ tailWord_2935511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935511).length < 2 ^ (prefixWord ++ tailWord_2935511).sum := by decide
  have hdescent : baseEnd_2935511 < baseStart_2935511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935601 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_2935601 : Nat := 118140960795 + 2935601 * 2 ^ 59
def prefixEnd_2935601 : Nat := 4983230072969 + 3 ^ 40 * 2935601 * 2
def baseEnd_2935601 : Nat := 1004916215212982787524615

theorem tailTrace_2935601 : CollatzResearch.WordTrace tailWord_2935601 prefixEnd_2935601 1004916215212982787524615 := by
  unfold tailWord_2935601
  simp only [CollatzResearch.WordTrace]
  refine ⟨107070164637826412580542657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71380109758550941720361771 107070164637826412580542657)
  ·
    refine ⟨80302623478369809435406993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107070164637826412580542657 80302623478369809435406993)
    ·
      refine ⟨60226967608777357076555245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80302623478369809435406993 60226967608777357076555245)
      ·
        refine ⟨22585112853291508903708217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60226967608777357076555245 22585112853291508903708217)
        ·
          refine ⟨16938834639968631677781163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22585112853291508903708217 16938834639968631677781163)
          ·
            refine ⟨25408251959952947516671745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16938834639968631677781163 25408251959952947516671745)
            ·
              refine ⟨19056188969964710637503809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25408251959952947516671745 19056188969964710637503809)
              ·
                refine ⟨14292141727473532978127857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19056188969964710637503809 14292141727473532978127857)
                ·
                  refine ⟨10719106295605149733595893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14292141727473532978127857 10719106295605149733595893)
                  ·
                    refine ⟨1004916215212982787524615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10719106295605149733595893 1004916215212982787524615)
                    ·
                      rfl

theorem cell22_2935601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_2935601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935601 prefixEnd_2935601 := by exact prefixLift 2935601
  have htrace : WordTrace (prefixWord ++ tailWord_2935601) baseStart_2935601 baseEnd_2935601 := by
    simpa [prefixWord, tailWord_2935601, baseEnd_2935601] using wordTrace_append hprefix tailTrace_2935601
  have hstable : (prefixWord ++ tailWord_2935601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935601).length < 2 ^ (prefixWord ++ tailWord_2935601).sum := by decide
  have hdescent : baseEnd_2935601 < baseStart_2935601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935603 : List Nat := [1, 1, 1, 2, 6, 2, 2, 2, 5]
def baseStart_2935603 : Nat := 118140960795 + 2935603 * 2 ^ 59
def prefixEnd_2935603 : Nat := 4983230072969 + 3 ^ 40 * 2935603 * 2
def baseEnd_2935603 : Nat := 334972299951285149658203

theorem tailTrace_2935603 : CollatzResearch.WordTrace tailWord_2935603 prefixEnd_2935603 334972299951285149658203 := by
  unfold tailWord_2935603
  simp only [CollatzResearch.WordTrace]
  refine ⟨107070237583819166922115463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71380158389212777948076975 107070237583819166922115463)
  ·
    refine ⟨160605356375728750383173195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107070237583819166922115463 160605356375728750383173195)
    ·
      refine ⟨240908034563593125574759793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160605356375728750383173195 240908034563593125574759793)
      ·
        refine ⟨180681025922694844181069845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240908034563593125574759793 180681025922694844181069845)
        ·
          refine ⟨8469423090126320820987649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 180681025922694844181069845 8469423090126320820987649)
          ·
            refine ⟨6352067317594740615740737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8469423090126320820987649 6352067317594740615740737)
            ·
              refine ⟨4764050488196055461805553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6352067317594740615740737 4764050488196055461805553)
              ·
                refine ⟨3573037866147041596354165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4764050488196055461805553 3573037866147041596354165)
                ·
                  refine ⟨334972299951285149658203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3573037866147041596354165 334972299951285149658203)
                  ·
                    rfl

theorem cell22_2935603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 2, 5].length) (baseStart_2935603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935603 prefixEnd_2935603 := by exact prefixLift 2935603
  have htrace : WordTrace (prefixWord ++ tailWord_2935603) baseStart_2935603 baseEnd_2935603 := by
    simpa [prefixWord, tailWord_2935603, baseEnd_2935603] using wordTrace_append hprefix tailTrace_2935603
  have hstable : (prefixWord ++ tailWord_2935603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935603).length < 2 ^ (prefixWord ++ tailWord_2935603).sum := by decide
  have hdescent : baseEnd_2935603 < baseStart_2935603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935721 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 7]
def baseStart_2935721 : Nat := 118140960795 + 2935721 * 2 ^ 59
def prefixEnd_2935721 : Nat := 4983230072969 + 3 ^ 40 * 2935721 * 2
def baseEnd_2935721 : Nat := 334985764555114158174749

theorem tailTrace_2935721 : CollatzResearch.WordTrace tailWord_2935721 prefixEnd_2935721 334985764555114158174749 := by
  unfold tailWord_2935721
  simp only [CollatzResearch.WordTrace]
  refine ⟨107074541397391673074911017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71383027598261115383274011 107074541397391673074911017)
  ·
    refine ⟨80305906048043754806183263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107074541397391673074911017 80305906048043754806183263)
    ·
      refine ⟨120458859072065632209274895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80305906048043754806183263 120458859072065632209274895)
      ·
        refine ⟨180688288608098448313912343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120458859072065632209274895 180688288608098448313912343)
        ·
          refine ⟨271032432912147672470868515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180688288608098448313912343 271032432912147672470868515)
          ·
            refine ⟨406548649368221508706302773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271032432912147672470868515 406548649368221508706302773)
            ·
              refine ⟨38113935878270766441215885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 406548649368221508706302773 38113935878270766441215885)
              ·
                refine ⟨14292725954351537415455957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38113935878270766441215885 14292725954351537415455957)
                ·
                  refine ⟨334985764555114158174749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14292725954351537415455957 334985764555114158174749)
                  ·
                    rfl

theorem cell22_2935721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_2935721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935721 prefixEnd_2935721 := by exact prefixLift 2935721
  have htrace : WordTrace (prefixWord ++ tailWord_2935721) baseStart_2935721 baseEnd_2935721 := by
    simpa [prefixWord, tailWord_2935721, baseEnd_2935721] using wordTrace_append hprefix tailTrace_2935721
  have hstable : (prefixWord ++ tailWord_2935721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935721).length < 2 ^ (prefixWord ++ tailWord_2935721).sum := by decide
  have hdescent : baseEnd_2935721 < baseStart_2935721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935738 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_2935738 : Nat := 118140960795 + 2935738 * 2 ^ 59
def prefixEnd_2935738 : Nat := 4983230072969 + 3 ^ 40 * 2935738 * 2
def baseEnd_2935738 : Nat := 334987704370920032283065

theorem tailTrace_2935738 : CollatzResearch.WordTrace tailWord_2935738 prefixEnd_2935738 334987704370920032283065 := by
  unfold tailWord_2935738
  simp only [CollatzResearch.WordTrace]
  refine ⟨26768790359582521244569967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71383440958886723318853245 26768790359582521244569967)
  ·
    refine ⟨40153185539373781866854951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26768790359582521244569967 40153185539373781866854951)
    ·
      refine ⟨60229778309060672800282427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40153185539373781866854951 60229778309060672800282427)
      ·
        refine ⟨90344667463591009200423641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60229778309060672800282427 90344667463591009200423641)
        ·
          refine ⟨67758500597693256900317731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90344667463591009200423641 67758500597693256900317731)
          ·
            refine ⟨101637750896539885350476597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67758500597693256900317731 101637750896539885350476597)
            ·
              refine ⟨9528539146550614251607181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101637750896539885350476597 9528539146550614251607181)
              ·
                refine ⟨3573202179956480344352693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9528539146550614251607181 3573202179956480344352693)
                ·
                  refine ⟨334987704370920032283065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3573202179956480344352693 334987704370920032283065)
                  ·
                    rfl

theorem cell22_2935738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_2935738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935738 prefixEnd_2935738 := by exact prefixLift 2935738
  have htrace : WordTrace (prefixWord ++ tailWord_2935738) baseStart_2935738 baseEnd_2935738 := by
    simpa [prefixWord, tailWord_2935738, baseEnd_2935738] using wordTrace_append hprefix tailTrace_2935738
  have hstable : (prefixWord ++ tailWord_2935738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935738).length < 2 ^ (prefixWord ++ tailWord_2935738).sum := by decide
  have hdescent : baseEnd_2935738 < baseStart_2935738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935813 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_2935813 : Nat := 118140960795 + 2935813 * 2 ^ 59
def prefixEnd_2935813 : Nat := 4983230072969 + 3 ^ 40 * 2935813 * 2
def baseEnd_2935813 : Nat := 1004988787145484901223965

theorem tailTrace_2935813 : CollatzResearch.WordTrace tailWord_2935813 prefixEnd_2935813 1004988787145484901223965 := by
  unfold tailWord_2935813
  simp only [CollatzResearch.WordTrace]
  refine ⟨107077896913058372787260093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71385264608705581858173395 107077896913058372787260093)
  ·
    refine ⟨40154211342396889795222535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107077896913058372787260093 40154211342396889795222535)
    ·
      refine ⟨60231317013595334692833803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40154211342396889795222535 60231317013595334692833803)
      ·
        refine ⟨90346975520393002039250705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60231317013595334692833803 90346975520393002039250705)
        ·
          refine ⟨67760231640294751529438029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90346975520393002039250705 67760231640294751529438029)
          ·
            refine ⟨25410086865110531823539261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67760231640294751529438029 25410086865110531823539261)
            ·
              refine ⟨9528782574416449433827223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25410086865110531823539261 9528782574416449433827223)
              ·
                refine ⟨14293173861624674150740835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9528782574416449433827223 14293173861624674150740835)
                ·
                  refine ⟨21439760792437011226111253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14293173861624674150740835 21439760792437011226111253)
                  ·
                    refine ⟨1004988787145484901223965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21439760792437011226111253 1004988787145484901223965)
                    ·
                      rfl

theorem cell22_2935813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_2935813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935813 prefixEnd_2935813 := by exact prefixLift 2935813
  have htrace : WordTrace (prefixWord ++ tailWord_2935813) baseStart_2935813 baseEnd_2935813 := by
    simpa [prefixWord, tailWord_2935813, baseEnd_2935813] using wordTrace_append hprefix tailTrace_2935813
  have hstable : (prefixWord ++ tailWord_2935813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935813).length < 2 ^ (prefixWord ++ tailWord_2935813).sum := by decide
  have hdescent : baseEnd_2935813 < baseStart_2935813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935815 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 4, 3]
def baseStart_2935815 : Nat := 118140960795 + 2935815 * 2 ^ 59
def prefixEnd_2935815 : Nat := 4983230072969 + 3 ^ 40 * 2935815 * 2
def baseEnd_2935815 : Nat := 1004989471786357562673959

theorem tailTrace_2935815 : CollatzResearch.WordTrace tailWord_2935815 prefixEnd_2935815 1004989471786357562673959 := by
  unfold tailWord_2935815
  simp only [CollatzResearch.WordTrace]
  refine ⟨107077969859051127128832899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71385313239367418085888599 107077969859051127128832899)
  ·
    refine ⟨160616954788576690693249349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107077969859051127128832899 160616954788576690693249349)
    ·
      refine ⟨30115679022858129504984253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160616954788576690693249349 30115679022858129504984253)
      ·
        refine ⟨11293379633571798564369095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30115679022858129504984253 11293379633571798564369095)
        ·
          refine ⟨16940069450357697846553643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11293379633571798564369095 16940069450357697846553643)
          ·
            refine ⟨25410104175536546769830465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16940069450357697846553643 25410104175536546769830465)
            ·
              refine ⟨19057578131652410077372849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25410104175536546769830465 19057578131652410077372849)
              ·
                refine ⟨14293183598739307558029637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19057578131652410077372849 14293183598739307558029637)
                ·
                  refine ⟨2679971924763620167130557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14293183598739307558029637 2679971924763620167130557)
                  ·
                    refine ⟨1004989471786357562673959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2679971924763620167130557 1004989471786357562673959)
                    ·
                      rfl

theorem cell22_2935815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_2935815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935815 prefixEnd_2935815 := by exact prefixLift 2935815
  have htrace : WordTrace (prefixWord ++ tailWord_2935815) baseStart_2935815 baseEnd_2935815 := by
    simpa [prefixWord, tailWord_2935815, baseEnd_2935815] using wordTrace_append hprefix tailTrace_2935815
  have hstable : (prefixWord ++ tailWord_2935815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935815).length < 2 ^ (prefixWord ++ tailWord_2935815).sum := by decide
  have hdescent : baseEnd_2935815 < baseStart_2935815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935832 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 2, 3]
def baseStart_2935832 : Nat := 118140960795 + 2935832 * 2 ^ 59
def prefixEnd_2935832 : Nat := 4983230072969 + 3 ^ 40 * 2935832 * 2
def baseEnd_2935832 : Nat := 1004995291233775184998907

theorem tailTrace_2935832 : CollatzResearch.WordTrace tailWord_2935832 prefixEnd_2935832 1004995291233775184998907 := by
  unfold tailWord_2935832
  simp only [CollatzResearch.WordTrace]
  refine ⟨53539294949994769516100875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71385726599993026021467833 53539294949994769516100875)
  ·
    refine ⟨80308942424992154274151313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53539294949994769516100875 80308942424992154274151313)
    ·
      refine ⟨60231706818744115705613485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80308942424992154274151313 60231706818744115705613485)
      ·
        refine ⟨22586890057029043389605057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60231706818744115705613485 22586890057029043389605057)
        ·
          refine ⟨16940167542771782542203793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22586890057029043389605057 16940167542771782542203793)
          ·
            refine ⟨12705125657078836906652845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16940167542771782542203793 12705125657078836906652845)
            ·
              refine ⟨4764422121404563839994817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12705125657078836906652845 4764422121404563839994817)
              ·
                refine ⟨3573316591053422879996113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4764422121404563839994817 3573316591053422879996113)
                ·
                  refine ⟨2679987443290067159997085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3573316591053422879996113 2679987443290067159997085)
                  ·
                    refine ⟨1004995291233775184998907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2679987443290067159997085 1004995291233775184998907)
                    ·
                      rfl

theorem cell22_2935832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_2935832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935832 prefixEnd_2935832 := by exact prefixLift 2935832
  have htrace : WordTrace (prefixWord ++ tailWord_2935832) baseStart_2935832 baseEnd_2935832 := by
    simpa [prefixWord, tailWord_2935832, baseEnd_2935832] using wordTrace_append hprefix tailTrace_2935832
  have hstable : (prefixWord ++ tailWord_2935832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935832).length < 2 ^ (prefixWord ++ tailWord_2935832).sum := by decide
  have hdescent : baseEnd_2935832 < baseStart_2935832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935862 : List Nat := [5, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2935862 : Nat := 118140960795 + 2935862 * 2 ^ 59
def prefixEnd_2935862 : Nat := 4983230072969 + 3 ^ 40 * 2935862 * 2
def baseEnd_2935862 : Nat := 111667284538540567416535

theorem tailTrace_2935862 : CollatzResearch.WordTrace tailWord_2935862 prefixEnd_2935862 111667284538540567416535 := by
  unfold tailWord_2935862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6692480255617553384737115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71386456059920569437195893 6692480255617553384737115)
  ·
    refine ⟨10038720383426330077105673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6692480255617553384737115 10038720383426330077105673)
    ·
      refine ⟨7529040287569747557829255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10038720383426330077105673 7529040287569747557829255)
      ·
        refine ⟨11293560431354621336743883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7529040287569747557829255 11293560431354621336743883)
        ·
          refine ⟨16940340647031932005115825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11293560431354621336743883 16940340647031932005115825)
          ·
            refine ⟨12705255485273949003836869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16940340647031932005115825 12705255485273949003836869)
            ·
              refine ⟨2382235403488865438219413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12705255485273949003836869 2382235403488865438219413)
              ·
                refine ⟨111667284538540567416535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2382235403488865438219413 111667284538540567416535)
                ·
                  rfl

theorem cell22_2935862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2935862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935862 prefixEnd_2935862 := by exact prefixLift 2935862
  have htrace : WordTrace (prefixWord ++ tailWord_2935862) baseStart_2935862 baseEnd_2935862 := by
    simpa [prefixWord, tailWord_2935862, baseEnd_2935862] using wordTrace_append hprefix tailTrace_2935862
  have hstable : (prefixWord ++ tailWord_2935862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935862).length < 2 ^ (prefixWord ++ tailWord_2935862).sum := by decide
  have hdescent : baseEnd_2935862 < baseStart_2935862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935888 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_2935888 : Nat := 118140960795 + 2935888 * 2 ^ 59
def prefixEnd_2935888 : Nat := 4983230072969 + 3 ^ 40 * 2935888 * 2
def baseEnd_2935888 : Nat := 1005014461178209705598735

theorem tailTrace_2935888 : CollatzResearch.WordTrace tailWord_2935888 prefixEnd_2935888 1005014461178209705598735 := by
  unfold tailWord_2935888
  simp only [CollatzResearch.WordTrace]
  refine ⟨53540316193893330298120159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71387088258524440397493545 53540316193893330298120159)
  ·
    refine ⟨80310474290839995447180239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53540316193893330298120159 80310474290839995447180239)
    ·
      refine ⟨120465711436259993170770359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80310474290839995447180239 120465711436259993170770359)
      ·
        refine ⟨180698567154389989756155539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120465711436259993170770359 180698567154389989756155539)
        ·
          refine ⟨271047850731584984634233309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180698567154389989756155539 271047850731584984634233309)
          ·
            refine ⟨101642944024344369237837491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271047850731584984634233309 101642944024344369237837491)
            ·
              refine ⟨152464416036516553856756237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101642944024344369237837491 152464416036516553856756237)
              ·
                refine ⟨57174156013693707696283589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152464416036516553856756237 57174156013693707696283589)
                ·
                  refine ⟨10720154252567570193053173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57174156013693707696283589 10720154252567570193053173)
                  ·
                    refine ⟨1005014461178209705598735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10720154252567570193053173 1005014461178209705598735)
                    ·
                      rfl

theorem cell22_2935888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_2935888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935888 prefixEnd_2935888 := by exact prefixLift 2935888
  have htrace : WordTrace (prefixWord ++ tailWord_2935888) baseStart_2935888 baseEnd_2935888 := by
    simpa [prefixWord, tailWord_2935888, baseEnd_2935888] using wordTrace_append hprefix tailTrace_2935888
  have hstable : (prefixWord ++ tailWord_2935888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935888).length < 2 ^ (prefixWord ++ tailWord_2935888).sum := by decide
  have hdescent : baseEnd_2935888 < baseStart_2935888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935890 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 7]
def baseStart_2935890 : Nat := 118140960795 + 2935890 * 2 ^ 59
def prefixEnd_2935890 : Nat := 4983230072969 + 3 ^ 40 * 2935890 * 2
def baseEnd_2935890 : Nat := 335005048606360789016243

theorem tailTrace_2935890 : CollatzResearch.WordTrace tailWord_2935890 prefixEnd_2935890 335005048606360789016243 := by
  unfold tailWord_2935890
  simp only [CollatzResearch.WordTrace]
  refine ⟨26770176333444853734453281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71387136889186276625208749 26770176333444853734453281)
  ·
    refine ⟨20077632250083640300839961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26770176333444853734453281 20077632250083640300839961)
    ·
      refine ⟨15058224187562730225629971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20077632250083640300839961 15058224187562730225629971)
      ·
        refine ⟨22587336281344095338444957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15058224187562730225629971 22587336281344095338444957)
        ·
          refine ⟨8470251105504035751916859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22587336281344095338444957 8470251105504035751916859)
          ·
            refine ⟨12705376658256053627875289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8470251105504035751916859 12705376658256053627875289)
            ·
              refine ⟨9529032493692040220906467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12705376658256053627875289 9529032493692040220906467)
              ·
                refine ⟨14293548740538060331359701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9529032493692040220906467 14293548740538060331359701)
                ·
                  refine ⟨335005048606360789016243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14293548740538060331359701 335005048606360789016243)
                  ·
                    rfl

theorem cell22_2935890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_2935890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935890 prefixEnd_2935890 := by exact prefixLift 2935890
  have htrace : WordTrace (prefixWord ++ tailWord_2935890) baseStart_2935890 baseEnd_2935890 := by
    simpa [prefixWord, tailWord_2935890, baseEnd_2935890] using wordTrace_append hprefix tailTrace_2935890
  have hstable : (prefixWord ++ tailWord_2935890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935890).length < 2 ^ (prefixWord ++ tailWord_2935890).sum := by decide
  have hdescent : baseEnd_2935890 < baseStart_2935890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935920 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_2935920 : Nat := 118140960795 + 2935920 * 2 ^ 59
def prefixEnd_2935920 : Nat := 4983230072969 + 3 ^ 40 * 2935920 * 2
def baseEnd_2935920 : Nat := 1005025415432172288798637

theorem tailTrace_2935920 : CollatzResearch.WordTrace tailWord_2935920 prefixEnd_2935920 1005025415432172288798637 := by
  unfold tailWord_2935920
  simp only [CollatzResearch.WordTrace]
  refine ⟨53540899761835365030702607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71387866349113820040936809 53540899761835365030702607)
  ·
    refine ⟨80311349642753047546053911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53540899761835365030702607 80311349642753047546053911)
    ·
      refine ⟨120467024464129571319080867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80311349642753047546053911 120467024464129571319080867)
      ·
        refine ⟨180700536696194356978621301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120467024464129571319080867 180700536696194356978621301)
        ·
          refine ⟨16940675315268220966745747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180700536696194356978621301 16940675315268220966745747)
          ·
            refine ⟨25411012972902331450118621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16940675315268220966745747 25411012972902331450118621)
            ·
              refine ⟨9529129864838374293794483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25411012972902331450118621 9529129864838374293794483)
              ·
                refine ⟨14293694797257561440691725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9529129864838374293794483 14293694797257561440691725)
                ·
                  refine ⟨5360135548971585540259397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14293694797257561440691725 5360135548971585540259397)
                  ·
                    refine ⟨1005025415432172288798637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5360135548971585540259397 1005025415432172288798637)
                    ·
                      rfl

theorem cell22_2935920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_2935920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935920 prefixEnd_2935920 := by exact prefixLift 2935920
  have htrace : WordTrace (prefixWord ++ tailWord_2935920) baseStart_2935920 baseEnd_2935920 := by
    simpa [prefixWord, tailWord_2935920, baseEnd_2935920] using wordTrace_append hprefix tailTrace_2935920
  have hstable : (prefixWord ++ tailWord_2935920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935920).length < 2 ^ (prefixWord ++ tailWord_2935920).sum := by decide
  have hdescent : baseEnd_2935920 < baseStart_2935920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935965 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2935965 : Nat := 118140960795 + 2935965 * 2 ^ 59
def prefixEnd_2935965 : Nat := 4983230072969 + 3 ^ 40 * 2935965 * 2
def baseEnd_2935965 : Nat := 1005040819851807171423499

theorem tailTrace_2935965 : CollatzResearch.WordTrace tailWord_2935965 prefixEnd_2935965 1005040819851807171423499 := by
  unfold tailWord_2935965
  simp only [CollatzResearch.WordTrace]
  refine ⟨107083440808507702746793349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71388960539005135164528899 107083440808507702746793349)
  ·
    refine ⟨20078145151595194265023753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107083440808507702746793349 20078145151595194265023753)
    ·
      refine ⟨15058608863696395698767815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20078145151595194265023753 15058608863696395698767815)
      ·
        refine ⟨22587913295544593548151723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15058608863696395698767815 22587913295544593548151723)
        ·
          refine ⟨33881869943316890322227585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22587913295544593548151723 33881869943316890322227585)
          ·
            refine ⟨25411402457487667741670689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33881869943316890322227585 25411402457487667741670689)
            ·
              refine ⟨19058551843115750806253017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25411402457487667741670689 19058551843115750806253017)
              ·
                refine ⟨14293913882336813104689763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19058551843115750806253017 14293913882336813104689763)
                ·
                  refine ⟨21440870823505219657034645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14293913882336813104689763 21440870823505219657034645)
                  ·
                    refine ⟨1005040819851807171423499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21440870823505219657034645 1005040819851807171423499)
                    ·
                      rfl

theorem cell22_2935965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2935965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2935965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2935965 prefixEnd_2935965 := by exact prefixLift 2935965
  have htrace : WordTrace (prefixWord ++ tailWord_2935965) baseStart_2935965 baseEnd_2935965 := by
    simpa [prefixWord, tailWord_2935965, baseEnd_2935965] using wordTrace_append hprefix tailTrace_2935965
  have hstable : (prefixWord ++ tailWord_2935965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935965).length < 2 ^ (prefixWord ++ tailWord_2935965).sum := by decide
  have hdescent : baseEnd_2935965 < baseStart_2935965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936001 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2936001 : Nat := 118140960795 + 2936001 * 2 ^ 59
def prefixEnd_2936001 : Nat := 4983230072969 + 3 ^ 40 * 2936001 * 2
def baseEnd_2936001 : Nat := 1005053143387515077523389

theorem tailTrace_2936001 : CollatzResearch.WordTrace tailWord_2936001 prefixEnd_2936001 1005053143387515077523389 := by
  unfold tailWord_2936001
  simp only [CollatzResearch.WordTrace]
  refine ⟨107084753836377280895103857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71389835890918187263402571 107084753836377280895103857)
  ·
    refine ⟨80313565377282960671327893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107084753836377280895103857 80313565377282960671327893)
    ·
      refine ⟨3764698377060138781468495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80313565377282960671327893 3764698377060138781468495)
      ·
        refine ⟨5647047565590208172202743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3764698377060138781468495 5647047565590208172202743)
        ·
          refine ⟨8470571348385312258304115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5647047565590208172202743 8470571348385312258304115)
          ·
            refine ⟨12705857022577968387456173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8470571348385312258304115 12705857022577968387456173)
            ·
              refine ⟨4764696383466738145296065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12705857022577968387456173 4764696383466738145296065)
              ·
                refine ⟨3573522287600053608972049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4764696383466738145296065 3573522287600053608972049)
                ·
                  refine ⟨2680141715700040206729037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3573522287600053608972049 2680141715700040206729037)
                  ·
                    refine ⟨1005053143387515077523389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2680141715700040206729037 1005053143387515077523389)
                    ·
                      rfl

theorem cell22_2936001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2936001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936001 prefixEnd_2936001 := by exact prefixLift 2936001
  have htrace : WordTrace (prefixWord ++ tailWord_2936001) baseStart_2936001 baseEnd_2936001 := by
    simpa [prefixWord, tailWord_2936001, baseEnd_2936001] using wordTrace_append hprefix tailTrace_2936001
  have hstable : (prefixWord ++ tailWord_2936001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936001).length < 2 ^ (prefixWord ++ tailWord_2936001).sum := by decide
  have hdescent : baseEnd_2936001 < baseStart_2936001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936046 : List Nat := [4, 1, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_2936046 : Nat := 118140960795 + 2936046 * 2 ^ 59
def prefixEnd_2936046 : Nat := 4983230072969 + 3 ^ 40 * 2936046 * 2
def baseEnd_2936046 : Nat := 1005068547807149960148251

theorem tailTrace_2936046 : CollatzResearch.WordTrace tailWord_2936046 prefixEnd_2936046 1005068547807149960148251 := by
  unfold tailWord_2936046
  simp only [CollatzResearch.WordTrace]
  refine ⟨13385799390151781697561499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71390930080809502386994661 13385799390151781697561499)
  ·
    refine ⟨20078699085227672546342249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13385799390151781697561499 20078699085227672546342249)
    ·
      refine ⟨15059024313920754409756687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20078699085227672546342249 15059024313920754409756687)
      ·
        refine ⟨22588536470881131614635031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15059024313920754409756687 22588536470881131614635031)
        ·
          refine ⟨33882804706321697421952547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22588536470881131614635031 33882804706321697421952547)
          ·
            refine ⟨50824207059482546132928821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33882804706321697421952547 50824207059482546132928821)
            ·
              refine ⟨4764769411826488699962077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50824207059482546132928821 4764769411826488699962077)
              ·
                refine ⟨1786788529434933262485779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4764769411826488699962077 1786788529434933262485779)
                ·
                  refine ⟨2680182794152399893728669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786788529434933262485779 2680182794152399893728669)
                  ·
                    refine ⟨1005068547807149960148251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2680182794152399893728669 1005068547807149960148251)
                    ·
                      rfl

theorem cell22_2936046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_2936046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936046 prefixEnd_2936046 := by exact prefixLift 2936046
  have htrace : WordTrace (prefixWord ++ tailWord_2936046) baseStart_2936046 baseEnd_2936046 := by
    simpa [prefixWord, tailWord_2936046, baseEnd_2936046] using wordTrace_append hprefix tailTrace_2936046
  have hstable : (prefixWord ++ tailWord_2936046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936046).length < 2 ^ (prefixWord ++ tailWord_2936046).sum := by decide
  have hdescent : baseEnd_2936046 < baseStart_2936046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936115 : List Nat := [1, 1, 1, 2, 5, 12]
def baseStart_2936115 : Nat := 118140960795 + 2936115 * 2 ^ 59
def prefixEnd_2936115 : Nat := 4983230072969 + 3 ^ 40 * 2936115 * 2
def baseEnd_2936115 : Nat := 12408545282929096051519

theorem tailTrace_2936115 : CollatzResearch.WordTrace tailWord_2936115 prefixEnd_2936115 12408545282929096051519 := by
  unfold tailWord_2936115
  simp only [CollatzResearch.WordTrace]
  refine ⟨107088911757964278364753799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71392607838642852243169199 107088911757964278364753799)
  ·
    refine ⟨160633367636946417547130699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107088911757964278364753799 160633367636946417547130699)
    ·
      refine ⟨240950051455419626320696049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160633367636946417547130699 240950051455419626320696049)
      ·
        refine ⟨180712538591564719740522037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240950051455419626320696049 180712538591564719740522037)
        ·
          refine ⟨16941800492959192475673941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180712538591564719740522037 16941800492959192475673941)
          ·
            refine ⟨12408545282929096051519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16941800492959192475673941 12408545282929096051519)
            ·
              rfl

theorem cell22_2936115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 12].length) (baseStart_2936115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936115 prefixEnd_2936115 := by exact prefixLift 2936115
  have htrace : WordTrace (prefixWord ++ tailWord_2936115) baseStart_2936115 baseEnd_2936115 := by
    simpa [prefixWord, tailWord_2936115, baseEnd_2936115] using wordTrace_append hprefix tailTrace_2936115
  have hstable : (prefixWord ++ tailWord_2936115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936115).length < 2 ^ (prefixWord ++ tailWord_2936115).sum := by decide
  have hdescent : baseEnd_2936115 < baseStart_2936115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936121 : List Nat := [1, 2, 1, 6, 2, 1, 1, 4, 4]
def baseStart_2936121 : Nat := 118140960795 + 2936121 * 2 ^ 59
def prefixEnd_2936121 : Nat := 4983230072969 + 3 ^ 40 * 2936121 * 2
def baseEnd_2936121 : Nat := 335031407279958254841007

theorem tailTrace_2936121 : CollatzResearch.WordTrace tailWord_2936121 prefixEnd_2936121 335031407279958254841007 := by
  unfold tailWord_2936121
  simp only [CollatzResearch.WordTrace]
  refine ⟨107089130595942541389472217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71392753730628360926314811 107089130595942541389472217)
  ·
    refine ⟨80316847946956906042104163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107089130595942541389472217 80316847946956906042104163)
    ·
      refine ⟨120475271920435359063156245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80316847946956906042104163 120475271920435359063156245)
      ·
        refine ⟨5647278371270407456085449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120475271920435359063156245 5647278371270407456085449)
        ·
          refine ⟨4235458778452805592064087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5647278371270407456085449 4235458778452805592064087)
          ·
            refine ⟨6353188167679208388096131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235458778452805592064087 6353188167679208388096131)
            ·
              refine ⟨9529782251518812582144197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353188167679208388096131 9529782251518812582144197)
              ·
                refine ⟨1786834172159777359152037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9529782251518812582144197 1786834172159777359152037)
                ·
                  refine ⟨335031407279958254841007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786834172159777359152037 335031407279958254841007)
                  ·
                    rfl

theorem cell22_2936121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 4, 4].length) (baseStart_2936121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936121 prefixEnd_2936121 := by exact prefixLift 2936121
  have htrace : WordTrace (prefixWord ++ tailWord_2936121) baseStart_2936121 baseEnd_2936121 := by
    simpa [prefixWord, tailWord_2936121, baseEnd_2936121] using wordTrace_append hprefix tailTrace_2936121
  have hstable : (prefixWord ++ tailWord_2936121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936121).length < 2 ^ (prefixWord ++ tailWord_2936121).sum := by decide
  have hdescent : baseEnd_2936121 < baseStart_2936121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936149 : List Nat := [1, 3, 2, 2, 3, 2, 3, 6]
def baseStart_2936149 : Nat := 118140960795 + 2936149 * 2 ^ 59
def prefixEnd_2936149 : Nat := 4983230072969 + 3 ^ 40 * 2936149 * 2
def baseEnd_2936149 : Nat := 111678200756899113869215

theorem tailTrace_2936149 : CollatzResearch.WordTrace tailWord_2936149 prefixEnd_2936149 111678200756899113869215 := by
  unfold tailWord_2936149
  simp only [CollatzResearch.WordTrace]
  refine ⟨107090151839841102171491501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71393434559894068114327667 107090151839841102171491501)
  ·
    refine ⟨40158806939940413314309313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107090151839841102171491501 40158806939940413314309313)
    ·
      refine ⟨30119105204955309985731985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40158806939940413314309313 30119105204955309985731985)
      ·
        refine ⟨22589328903716482489298989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30119105204955309985731985 22589328903716482489298989)
        ·
          refine ⟨8470998338893680933487121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22589328903716482489298989 8470998338893680933487121)
          ·
            refine ⟨6353248754170260700115341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8470998338893680933487121 6353248754170260700115341)
            ·
              refine ⟨2382468282813847762543253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6353248754170260700115341 2382468282813847762543253)
              ·
                refine ⟨111678200756899113869215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2382468282813847762543253 111678200756899113869215)
                ·
                  rfl

theorem cell22_2936149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 6].length) (baseStart_2936149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936149 prefixEnd_2936149 := by exact prefixLift 2936149
  have htrace : WordTrace (prefixWord ++ tailWord_2936149) baseStart_2936149 baseEnd_2936149 := by
    simpa [prefixWord, tailWord_2936149, baseEnd_2936149] using wordTrace_append hprefix tailTrace_2936149
  have hstable : (prefixWord ++ tailWord_2936149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936149).length < 2 ^ (prefixWord ++ tailWord_2936149).sum := by decide
  have hdescent : baseEnd_2936149 < baseStart_2936149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936157 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2936157 : Nat := 118140960795 + 2936157 * 2 ^ 59
def prefixEnd_2936157 : Nat := 4983230072969 + 3 ^ 40 * 2936157 * 2
def baseEnd_2936157 : Nat := 1005106545375582670622911

theorem tailTrace_2936157 : CollatzResearch.WordTrace tailWord_2936157 prefixEnd_2936157 1005106545375582670622911 := by
  unfold tailWord_2936157
  simp only [CollatzResearch.WordTrace]
  refine ⟨107090443623812119537782725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71393629082541413025188483 107090443623812119537782725)
  ·
    refine ⟨20079458179464772413334261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107090443623812119537782725 20079458179464772413334261)
    ·
      refine ⟨1882449204324822413750087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20079458179464772413334261 1882449204324822413750087)
      ·
        refine ⟨2823673806487233620625131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882449204324822413750087 2823673806487233620625131)
        ·
          refine ⟨4235510709730850430937697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823673806487233620625131 4235510709730850430937697)
          ·
            refine ⟨3176633032298137823203273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4235510709730850430937697 3176633032298137823203273)
            ·
              refine ⟨2382474774223603367402455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176633032298137823203273 2382474774223603367402455)
              ·
                refine ⟨3573712161335405051103683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382474774223603367402455 3573712161335405051103683)
                ·
                  refine ⟨5360568242003107576655525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573712161335405051103683 5360568242003107576655525)
                  ·
                    refine ⟨1005106545375582670622911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5360568242003107576655525 1005106545375582670622911)
                    ·
                      rfl

theorem cell22_2936157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2936157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936157 prefixEnd_2936157 := by exact prefixLift 2936157
  have htrace : WordTrace (prefixWord ++ tailWord_2936157) baseStart_2936157 baseEnd_2936157 := by
    simpa [prefixWord, tailWord_2936157, baseEnd_2936157] using wordTrace_append hprefix tailTrace_2936157
  have hstable : (prefixWord ++ tailWord_2936157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936157).length < 2 ^ (prefixWord ++ tailWord_2936157).sum := by decide
  have hdescent : baseEnd_2936157 < baseStart_2936157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936170 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 2, 3]
def baseStart_2936170 : Nat := 118140960795 + 2936170 * 2 ^ 59
def prefixEnd_2936170 : Nat := 4983230072969 + 3 ^ 40 * 2936170 * 2
def baseEnd_2936170 : Nat := 1005110995541254970047871

theorem tailTrace_2936170 : CollatzResearch.WordTrace tailWord_2936170 prefixEnd_2936170 1005110995541254970047871 := by
  unfold tailWord_2936170
  simp only [CollatzResearch.WordTrace]
  refine ⟨26772729443191255689501491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71393945181843348505337309 26772729443191255689501491)
  ·
    refine ⟨40159094164786883534252237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26772729443191255689501491 40159094164786883534252237)
    ·
      refine ⟨15059660311795081325344589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40159094164786883534252237 15059660311795081325344589)
      ·
        refine ⟨5647372616923155497004221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15059660311795081325344589 5647372616923155497004221)
        ·
          refine ⟨2117764731346183311376583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5647372616923155497004221 2117764731346183311376583)
          ·
            refine ⟨3176647097019274967064875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117764731346183311376583 3176647097019274967064875)
            ·
              refine ⟨4764970645528912450597313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176647097019274967064875 4764970645528912450597313)
              ·
                refine ⟨3573727984146684337947985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4764970645528912450597313 3573727984146684337947985)
                ·
                  refine ⟨2680295988110013253460989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3573727984146684337947985 2680295988110013253460989)
                  ·
                    refine ⟨1005110995541254970047871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2680295988110013253460989 1005110995541254970047871)
                    ·
                      rfl

theorem cell22_2936170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_2936170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936170 prefixEnd_2936170 := by exact prefixLift 2936170
  have htrace : WordTrace (prefixWord ++ tailWord_2936170) baseStart_2936170 baseEnd_2936170 := by
    simpa [prefixWord, tailWord_2936170, baseEnd_2936170] using wordTrace_append hprefix tailTrace_2936170
  have hstable : (prefixWord ++ tailWord_2936170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936170).length < 2 ^ (prefixWord ++ tailWord_2936170).sum := by decide
  have hdescent : baseEnd_2936170 < baseStart_2936170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936224 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_2936224 : Nat := 118140960795 + 2936224 * 2 ^ 59
def prefixEnd_2936224 : Nat := 4983230072969 + 3 ^ 40 * 2936224 * 2
def baseEnd_2936224 : Nat := 1005129480844816829197705

theorem tailTrace_2936224 : CollatzResearch.WordTrace tailWord_2936224 prefixEnd_2936224 1005129480844816829197705 := by
  unfold tailWord_2936224
  simp only [CollatzResearch.WordTrace]
  refine ⟨53546443657284694990235863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71395258209712926653647817 53546443657284694990235863)
  ·
    refine ⟨80319665485927042485353795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53546443657284694990235863 80319665485927042485353795)
    ·
      refine ⟨120479498228890563728030693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80319665485927042485353795 120479498228890563728030693)
      ·
        refine ⟨22589905917916980699005755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120479498228890563728030693 22589905917916980699005755)
        ·
          refine ⟨33884858876875471048508633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22589905917916980699005755 33884858876875471048508633)
          ·
            refine ⟨25413644157656603286381475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33884858876875471048508633 25413644157656603286381475)
            ·
              refine ⟨38120466236484904929572213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25413644157656603286381475 38120466236484904929572213)
              ·
                refine ⟨3573793709670459837147395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38120466236484904929572213 3573793709670459837147395)
                ·
                  refine ⟨5360690564505689755721093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573793709670459837147395 5360690564505689755721093)
                  ·
                    refine ⟨1005129480844816829197705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5360690564505689755721093 1005129480844816829197705)
                    ·
                      rfl

theorem cell22_2936224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_2936224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936224 prefixEnd_2936224 := by exact prefixLift 2936224
  have htrace : WordTrace (prefixWord ++ tailWord_2936224) baseStart_2936224 baseEnd_2936224 := by
    simpa [prefixWord, tailWord_2936224, baseEnd_2936224] using wordTrace_append hprefix tailTrace_2936224
  have hstable : (prefixWord ++ tailWord_2936224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936224).length < 2 ^ (prefixWord ++ tailWord_2936224).sum := by decide
  have hdescent : baseEnd_2936224 < baseStart_2936224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936232 : List Nat := [2, 1, 6, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2936232 : Nat := 118140960795 + 2936232 * 2 ^ 59
def prefixEnd_2936232 : Nat := 4983230072969 + 3 ^ 40 * 2936232 * 2
def baseEnd_2936232 : Nat := 1005132219408307474997681

theorem tailTrace_2936232 : CollatzResearch.WordTrace tailWord_2936232 prefixEnd_2936232 1005132219408307474997681 := by
  unfold tailWord_2936232
  simp only [CollatzResearch.WordTrace]
  refine ⟨53546589549270203673381475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71395452732360271564508633 53546589549270203673381475)
  ·
    refine ⟨80319884323905305510072213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53546589549270203673381475 80319884323905305510072213)
    ·
      refine ⟨3764994577683061195784635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 80319884323905305510072213 3764994577683061195784635)
      ·
        refine ⟨5647491866524591793676953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3764994577683061195784635 5647491866524591793676953)
        ·
          refine ⟨4235618899893443845257715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5647491866524591793676953 4235618899893443845257715)
          ·
            refine ⟨6353428349840165767886573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235618899893443845257715 6353428349840165767886573)
            ·
              refine ⟨2382535631190062162957465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6353428349840165767886573 2382535631190062162957465)
              ·
                refine ⟨1786901723392546622218099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382535631190062162957465 1786901723392546622218099)
                ·
                  refine ⟨2680352585088819933327149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786901723392546622218099 2680352585088819933327149)
                  ·
                    refine ⟨1005132219408307474997681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2680352585088819933327149 1005132219408307474997681)
                    ·
                      rfl

theorem cell22_2936232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2936232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936232 prefixEnd_2936232 := by exact prefixLift 2936232
  have htrace : WordTrace (prefixWord ++ tailWord_2936232) baseStart_2936232 baseEnd_2936232 := by
    simpa [prefixWord, tailWord_2936232, baseEnd_2936232] using wordTrace_append hprefix tailTrace_2936232
  have hstable : (prefixWord ++ tailWord_2936232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936232).length < 2 ^ (prefixWord ++ tailWord_2936232).sum := by decide
  have hdescent : baseEnd_2936232 < baseStart_2936232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936239 : List Nat := [1, 1, 2, 1, 2, 2, 1, 8, 4]
def baseStart_2936239 : Nat := 118140960795 + 2936239 * 2 ^ 59
def prefixEnd_2936239 : Nat := 4983230072969 + 3 ^ 40 * 2936239 * 2
def baseEnd_2936239 : Nat := 335044871883787263357553

theorem tailTrace_2936239 : CollatzResearch.WordTrace tailWord_2936239 prefixEnd_2936239 335044871883787263357553 := by
  unfold tailWord_2936239
  simp only [CollatzResearch.WordTrace]
  refine ⟨107093434409515047542267771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71395622939676698361511847 107093434409515047542267771)
  ·
    refine ⟨160640151614272571313401657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107093434409515047542267771 160640151614272571313401657)
    ·
      refine ⟨120480113710704428485051243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160640151614272571313401657 120480113710704428485051243)
      ·
        refine ⟨180720170566056642727576865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120480113710704428485051243 180720170566056642727576865)
        ·
          refine ⟨135540127924542482045682649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180720170566056642727576865 135540127924542482045682649)
          ·
            refine ⟨101655095943406861534261987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135540127924542482045682649 101655095943406861534261987)
            ·
              refine ⟨152482643915110292301392981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101655095943406861534261987 152482643915110292301392981)
              ·
                refine ⟨1786905983380198737906949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 152482643915110292301392981 1786905983380198737906949)
                ·
                  refine ⟨335044871883787263357553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786905983380198737906949 335044871883787263357553)
                  ·
                    rfl

theorem cell22_2936239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 4].length) (baseStart_2936239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936239 prefixEnd_2936239 := by exact prefixLift 2936239
  have htrace : WordTrace (prefixWord ++ tailWord_2936239) baseStart_2936239 baseEnd_2936239 := by
    simpa [prefixWord, tailWord_2936239, baseEnd_2936239] using wordTrace_append hprefix tailTrace_2936239
  have hstable : (prefixWord ++ tailWord_2936239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936239).length < 2 ^ (prefixWord ++ tailWord_2936239).sum := by decide
  have hdescent : baseEnd_2936239 < baseStart_2936239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936254 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2936254 : Nat := 118140960795 + 2936254 * 2 ^ 59
def prefixEnd_2936254 : Nat := 4983230072969 + 3 ^ 40 * 2936254 * 2
def baseEnd_2936254 : Nat := 1005139750457906750947613

theorem tailTrace_2936254 : CollatzResearch.WordTrace tailWord_2936254 prefixEnd_2936254 1005139750457906750947613 := by
  unfold tailWord_2936254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13386747688057588138007977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71395987669640470069375877 13386747688057588138007977)
  ·
    refine ⟨10040060766043191103505983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13386747688057588138007977 10040060766043191103505983)
    ·
      refine ⟨15060091149064786655258975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10040060766043191103505983 15060091149064786655258975)
      ·
        refine ⟨22590136723597179982888463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15060091149064786655258975 22590136723597179982888463)
        ·
          refine ⟨33885205085395769974332695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22590136723597179982888463 33885205085395769974332695)
          ·
            refine ⟨50827807628093654961499043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33885205085395769974332695 50827807628093654961499043)
            ·
              refine ⟨76241711442140482442248565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50827807628093654961499043 76241711442140482442248565)
              ·
                refine ⟨7147660447700670228960803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76241711442140482442248565 7147660447700670228960803)
                ·
                  refine ⟨10721490671551005343441205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7147660447700670228960803 10721490671551005343441205)
                  ·
                    refine ⟨1005139750457906750947613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10721490671551005343441205 1005139750457906750947613)
                    ·
                      rfl

theorem cell22_2936254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2936254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936254 prefixEnd_2936254 := by exact prefixLift 2936254
  have htrace : WordTrace (prefixWord ++ tailWord_2936254) baseStart_2936254 baseEnd_2936254 := by
    simpa [prefixWord, tailWord_2936254, baseEnd_2936254] using wordTrace_append hprefix tailTrace_2936254
  have hstable : (prefixWord ++ tailWord_2936254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936254).length < 2 ^ (prefixWord ++ tailWord_2936254).sum := by decide
  have hdescent : baseEnd_2936254 < baseStart_2936254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936267 : List Nat := [1, 1, 1, 1, 3, 3, 4, 8]
def baseStart_2936267 : Nat := 118140960795 + 2936267 * 2 ^ 59
def prefixEnd_2936267 : Nat := 4983230072969 + 3 ^ 40 * 2936267 * 2
def baseEnd_2936267 : Nat := 111682688958175450041397

theorem tailTrace_2936267 : CollatzResearch.WordTrace tailWord_2936267 prefixEnd_2936267 111682688958175450041397 := by
  unfold tailWord_2936267
  simp only [CollatzResearch.WordTrace]
  refine ⟨107094455653413608324287055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71396303768942405549524703 107094455653413608324287055)
  ·
    refine ⟨160641683480120412486430583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107094455653413608324287055 160641683480120412486430583)
    ·
      refine ⟨240962525220180618729645875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160641683480120412486430583 240962525220180618729645875)
      ·
        refine ⟨361443787830270928094468813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240962525220180618729645875 361443787830270928094468813)
        ·
          refine ⟨135541420436351598035425805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361443787830270928094468813 135541420436351598035425805)
          ·
            refine ⟨50828032663631849263284677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135541420436351598035425805 50828032663631849263284677)
            ·
              refine ⟨9530256124430971736865877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50828032663631849263284677 9530256124430971736865877)
              ·
                refine ⟨111682688958175450041397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9530256124430971736865877 111682688958175450041397)
                ·
                  rfl

theorem cell22_2936267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 8].length) (baseStart_2936267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936267 prefixEnd_2936267 := by exact prefixLift 2936267
  have htrace : WordTrace (prefixWord ++ tailWord_2936267) baseStart_2936267 baseEnd_2936267 := by
    simpa [prefixWord, tailWord_2936267, baseEnd_2936267] using wordTrace_append hprefix tailTrace_2936267
  have hstable : (prefixWord ++ tailWord_2936267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936267).length < 2 ^ (prefixWord ++ tailWord_2936267).sum := by decide
  have hdescent : baseEnd_2936267 < baseStart_2936267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936326 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2936326 : Nat := 118140960795 + 2936326 * 2 ^ 59
def prefixEnd_2936326 : Nat := 4983230072969 + 3 ^ 40 * 2936326 * 2
def baseEnd_2936326 : Nat := 1005164397529322563147393

theorem tailTrace_2936326 : CollatzResearch.WordTrace tailWord_2936326 prefixEnd_2936326 1005164397529322563147393 := by
  unfold tailWord_2936326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346768986256245668771401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71397738373466574267123221 3346768986256245668771401)
  ·
    refine ⟨2510076739692184251578551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3346768986256245668771401 2510076739692184251578551)
    ·
      refine ⟨3765115109538276377367827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2510076739692184251578551 3765115109538276377367827)
      ·
        refine ⟨5647672664307414566051741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765115109538276377367827 5647672664307414566051741)
        ·
          refine ⟨2117877249115280462269403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5647672664307414566051741 2117877249115280462269403)
          ·
            refine ⟨3176815873672920693404105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117877249115280462269403 3176815873672920693404105)
            ·
              refine ⟨2382611905254690520053079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176815873672920693404105 2382611905254690520053079)
              ·
                refine ⟨3573917857882035780079619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382611905254690520053079 3573917857882035780079619)
                ·
                  refine ⟨5360876786823053670119429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573917857882035780079619 5360876786823053670119429)
                  ·
                    refine ⟨1005164397529322563147393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5360876786823053670119429 1005164397529322563147393)
                    ·
                      rfl

theorem cell22_2936326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2936326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936326 prefixEnd_2936326 := by exact prefixLift 2936326
  have htrace : WordTrace (prefixWord ++ tailWord_2936326) baseStart_2936326 baseEnd_2936326 := by
    simpa [prefixWord, tailWord_2936326, baseEnd_2936326] using wordTrace_append hprefix tailTrace_2936326
  have hstable : (prefixWord ++ tailWord_2936326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936326).length < 2 ^ (prefixWord ++ tailWord_2936326).sum := by decide
  have hdescent : baseEnd_2936326 < baseStart_2936326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936376 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_2936376 : Nat := 118140960795 + 2936376 * 2 ^ 59
def prefixEnd_2936376 : Nat := 4983230072969 + 3 ^ 40 * 2936376 * 2
def baseEnd_2936376 : Nat := 1005181513551139099397239

theorem tailTrace_2936376 : CollatzResearch.WordTrace tailWord_2936376 prefixEnd_2936376 1005181513551139099397239 := by
  unfold tailWord_2936376
  simp only [CollatzResearch.WordTrace]
  refine ⟨53549215605009359970002491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71398954140012479960003321 53549215605009359970002491)
  ·
    refine ⟨80323823407514039955003737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53549215605009359970002491 80323823407514039955003737)
    ·
      refine ⟨60242867555635529966252803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80323823407514039955003737 60242867555635529966252803)
      ·
        refine ⟨90364301333453294949379205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60242867555635529966252803 90364301333453294949379205)
        ·
          refine ⟨16943306500022492803008601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90364301333453294949379205 16943306500022492803008601)
          ·
            refine ⟨12707479875016869602256451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16943306500022492803008601 12707479875016869602256451)
            ·
              refine ⟨19061219812525304403384677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12707479875016869602256451 19061219812525304403384677)
              ·
                refine ⟨3573978714848494575634627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19061219812525304403384677 3573978714848494575634627)
                ·
                  refine ⟨5360968072272741863451941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573978714848494575634627 5360968072272741863451941)
                  ·
                    refine ⟨1005181513551139099397239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5360968072272741863451941 1005181513551139099397239)
                    ·
                      rfl

theorem cell22_2936376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_2936376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936376 prefixEnd_2936376 := by exact prefixLift 2936376
  have htrace : WordTrace (prefixWord ++ tailWord_2936376) baseStart_2936376 baseEnd_2936376 := by
    simpa [prefixWord, tailWord_2936376, baseEnd_2936376] using wordTrace_append hprefix tailTrace_2936376
  have hstable : (prefixWord ++ tailWord_2936376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936376).length < 2 ^ (prefixWord ++ tailWord_2936376).sum := by decide
  have hdescent : baseEnd_2936376 < baseStart_2936376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936389 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2936389 : Nat := 118140960795 + 2936389 * 2 ^ 59
def prefixEnd_2936389 : Nat := 4983230072969 + 3 ^ 40 * 2936389 * 2
def baseEnd_2936389 : Nat := 1005185963716811398822199

theorem tailTrace_2936389 : CollatzResearch.WordTrace tailWord_2936389 prefixEnd_2936389 1005185963716811398822199 := by
  unfold tailWord_2936389
  simp only [CollatzResearch.WordTrace]
  refine ⟨107098905358971623160228221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71399270239314415440152147 107098905358971623160228221)
  ·
    refine ⟨40162089509614358685085583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107098905358971623160228221 40162089509614358685085583)
    ·
      refine ⟨60243134264421538027628375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40162089509614358685085583 60243134264421538027628375)
      ·
        refine ⟨90364701396632307041442563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60243134264421538027628375 90364701396632307041442563)
        ·
          refine ⟨135547052094948460562163845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90364701396632307041442563 135547052094948460562163845)
          ·
            refine ⟨25415072267802836355405721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135547052094948460562163845 25415072267802836355405721)
            ·
              refine ⟨19061304200852127266554291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25415072267802836355405721 19061304200852127266554291)
              ·
                refine ⟨28591956301278190899831437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19061304200852127266554291 28591956301278190899831437)
                ·
                  refine ⟨10721983612979321587436789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28591956301278190899831437 10721983612979321587436789)
                  ·
                    refine ⟨1005185963716811398822199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10721983612979321587436789 1005185963716811398822199)
                    ·
                      rfl

theorem cell22_2936389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2936389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936389 prefixEnd_2936389 := by exact prefixLift 2936389
  have htrace : WordTrace (prefixWord ++ tailWord_2936389) baseStart_2936389 baseEnd_2936389 := by
    simpa [prefixWord, tailWord_2936389, baseEnd_2936389] using wordTrace_append hprefix tailTrace_2936389
  have hstable : (prefixWord ++ tailWord_2936389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936389).length < 2 ^ (prefixWord ++ tailWord_2936389).sum := by decide
  have hdescent : baseEnd_2936389 < baseStart_2936389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936419 : List Nat := [1, 1, 1, 5, 1, 3, 1, 9]
def baseStart_2936419 : Nat := 118140960795 + 2936419 * 2 ^ 59
def prefixEnd_2936419 : Nat := 4983230072969 + 3 ^ 40 * 2936419 * 2
def baseEnd_2936419 : Nat := 111688470369989035619123

theorem tailTrace_2936419 : CollatzResearch.WordTrace tailWord_2936419 prefixEnd_2936419 111688470369989035619123 := by
  unfold tailWord_2936419
  simp only [CollatzResearch.WordTrace]
  refine ⟨107099999548862938283820311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71399999699241958855880207 107099999548862938283820311)
  ·
    refine ⟨160649999323294407425730467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107099999548862938283820311 160649999323294407425730467)
    ·
      refine ⟨240974998984941611138595701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160649999323294407425730467 240974998984941611138595701)
      ·
        refine ⟨22591406154838276044243347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 240974998984941611138595701 22591406154838276044243347)
        ·
          refine ⟨33887109232257414066365021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22591406154838276044243347 33887109232257414066365021)
          ·
            refine ⟨12707665962096530274886883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33887109232257414066365021 12707665962096530274886883)
            ·
              refine ⟨19061498943144795412330325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12707665962096530274886883 19061498943144795412330325)
              ·
                refine ⟨111688470369989035619123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19061498943144795412330325 111688470369989035619123)
                ·
                  rfl

theorem cell22_2936419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 9].length) (baseStart_2936419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936419 prefixEnd_2936419 := by exact prefixLift 2936419
  have htrace : WordTrace (prefixWord ++ tailWord_2936419) baseStart_2936419 baseEnd_2936419 := by
    simpa [prefixWord, tailWord_2936419, baseEnd_2936419] using wordTrace_append hprefix tailTrace_2936419
  have hstable : (prefixWord ++ tailWord_2936419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936419).length < 2 ^ (prefixWord ++ tailWord_2936419).sum := by decide
  have hdescent : baseEnd_2936419 < baseStart_2936419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936438 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2936438 : Nat := 118140960795 + 2936438 * 2 ^ 59
def prefixEnd_2936438 : Nat := 4983230072969 + 3 ^ 40 * 2936438 * 2
def baseEnd_2936438 : Nat := 1005202737418191604347049

theorem tailTrace_2936438 : CollatzResearch.WordTrace tailWord_2936438 prefixEnd_2936438 1005202737418191604347049 := by
  unfold tailWord_2936438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6693793283487131533047623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71400461690529403019174645 6693793283487131533047623)
  ·
    refine ⟨10040689925230697299571435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6693793283487131533047623 10040689925230697299571435)
    ·
      refine ⟨15061034887846045949357153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10040689925230697299571435 15061034887846045949357153)
      ·
        refine ⟨11295776165884534462017865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15061034887846045949357153 11295776165884534462017865)
        ·
          refine ⟨8471832124413400846513399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11295776165884534462017865 8471832124413400846513399)
          ·
            refine ⟨12707748186620101269770099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8471832124413400846513399 12707748186620101269770099)
            ·
              refine ⟨19061622279930151904655149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12707748186620101269770099 19061622279930151904655149)
              ·
                refine ⟨7148108354973806964245681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19061622279930151904655149 7148108354973806964245681)
                ·
                  refine ⟨5361081266230355223184261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7148108354973806964245681 5361081266230355223184261)
                  ·
                    refine ⟨1005202737418191604347049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5361081266230355223184261 1005202737418191604347049)
                    ·
                      rfl

theorem cell22_2936438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2936438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936438 prefixEnd_2936438 := by exact prefixLift 2936438
  have htrace : WordTrace (prefixWord ++ tailWord_2936438) baseStart_2936438 baseEnd_2936438 := by
    simpa [prefixWord, tailWord_2936438, baseEnd_2936438] using wordTrace_append hprefix tailTrace_2936438
  have hstable : (prefixWord ++ tailWord_2936438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936438).length < 2 ^ (prefixWord ++ tailWord_2936438).sum := by decide
  have hdescent : baseEnd_2936438 < baseStart_2936438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936464 : List Nat := [2, 1, 1, 1, 1, 1, 3, 5, 7]
def baseStart_2936464 : Nat := 118140960795 + 2936464 * 2 ^ 59
def prefixEnd_2936464 : Nat := 4983230072969 + 3 ^ 40 * 2936464 * 2
def baseEnd_2936464 : Nat := 335070545916512067732323

theorem tailTrace_2936464 : CollatzResearch.WordTrace tailWord_2936464 prefixEnd_2936464 335070545916512067732323 := by
  unfold tailWord_2936464
  simp only [CollatzResearch.WordTrace]
  refine ⟨53550820416849955484604223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71401093889133273979472297 53550820416849955484604223)
  ·
    refine ⟨80326230625274933226906335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53550820416849955484604223 80326230625274933226906335)
    ·
      refine ⟨120489345937912399840359503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80326230625274933226906335 120489345937912399840359503)
      ·
        refine ⟨180734018906868599760539255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120489345937912399840359503 180734018906868599760539255)
        ·
          refine ⟨271101028360302899640808883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180734018906868599760539255 271101028360302899640808883)
          ·
            refine ⟨406651542540454349461213325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271101028360302899640808883 406651542540454349461213325)
            ·
              refine ⟨152494328452670381047954997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406651542540454349461213325 152494328452670381047954997)
              ·
                refine ⟨14296343292437848223245781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152494328452670381047954997 14296343292437848223245781)
                ·
                  refine ⟨335070545916512067732323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14296343292437848223245781 335070545916512067732323)
                  ·
                    rfl

theorem cell22_2936464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_2936464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936464 prefixEnd_2936464 := by exact prefixLift 2936464
  have htrace : WordTrace (prefixWord ++ tailWord_2936464) baseStart_2936464 baseEnd_2936464 := by
    simpa [prefixWord, tailWord_2936464, baseEnd_2936464] using wordTrace_append hprefix tailTrace_2936464
  have hstable : (prefixWord ++ tailWord_2936464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936464).length < 2 ^ (prefixWord ++ tailWord_2936464).sum := by decide
  have hdescent : baseEnd_2936464 < baseStart_2936464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936545 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_2936545 : Nat := 118140960795 + 2936545 * 2 ^ 59
def prefixEnd_2936545 : Nat := 4983230072969 + 3 ^ 40 * 2936545 * 2
def baseEnd_2936545 : Nat := 1005239365704878991921721

theorem tailTrace_2936545 : CollatzResearch.WordTrace tailWord_2936545 prefixEnd_2936545 1005239365704878991921721 := by
  unfold tailWord_2936545
  simp only [CollatzResearch.WordTrace]
  refine ⟨107104595146406461802907089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71403063430937641201938059 107104595146406461802907089)
  ·
    refine ⟨80328446359804846352180317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107104595146406461802907089 80328446359804846352180317)
    ·
      refine ⟨30123167384926817382067619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80328446359804846352180317 30123167384926817382067619)
      ·
        refine ⟨45184751077390226073101429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30123167384926817382067619 45184751077390226073101429)
        ·
          refine ⟨4236070413505333694353259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45184751077390226073101429 4236070413505333694353259)
          ·
            refine ⟨6354105620258000541529889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4236070413505333694353259 6354105620258000541529889)
            ·
              refine ⟨4765579215193500406147417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6354105620258000541529889 4765579215193500406147417)
              ·
                refine ⟨3574184411395125304610563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4765579215193500406147417 3574184411395125304610563)
                ·
                  refine ⟨5361276617092687956915845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574184411395125304610563 5361276617092687956915845)
                  ·
                    refine ⟨1005239365704878991921721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5361276617092687956915845 1005239365704878991921721)
                    ·
                      rfl

theorem cell22_2936545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_2936545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936545 prefixEnd_2936545 := by exact prefixLift 2936545
  have htrace : WordTrace (prefixWord ++ tailWord_2936545) baseStart_2936545 baseEnd_2936545 := by
    simpa [prefixWord, tailWord_2936545, baseEnd_2936545] using wordTrace_append hprefix tailTrace_2936545
  have hstable : (prefixWord ++ tailWord_2936545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936545).length < 2 ^ (prefixWord ++ tailWord_2936545).sum := by decide
  have hdescent : baseEnd_2936545 < baseStart_2936545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936556 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_2936556 : Nat := 118140960795 + 2936556 * 2 ^ 59
def prefixEnd_2936556 : Nat := 4983230072969 + 3 ^ 40 * 2936556 * 2
def baseEnd_2936556 : Nat := 1005243131229678629896687

theorem tailTrace_2936556 : CollatzResearch.WordTrace tailWord_2936556 prefixEnd_2936556 1005243131229678629896687 := by
  unfold tailWord_2936556
  simp only [CollatzResearch.WordTrace]
  refine ⟨53552498174683305340778761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71403330899577740454371681 53552498174683305340778761)
  ·
    refine ⟨40164373631012479005584071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53552498174683305340778761 40164373631012479005584071)
    ·
      refine ⟨60246560446518718508376107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40164373631012479005584071 60246560446518718508376107)
      ·
        refine ⟨90369840669778077762564161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60246560446518718508376107 90369840669778077762564161)
        ·
          refine ⟨67777380502333558321923121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90369840669778077762564161 67777380502333558321923121)
          ·
            refine ⟨50833035376750168741442341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67777380502333558321923121 50833035376750168741442341)
            ·
              refine ⟨9531194133140656639020439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50833035376750168741442341 9531194133140656639020439)
              ·
                refine ⟨14296791199710984958530659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9531194133140656639020439 14296791199710984958530659)
                ·
                  refine ⟨21445186799566477437795989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14296791199710984958530659 21445186799566477437795989)
                  ·
                    refine ⟨1005243131229678629896687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21445186799566477437795989 1005243131229678629896687)
                    ·
                      rfl

theorem cell22_2936556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_2936556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936556 prefixEnd_2936556 := by exact prefixLift 2936556
  have htrace : WordTrace (prefixWord ++ tailWord_2936556) baseStart_2936556 baseEnd_2936556 := by
    simpa [prefixWord, tailWord_2936556, baseEnd_2936556] using wordTrace_append hprefix tailTrace_2936556
  have hstable : (prefixWord ++ tailWord_2936556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936556).length < 2 ^ (prefixWord ++ tailWord_2936556).sum := by decide
  have hdescent : baseEnd_2936556 < baseStart_2936556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936558 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_2936558 : Nat := 118140960795 + 2936558 * 2 ^ 59
def prefixEnd_2936558 : Nat := 4983230072969 + 3 ^ 40 * 2936558 * 2
def baseEnd_2936558 : Nat := 1005243815870551291346681

theorem tailTrace_2936558 : CollatzResearch.WordTrace tailWord_2936558 prefixEnd_2936558 1005243815870551291346681 := by
  unfold tailWord_2936558
  simp only [CollatzResearch.WordTrace]
  refine ⟨13388133661919920627891291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71403379530239576682086885 13388133661919920627891291)
  ·
    refine ⟨20082200492879880941836937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13388133661919920627891291 20082200492879880941836937)
    ·
      refine ⟨15061650369659910706377703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20082200492879880941836937 15061650369659910706377703)
      ·
        refine ⟨22592475554489866059566555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15061650369659910706377703 22592475554489866059566555)
        ·
          refine ⟨33888713331734799089349833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22592475554489866059566555 33888713331734799089349833)
          ·
            refine ⟨25416534998801099317012375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33888713331734799089349833 25416534998801099317012375)
            ·
              refine ⟨38124802498201648975518563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25416534998801099317012375 38124802498201648975518563)
              ·
                refine ⟨57187203747302473463277845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38124802498201648975518563 57187203747302473463277845)
                ·
                  refine ⟨2680650175654803443591149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57187203747302473463277845 2680650175654803443591149)
                  ·
                    refine ⟨1005243815870551291346681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2680650175654803443591149 1005243815870551291346681)
                    ·
                      rfl

theorem cell22_2936558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_2936558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936558 prefixEnd_2936558 := by exact prefixLift 2936558
  have htrace : WordTrace (prefixWord ++ tailWord_2936558) baseStart_2936558 baseEnd_2936558 := by
    simpa [prefixWord, tailWord_2936558, baseEnd_2936558] using wordTrace_append hprefix tailTrace_2936558
  have hstable : (prefixWord ++ tailWord_2936558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936558).length < 2 ^ (prefixWord ++ tailWord_2936558).sum := by decide
  have hdescent : baseEnd_2936558 < baseStart_2936558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936596 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2936596 : Nat := 118140960795 + 2936596 * 2 ^ 59
def prefixEnd_2936596 : Nat := 4983230072969 + 3 ^ 40 * 2936596 * 2
def baseEnd_2936596 : Nat := 1005256824047131858896565

theorem tailTrace_2936596 : CollatzResearch.WordTrace tailWord_2936596 prefixEnd_2936596 1005256824047131858896565 := by
  unfold tailWord_2936596
  simp only [CollatzResearch.WordTrace]
  refine ⟨53553227634610848756506821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71404303512814465008675761 53553227634610848756506821)
  ·
    refine ⟨10041230181489534141845029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53553227634610848756506821 10041230181489534141845029)
    ·
      refine ⟨1882730659029287651595943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10041230181489534141845029 1882730659029287651595943)
      ·
        refine ⟨2824095988543931477393915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882730659029287651595943 2824095988543931477393915)
        ·
          refine ⟨4236143982815897216090873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824095988543931477393915 4236143982815897216090873)
          ·
            refine ⟨3177107987111922912068155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4236143982815897216090873 3177107987111922912068155)
            ·
              refine ⟨4765661980667884368102233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177107987111922912068155 4765661980667884368102233)
              ·
                refine ⟨3574246485500913276076675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4765661980667884368102233 3574246485500913276076675)
                ·
                  refine ⟨5361369728251369914115013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574246485500913276076675 5361369728251369914115013)
                  ·
                    refine ⟨1005256824047131858896565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5361369728251369914115013 1005256824047131858896565)
                    ·
                      rfl

theorem cell22_2936596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2936596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936596 prefixEnd_2936596 := by exact prefixLift 2936596
  have htrace : WordTrace (prefixWord ++ tailWord_2936596) baseStart_2936596 baseEnd_2936596 := by
    simpa [prefixWord, tailWord_2936596, baseEnd_2936596] using wordTrace_append hprefix tailTrace_2936596
  have hstable : (prefixWord ++ tailWord_2936596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936596).length < 2 ^ (prefixWord ++ tailWord_2936596).sum := by decide
  have hdescent : baseEnd_2936596 < baseStart_2936596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936648 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_2936648 : Nat := 118140960795 + 2936648 * 2 ^ 59
def prefixEnd_2936648 : Nat := 4983230072969 + 3 ^ 40 * 2936648 * 2
def baseEnd_2936648 : Nat := 1005274624709821056596405

theorem tailTrace_2936648 : CollatzResearch.WordTrace tailWord_2936648 prefixEnd_2936648 1005274624709821056596405 := by
  unfold tailWord_2936648
  simp only [CollatzResearch.WordTrace]
  refine ⟨53554175932516655196953299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71405567910022206929271065 53554175932516655196953299)
  ·
    refine ⟨80331263898774982795429949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53554175932516655196953299 80331263898774982795429949)
    ·
      refine ⟨30124223962040618548286231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80331263898774982795429949 30124223962040618548286231)
      ·
        refine ⟨45186335943060927822429347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30124223962040618548286231 45186335943060927822429347)
        ·
          refine ⟨67779503914591391733644021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45186335943060927822429347 67779503914591391733644021)
          ·
            refine ⟨6354328491992942975029127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67779503914591391733644021 6354328491992942975029127)
            ·
              refine ⟨9531492737989414462543691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6354328491992942975029127 9531492737989414462543691)
              ·
                refine ⟨14297239106984121693815537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9531492737989414462543691 14297239106984121693815537)
                ·
                  refine ⟨10722929330238091270361653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14297239106984121693815537 10722929330238091270361653)
                  ·
                    refine ⟨1005274624709821056596405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10722929330238091270361653 1005274624709821056596405)
                    ·
                      rfl

theorem cell22_2936648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_2936648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936648 prefixEnd_2936648 := by exact prefixLift 2936648
  have htrace : WordTrace (prefixWord ++ tailWord_2936648) baseStart_2936648 baseEnd_2936648 := by
    simpa [prefixWord, tailWord_2936648, baseEnd_2936648] using wordTrace_append hprefix tailTrace_2936648
  have hstable : (prefixWord ++ tailWord_2936648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936648).length < 2 ^ (prefixWord ++ tailWord_2936648).sum := by decide
  have hdescent : baseEnd_2936648 < baseStart_2936648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936680 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_2936680 : Nat := 118140960795 + 2936680 * 2 ^ 59
def prefixEnd_2936680 : Nat := 4983230072969 + 3 ^ 40 * 2936680 * 2
def baseEnd_2936680 : Nat := 1005285578963783639796307

theorem tailTrace_2936680 : CollatzResearch.WordTrace tailWord_2936680 prefixEnd_2936680 1005285578963783639796307 := by
  unfold tailWord_2936680
  simp only [CollatzResearch.WordTrace]
  refine ⟨53554759500458689929535747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71406346000611586572714329 53554759500458689929535747)
  ·
    refine ⟨80332139250688034894303621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53554759500458689929535747 80332139250688034894303621)
    ·
      refine ⟨15062276109504006542681929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80332139250688034894303621 15062276109504006542681929)
      ·
        refine ⟨11296707082128004907011447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15062276109504006542681929 11296707082128004907011447)
        ·
          refine ⟨16945060623192007360517171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11296707082128004907011447 16945060623192007360517171)
          ·
            refine ⟨25417590934788011040775757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16945060623192007360517171 25417590934788011040775757)
            ·
              refine ⟨9531596600545504140290909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25417590934788011040775757 9531596600545504140290909)
              ·
                refine ⟨3574348725204564052609091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9531596600545504140290909 3574348725204564052609091)
                ·
                  refine ⟨5361523087806846078913637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574348725204564052609091 5361523087806846078913637)
                  ·
                    refine ⟨1005285578963783639796307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5361523087806846078913637 1005285578963783639796307)
                    ·
                      rfl

theorem cell22_2936680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_2936680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936680 prefixEnd_2936680 := by exact prefixLift 2936680
  have htrace : WordTrace (prefixWord ++ tailWord_2936680) baseStart_2936680 baseEnd_2936680 := by
    simpa [prefixWord, tailWord_2936680, baseEnd_2936680] using wordTrace_append hprefix tailTrace_2936680
  have hstable : (prefixWord ++ tailWord_2936680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936680).length < 2 ^ (prefixWord ++ tailWord_2936680).sum := by decide
  have hdescent : baseEnd_2936680 < baseStart_2936680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936708 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2936708 : Nat := 118140960795 + 2936708 * 2 ^ 59
def prefixEnd_2936708 : Nat := 4983230072969 + 3 ^ 40 * 2936708 * 2
def baseEnd_2936708 : Nat := 1005295163936000900096221

theorem tailTrace_2936708 : CollatzResearch.WordTrace tailWord_2936708 prefixEnd_2936708 1005295163936000900096221 := by
  unfold tailWord_2936708
  simp only [CollatzResearch.WordTrace]
  refine ⟨53555270122407970320545389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71407026829877293760727185 53555270122407970320545389)
  ·
    refine ⟨20083226295902988870204521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53555270122407970320545389 20083226295902988870204521)
    ·
      refine ⟨15062419721927241652653391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20083226295902988870204521 15062419721927241652653391)
      ·
        refine ⟨22593629582890862478980087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15062419721927241652653391 22593629582890862478980087)
        ·
          refine ⟨33890444374336293718470131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22593629582890862478980087 33890444374336293718470131)
          ·
            refine ⟨50835666561504440577705197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33890444374336293718470131 50835666561504440577705197)
            ·
              refine ⟨19063374960564165216639449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50835666561504440577705197 19063374960564165216639449)
              ·
                refine ⟨14297531220423123912479587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19063374960564165216639449 14297531220423123912479587)
                ·
                  refine ⟨21446296830634685868719381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14297531220423123912479587 21446296830634685868719381)
                  ·
                    refine ⟨1005295163936000900096221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21446296830634685868719381 1005295163936000900096221)
                    ·
                      rfl

theorem cell22_2936708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2936708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936708 prefixEnd_2936708 := by exact prefixLift 2936708
  have htrace : WordTrace (prefixWord ++ tailWord_2936708) baseStart_2936708 baseEnd_2936708 := by
    simpa [prefixWord, tailWord_2936708, baseEnd_2936708] using wordTrace_append hprefix tailTrace_2936708
  have hstable : (prefixWord ++ tailWord_2936708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936708).length < 2 ^ (prefixWord ++ tailWord_2936708).sum := by decide
  have hdescent : baseEnd_2936708 < baseStart_2936708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936920 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 7]
def baseStart_2936920 : Nat := 118140960795 + 2936920 * 2 ^ 59
def prefixEnd_2936920 : Nat := 4983230072969 + 3 ^ 40 * 2936920 * 2
def baseEnd_2936920 : Nat := 335122578622834337931857

theorem tailTrace_2936920 : CollatzResearch.WordTrace tailWord_2936920 prefixEnd_2936920 335122578622834337931857 := by
  unfold tailWord_2936920
  simp only [CollatzResearch.WordTrace]
  refine ⟨53559136260023950423904107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71412181680031933898538809 53559136260023950423904107)
  ·
    refine ⟨80338704390035925635856161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53559136260023950423904107 80338704390035925635856161)
    ·
      refine ⟨60254028292526944226892121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80338704390035925635856161 60254028292526944226892121)
      ·
        refine ⟨45190521219395208170169091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60254028292526944226892121 45190521219395208170169091)
        ·
          refine ⟨67785781829092812255253637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45190521219395208170169091 67785781829092812255253637)
          ·
            refine ⟨12709834092954902297860057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67785781829092812255253637 12709834092954902297860057)
            ·
              refine ⟨9532375569716176723395043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12709834092954902297860057 9532375569716176723395043)
              ·
                refine ⟨14298563354574265085092565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9532375569716176723395043 14298563354574265085092565)
                ·
                  refine ⟨335122578622834337931857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14298563354574265085092565 335122578622834337931857)
                  ·
                    rfl

theorem cell22_2936920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_2936920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936920 prefixEnd_2936920 := by exact prefixLift 2936920
  have htrace : WordTrace (prefixWord ++ tailWord_2936920) baseStart_2936920 baseEnd_2936920 := by
    simpa [prefixWord, tailWord_2936920, baseEnd_2936920] using wordTrace_append hprefix tailTrace_2936920
  have hstable : (prefixWord ++ tailWord_2936920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936920).length < 2 ^ (prefixWord ++ tailWord_2936920).sum := by decide
  have hdescent : baseEnd_2936920 < baseStart_2936920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936924 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2936924 : Nat := 118140960795 + 2936924 * 2 ^ 59
def prefixEnd_2936924 : Nat := 4983230072969 + 3 ^ 40 * 2936924 * 2
def baseEnd_2936924 : Nat := 1005369105150248336695559

theorem tailTrace_2936924 : CollatzResearch.WordTrace tailWord_2936924 prefixEnd_2936924 1005369105150248336695559 := by
  unfold tailWord_2936924
  simp only [CollatzResearch.WordTrace]
  refine ⟨53559209206016704765476913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71412278941355606353969217 53559209206016704765476913)
  ·
    refine ⟨40169406904512528574107685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53559209206016704765476913 40169406904512528574107685)
    ·
      refine ⟨7531763794596099107645191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40169406904512528574107685 7531763794596099107645191)
      ·
        refine ⟨11297645691894148661467787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7531763794596099107645191 11297645691894148661467787)
        ·
          refine ⟨16946468537841222992201681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11297645691894148661467787 16946468537841222992201681)
          ·
            refine ⟨12709851403380917244151261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16946468537841222992201681 12709851403380917244151261)
            ·
              refine ⟨4766194276267843966556723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12709851403380917244151261 4766194276267843966556723)
              ·
                refine ⟨7149291414401765949835085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766194276267843966556723 7149291414401765949835085)
                ·
                  refine ⟨2680984280400662231188157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7149291414401765949835085 2680984280400662231188157)
                  ·
                    refine ⟨1005369105150248336695559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2680984280400662231188157 1005369105150248336695559)
                    ·
                      rfl

theorem cell22_2936924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2936924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936924 prefixEnd_2936924 := by exact prefixLift 2936924
  have htrace : WordTrace (prefixWord ++ tailWord_2936924) baseStart_2936924 baseEnd_2936924 := by
    simpa [prefixWord, tailWord_2936924, baseEnd_2936924] using wordTrace_append hprefix tailTrace_2936924
  have hstable : (prefixWord ++ tailWord_2936924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936924).length < 2 ^ (prefixWord ++ tailWord_2936924).sum := by decide
  have hdescent : baseEnd_2936924 < baseStart_2936924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936926 : List Nat := [4, 4, 1, 1, 2, 1, 2, 7]
def baseStart_2936926 : Nat := 118140960795 + 2936926 * 2 ^ 59
def prefixEnd_2936926 : Nat := 4983230072969 + 3 ^ 40 * 2936926 * 2
def baseEnd_2936926 : Nat := 111707754421235666460617

theorem tailTrace_2936926 : CollatzResearch.WordTrace tailWord_2936926 prefixEnd_2936926 111707754421235666460617 := by
  unfold tailWord_2936926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13389811419753270484065829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71412327572017442581684421 13389811419753270484065829)
  ·
    refine ⟨2510589641203738215762343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13389811419753270484065829 2510589641203738215762343)
    ·
      refine ⟨3765884461805607323643515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2510589641203738215762343 3765884461805607323643515)
      ·
        refine ⟨5648826692708410985465273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765884461805607323643515 5648826692708410985465273)
        ·
          refine ⟨4236620019531308239098955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5648826692708410985465273 4236620019531308239098955)
          ·
            refine ⟨6354930029296962358648433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4236620019531308239098955 6354930029296962358648433)
            ·
              refine ⟨4766197521972721768986325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6354930029296962358648433 4766197521972721768986325)
              ·
                refine ⟨111707754421235666460617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4766197521972721768986325 111707754421235666460617)
                ·
                  rfl

theorem cell22_2936926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_2936926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936926 prefixEnd_2936926 := by exact prefixLift 2936926
  have htrace : WordTrace (prefixWord ++ tailWord_2936926) baseStart_2936926 baseEnd_2936926 := by
    simpa [prefixWord, tailWord_2936926, baseEnd_2936926] using wordTrace_append hprefix tailTrace_2936926
  have hstable : (prefixWord ++ tailWord_2936926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936926).length < 2 ^ (prefixWord ++ tailWord_2936926).sum := by decide
  have hdescent : baseEnd_2936926 < baseStart_2936926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936930 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2936930 : Nat := 118140960795 + 2936930 * 2 ^ 59
def prefixEnd_2936930 : Nat := 4983230072969 + 3 ^ 40 * 2936930 * 2
def baseEnd_2936930 : Nat := 1005371159072866321045541

theorem tailTrace_2936930 : CollatzResearch.WordTrace tailWord_2936930 prefixEnd_2936930 1005371159072866321045541 := by
  unfold tailWord_2936930
  simp only [CollatzResearch.WordTrace]
  refine ⟨26779659312502918138918061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71412424833341115037114829 26779659312502918138918061)
  ·
    refine ⟨10042372242188594302094273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26779659312502918138918061 10042372242188594302094273)
    ·
      refine ⟨7531779181641445726570705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10042372242188594302094273 7531779181641445726570705)
      ·
        refine ⟨5648834386231084294928029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7531779181641445726570705 5648834386231084294928029)
        ·
          refine ⟨2118312894836656610598011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5648834386231084294928029 2118312894836656610598011)
          ·
            refine ⟨3177469342254984915897017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118312894836656610598011 3177469342254984915897017)
            ·
              refine ⟨2383102006691238686922763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3177469342254984915897017 2383102006691238686922763)
              ·
                refine ⟨3574653010036858030384145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383102006691238686922763 3574653010036858030384145)
                ·
                  refine ⟨2680989757527643522788109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3574653010036858030384145 2680989757527643522788109)
                  ·
                    refine ⟨1005371159072866321045541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2680989757527643522788109 1005371159072866321045541)
                    ·
                      rfl

theorem cell22_2936930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2936930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936930 prefixEnd_2936930 := by exact prefixLift 2936930
  have htrace : WordTrace (prefixWord ++ tailWord_2936930) baseStart_2936930 baseEnd_2936930 := by
    simpa [prefixWord, tailWord_2936930, baseEnd_2936930] using wordTrace_append hprefix tailTrace_2936930
  have hstable : (prefixWord ++ tailWord_2936930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936930).length < 2 ^ (prefixWord ++ tailWord_2936930).sum := by decide
  have hdescent : baseEnd_2936930 < baseStart_2936930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936935 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2936935 : Nat := 118140960795 + 2936935 * 2 ^ 59
def prefixEnd_2936935 : Nat := 4983230072969 + 3 ^ 40 * 2936935 * 2
def baseEnd_2936935 : Nat := 1005372870675047974670525

theorem tailTrace_2936935 : CollatzResearch.WordTrace tailWord_2936935 prefixEnd_2936935 1005372870675047974670525 := by
  unfold tailWord_2936935
  simp only [CollatzResearch.WordTrace]
  refine ⟨107118819614993558409604259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71412546409995705606402839 107118819614993558409604259)
  ·
    refine ⟨160678229422490337614406389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107118819614993558409604259 160678229422490337614406389)
    ·
      refine ⟨15063584008358469151350599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160678229422490337614406389 15063584008358469151350599)
      ·
        refine ⟨22595376012537703727025899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15063584008358469151350599 22595376012537703727025899)
        ·
          refine ⟨33893064018806555590538849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22595376012537703727025899 33893064018806555590538849)
          ·
            refine ⟨25419798014104916692904137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33893064018806555590538849 25419798014104916692904137)
            ·
              refine ⟨19064848510578687519678103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25419798014104916692904137 19064848510578687519678103)
              ·
                refine ⟨28597272765868031279517155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19064848510578687519678103 28597272765868031279517155)
                ·
                  refine ⟨42895909148802046919275733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28597272765868031279517155 42895909148802046919275733)
                  ·
                    refine ⟨1005372870675047974670525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42895909148802046919275733 1005372870675047974670525)
                    ·
                      rfl

theorem cell22_2936935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2936935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936935 prefixEnd_2936935 := by exact prefixLift 2936935
  have htrace : WordTrace (prefixWord ++ tailWord_2936935) baseStart_2936935 baseEnd_2936935 := by
    simpa [prefixWord, tailWord_2936935, baseEnd_2936935] using wordTrace_append hprefix tailTrace_2936935
  have hstable : (prefixWord ++ tailWord_2936935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936935).length < 2 ^ (prefixWord ++ tailWord_2936935).sum := by decide
  have hdescent : baseEnd_2936935 < baseStart_2936935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936967 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 1, 4]
def baseStart_2936967 : Nat := 118140960795 + 2936967 * 2 ^ 59
def prefixEnd_2936967 : Nat := 4983230072969 + 3 ^ 40 * 2936967 * 2
def baseEnd_2936967 : Nat := 1005383824929010557870427

theorem tailTrace_2936967 : CollatzResearch.WordTrace tailWord_2936967 prefixEnd_2936967 1005383824929010557870427 := by
  unfold tailWord_2936967
  simp only [CollatzResearch.WordTrace]
  refine ⟨107119986750877627874769155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71413324500585085249846103 107119986750877627874769155)
  ·
    refine ⟨160679980126316441812153733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107119986750877627874769155 160679980126316441812153733)
    ·
      refine ⟨30127496273684332839778825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160679980126316441812153733 30127496273684332839778825)
      ·
        refine ⟨22595622205263249629834119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30127496273684332839778825 22595622205263249629834119)
        ·
          refine ⟨33893433307894874444751179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22595622205263249629834119 33893433307894874444751179)
          ·
            refine ⟨50840149961842311667126769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33893433307894874444751179 50840149961842311667126769)
            ·
              refine ⟨38130112471381733750345077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50840149961842311667126769 38130112471381733750345077)
              ·
                refine ⟨3574698044192037539094851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38130112471381733750345077 3574698044192037539094851)
                ·
                  refine ⟨5362047066288056308642277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574698044192037539094851 5362047066288056308642277)
                  ·
                    refine ⟨1005383824929010557870427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5362047066288056308642277 1005383824929010557870427)
                    ·
                      rfl

theorem cell22_2936967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_2936967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936967 prefixEnd_2936967 := by exact prefixLift 2936967
  have htrace : WordTrace (prefixWord ++ tailWord_2936967) baseStart_2936967 baseEnd_2936967 := by
    simpa [prefixWord, tailWord_2936967, baseEnd_2936967] using wordTrace_append hprefix tailTrace_2936967
  have hstable : (prefixWord ++ tailWord_2936967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936967).length < 2 ^ (prefixWord ++ tailWord_2936967).sum := by decide
  have hdescent : baseEnd_2936967 < baseStart_2936967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936997 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_2936997 : Nat := 118140960795 + 2936997 * 2 ^ 59
def prefixEnd_2936997 : Nat := 4983230072969 + 3 ^ 40 * 2936997 * 2
def baseEnd_2936997 : Nat := 1005394094542100479620335

theorem tailTrace_2936997 : CollatzResearch.WordTrace tailWord_2936997 prefixEnd_2936997 1005394094542100479620335 := by
  unfold tailWord_2936997
  simp only [CollatzResearch.WordTrace]
  refine ⟨107121080940768942998361245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71414053960512628665574163 107121080940768942998361245)
  ·
    refine ⟨40170405352788353624385467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107121080940768942998361245 40170405352788353624385467)
    ·
      refine ⟨60255608029182530436578201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40170405352788353624385467 60255608029182530436578201)
      ·
        refine ⟨45191706021886897827433651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60255608029182530436578201 45191706021886897827433651)
        ·
          refine ⟨67787559032830346741150477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45191706021886897827433651 67787559032830346741150477)
          ·
            refine ⟨25420334637311380027931429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67787559032830346741150477 25420334637311380027931429)
            ·
              refine ⟨4766312744495883755237143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25420334637311380027931429 4766312744495883755237143)
              ·
                refine ⟨7149469116743825632855715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766312744495883755237143 7149469116743825632855715)
                ·
                  refine ⟨10724203675115738449283573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7149469116743825632855715 10724203675115738449283573)
                  ·
                    refine ⟨1005394094542100479620335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10724203675115738449283573 1005394094542100479620335)
                    ·
                      rfl

theorem cell22_2936997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_2936997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936997 prefixEnd_2936997 := by exact prefixLift 2936997
  have htrace : WordTrace (prefixWord ++ tailWord_2936997) baseStart_2936997 baseEnd_2936997 := by
    simpa [prefixWord, tailWord_2936997, baseEnd_2936997] using wordTrace_append hprefix tailTrace_2936997
  have hstable : (prefixWord ++ tailWord_2936997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936997).length < 2 ^ (prefixWord ++ tailWord_2936997).sum := by decide
  have hdescent : baseEnd_2936997 < baseStart_2936997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936999 : List Nat := [1, 1, 6, 2, 2, 1, 1, 2, 6]
def baseStart_2936999 : Nat := 118140960795 + 2936999 * 2 ^ 59
def prefixEnd_2936999 : Nat := 4983230072969 + 3 ^ 40 * 2936999 * 2
def baseEnd_2936999 : Nat := 335131593060991047023443

theorem tailTrace_2936999 : CollatzResearch.WordTrace tailWord_2936999 prefixEnd_2936999 335131593060991047023443 := by
  unfold tailWord_2936999
  simp only [CollatzResearch.WordTrace]
  refine ⟨107121153886761697339934051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71414102591174464893289367 107121153886761697339934051)
  ·
    refine ⟨160681730830142546009901077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107121153886761697339934051 160681730830142546009901077)
    ·
      refine ⟨7531956132662931844214113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 160681730830142546009901077 7531956132662931844214113)
      ·
        refine ⟨5648967099497198883160585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7531956132662931844214113 5648967099497198883160585)
        ·
          refine ⟨4236725324622899162370439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5648967099497198883160585 4236725324622899162370439)
          ·
            refine ⟨6355087986934348743555659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4236725324622899162370439 6355087986934348743555659)
            ·
              refine ⟨9532631980401523115333489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6355087986934348743555659 9532631980401523115333489)
              ·
                refine ⟨7149473985301142336500117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9532631980401523115333489 7149473985301142336500117)
                ·
                  refine ⟨335131593060991047023443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7149473985301142336500117 335131593060991047023443)
                  ·
                    rfl

theorem cell22_2936999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 2, 6].length) (baseStart_2936999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2936999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2936999 prefixEnd_2936999 := by exact prefixLift 2936999
  have htrace : WordTrace (prefixWord ++ tailWord_2936999) baseStart_2936999 baseEnd_2936999 := by
    simpa [prefixWord, tailWord_2936999, baseEnd_2936999] using wordTrace_append hprefix tailTrace_2936999
  have hstable : (prefixWord ++ tailWord_2936999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936999).length < 2 ^ (prefixWord ++ tailWord_2936999).sum := by decide
  have hdescent : baseEnd_2936999 < baseStart_2936999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937119 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 3, 4]
def baseStart_2937119 : Nat := 118140960795 + 2937119 * 2 ^ 59
def prefixEnd_2937119 : Nat := 4983230072969 + 3 ^ 40 * 2937119 * 2
def baseEnd_2937119 : Nat := 1005435857635332828069961

theorem tailTrace_2937119 : CollatzResearch.WordTrace tailWord_2937119 prefixEnd_2937119 1005435857635332828069961 := by
  unfold tailWord_2937119
  simp only [CollatzResearch.WordTrace]
  refine ⟨107125530646326957834302411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71417020430884638556201607 107125530646326957834302411)
  ·
    refine ⟨160688295969490436751453617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107125530646326957834302411 160688295969490436751453617)
    ·
      refine ⟨120516221977117827563590213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160688295969490436751453617 120516221977117827563590213)
      ·
        refine ⟨22596791620709592668173165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120516221977117827563590213 22596791620709592668173165)
        ·
          refine ⟨8473796857766097250564937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22596791620709592668173165 8473796857766097250564937)
          ·
            refine ⟨6355347643324572937923703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8473796857766097250564937 6355347643324572937923703)
            ·
              refine ⟨9533021464986859406885555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6355347643324572937923703 9533021464986859406885555)
              ·
                refine ⟨14299532197480289110328333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9533021464986859406885555 14299532197480289110328333)
                ·
                  refine ⟨5362324574055108416373125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14299532197480289110328333 5362324574055108416373125)
                  ·
                    refine ⟨1005435857635332828069961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5362324574055108416373125 1005435857635332828069961)
                    ·
                      rfl

theorem cell22_2937119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_2937119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937119 prefixEnd_2937119 := by exact prefixLift 2937119
  have htrace : WordTrace (prefixWord ++ tailWord_2937119) baseStart_2937119 baseEnd_2937119 := by
    simpa [prefixWord, tailWord_2937119, baseEnd_2937119] using wordTrace_append hprefix tailTrace_2937119
  have hstable : (prefixWord ++ tailWord_2937119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937119).length < 2 ^ (prefixWord ++ tailWord_2937119).sum := by decide
  have hdescent : baseEnd_2937119 < baseStart_2937119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937132 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_2937132 : Nat := 118140960795 + 2937132 * 2 ^ 59
def prefixEnd_2937132 : Nat := 4983230072969 + 3 ^ 40 * 2937132 * 2
def baseEnd_2937132 : Nat := 1005440307801005127494921

theorem tailTrace_2937132 : CollatzResearch.WordTrace tailWord_2937132 prefixEnd_2937132 1005440307801005127494921 := by
  unfold tailWord_2937132
  simp only [CollatzResearch.WordTrace]
  refine ⟨53563002397639930527262825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71417336530186574036350433 53563002397639930527262825)
  ·
    refine ⟨40172251798229947895447119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53563002397639930527262825 40172251798229947895447119)
    ·
      refine ⟨60258377697344921843170679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40172251798229947895447119 60258377697344921843170679)
      ·
        refine ⟨90387566546017382764756019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60258377697344921843170679 90387566546017382764756019)
        ·
          refine ⟨135581349819026074147134029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90387566546017382764756019 135581349819026074147134029)
          ·
            refine ⟨50843006182134777805175261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135581349819026074147134029 50843006182134777805175261)
            ·
              refine ⟨19066127318300541676940723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50843006182134777805175261 19066127318300541676940723)
              ·
                refine ⟨28599190977450812515411085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19066127318300541676940723 28599190977450812515411085)
                ·
                  refine ⟨10724696616544054693279157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28599190977450812515411085 10724696616544054693279157)
                  ·
                    refine ⟨1005440307801005127494921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10724696616544054693279157 1005440307801005127494921)
                    ·
                      rfl

theorem cell22_2937132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_2937132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937132 prefixEnd_2937132 := by exact prefixLift 2937132
  have htrace : WordTrace (prefixWord ++ tailWord_2937132) baseStart_2937132 baseEnd_2937132 := by
    simpa [prefixWord, tailWord_2937132, baseEnd_2937132] using wordTrace_append hprefix tailTrace_2937132
  have hstable : (prefixWord ++ tailWord_2937132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937132).length < 2 ^ (prefixWord ++ tailWord_2937132).sum := by decide
  have hdescent : baseEnd_2937132 < baseStart_2937132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937211 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 3, 3]
def baseStart_2937211 : Nat := 118140960795 + 2937211 * 2 ^ 59
def prefixEnd_2937211 : Nat := 4983230072969 + 3 ^ 40 * 2937211 * 2
def baseEnd_2937211 : Nat := 1005467351115475254769679

theorem tailTrace_2937211 : CollatzResearch.WordTrace tailWord_2937211 prefixEnd_2937211 1005467351115475254769679 := by
  unfold tailWord_2937211
  simp only [CollatzResearch.WordTrace]
  refine ⟨107128886161993657546651487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71419257441329105031100991 107128886161993657546651487)
  ·
    refine ⟨160693329242990486319977231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107128886161993657546651487 160693329242990486319977231)
    ·
      refine ⟨241039993864485729479965847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160693329242990486319977231 241039993864485729479965847)
      ·
        refine ⟨361559990796728594219948771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241039993864485729479965847 361559990796728594219948771)
        ·
          refine ⟨542339986195092891329923157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361559990796728594219948771 542339986195092891329923157)
          ·
            refine ⟨6355546713223744820272537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 542339986195092891329923157 6355546713223744820272537)
            ·
              refine ⟨4766660034917808615204403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6355546713223744820272537 4766660034917808615204403)
              ·
                refine ⟨7149990052376712922806605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766660034917808615204403 7149990052376712922806605)
                ·
                  refine ⟨2681246269641267346052477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7149990052376712922806605 2681246269641267346052477)
                  ·
                    refine ⟨1005467351115475254769679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681246269641267346052477 1005467351115475254769679)
                    ·
                      rfl

theorem cell22_2937211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 3].length) (baseStart_2937211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937211 prefixEnd_2937211 := by exact prefixLift 2937211
  have htrace : WordTrace (prefixWord ++ tailWord_2937211) baseStart_2937211 baseEnd_2937211 := by
    simpa [prefixWord, tailWord_2937211, baseEnd_2937211] using wordTrace_append hprefix tailTrace_2937211
  have hstable : (prefixWord ++ tailWord_2937211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937211).length < 2 ^ (prefixWord ++ tailWord_2937211).sum := by decide
  have hdescent : baseEnd_2937211 < baseStart_2937211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937288 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 1, 4]
def baseStart_2937288 : Nat := 118140960795 + 2937288 * 2 ^ 59
def prefixEnd_2937288 : Nat := 4983230072969 + 3 ^ 40 * 2937288 * 2
def baseEnd_2937288 : Nat := 1005493709789072720594443

theorem tailTrace_2937288 : CollatzResearch.WordTrace tailWord_2937288 prefixEnd_2937288 1005493709789072720594443 := by
  unfold tailWord_2937288
  simp only [CollatzResearch.WordTrace]
  refine ⟨53565847291357349848602259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71421129721809799798136345 53565847291357349848602259)
  ·
    refine ⟨80348770937036024772903389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53565847291357349848602259 80348770937036024772903389)
    ·
      refine ⟨30130789101388509289838771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80348770937036024772903389 30130789101388509289838771)
      ·
        refine ⟨45196183652082763934758157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30130789101388509289838771 45196183652082763934758157)
        ·
          refine ⟨16948568869531036475534309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45196183652082763934758157 16948568869531036475534309)
          ·
            refine ⟨3177856663037069339162683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16948568869531036475534309 3177856663037069339162683)
            ·
              refine ⟨4766784994555604008744025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177856663037069339162683 4766784994555604008744025)
              ·
                refine ⟨3575088745916703006558019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4766784994555604008744025 3575088745916703006558019)
                ·
                  refine ⟨5362633118875054509837029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575088745916703006558019 5362633118875054509837029)
                  ·
                    refine ⟨1005493709789072720594443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5362633118875054509837029 1005493709789072720594443)
                    ·
                      rfl

theorem cell22_2937288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_2937288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937288 prefixEnd_2937288 := by exact prefixLift 2937288
  have htrace : WordTrace (prefixWord ++ tailWord_2937288) baseStart_2937288 baseEnd_2937288 := by
    simpa [prefixWord, tailWord_2937288, baseEnd_2937288] using wordTrace_append hprefix tailTrace_2937288
  have hstable : (prefixWord ++ tailWord_2937288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937288).length < 2 ^ (prefixWord ++ tailWord_2937288).sum := by decide
  have hdescent : baseEnd_2937288 < baseStart_2937288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937301 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2937301 : Nat := 118140960795 + 2937301 * 2 ^ 59
def prefixEnd_2937301 : Nat := 4983230072969 + 3 ^ 40 * 2937301 * 2
def baseEnd_2937301 : Nat := 1005498159954745020019403

theorem tailTrace_2937301 : CollatzResearch.WordTrace tailWord_2937301 prefixEnd_2937301 1005498159954745020019403 := by
  unfold tailWord_2937301
  simp only [CollatzResearch.WordTrace]
  refine ⟨107132168731667602917427757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71421445821111735278285171 107132168731667602917427757)
  ·
    refine ⟨40174563274375351094035409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107132168731667602917427757 40174563274375351094035409)
    ·
      refine ⟨30130922455781513320526557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40174563274375351094035409 30130922455781513320526557)
      ·
        refine ⟨11299095920918067495197459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30130922455781513320526557 11299095920918067495197459)
        ·
          refine ⟨16948643881377101242796189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11299095920918067495197459 16948643881377101242796189)
          ·
            refine ⟨6355741455516412966048571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16948643881377101242796189 6355741455516412966048571)
            ·
              refine ⟨9533612183274619449072857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6355741455516412966048571 9533612183274619449072857)
              ·
                refine ⟨7150209137455964586804643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9533612183274619449072857 7150209137455964586804643)
                ·
                  refine ⟨10725313706183946880206965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7150209137455964586804643 10725313706183946880206965)
                  ·
                    refine ⟨1005498159954745020019403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10725313706183946880206965 1005498159954745020019403)
                    ·
                      rfl

theorem cell22_2937301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2937301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937301 prefixEnd_2937301 := by exact prefixLift 2937301
  have htrace : WordTrace (prefixWord ++ tailWord_2937301) baseStart_2937301 baseEnd_2937301 := by
    simpa [prefixWord, tailWord_2937301, baseEnd_2937301] using wordTrace_append hprefix tailTrace_2937301
  have hstable : (prefixWord ++ tailWord_2937301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937301).length < 2 ^ (prefixWord ++ tailWord_2937301).sum := by decide
  have hdescent : baseEnd_2937301 < baseStart_2937301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937320 : List Nat := [2, 1, 4, 1, 1, 5, 2, 2, 4]
def baseStart_2937320 : Nat := 118140960795 + 2937320 * 2 ^ 59
def prefixEnd_2937320 : Nat := 4983230072969 + 3 ^ 40 * 2937320 * 2
def baseEnd_2937320 : Nat := 335168221347678434598115

theorem tailTrace_2937320 : CollatzResearch.WordTrace tailWord_2937320 prefixEnd_2937320 335168221347678434598115 := by
  unfold tailWord_2937320
  simp only [CollatzResearch.WordTrace]
  refine ⟨53566430859299384581184707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71421907812399179441579609 53566430859299384581184707)
  ·
    refine ⟨80349646288949076871777061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53566430859299384581184707 80349646288949076871777061)
    ·
      refine ⟨15065558679177951913458199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80349646288949076871777061 15065558679177951913458199)
      ·
        refine ⟨22598338018766927870187299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15065558679177951913458199 22598338018766927870187299)
        ·
          refine ⟨33897507028150391805280949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22598338018766927870187299 33897507028150391805280949)
          ·
            refine ⟨3177891283889099231745089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33897507028150391805280949 3177891283889099231745089)
            ·
              refine ⟨2383418462916824423808817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3177891283889099231745089 2383418462916824423808817)
              ·
                refine ⟨1787563847187618317856613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2383418462916824423808817 1787563847187618317856613)
                ·
                  refine ⟨335168221347678434598115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1787563847187618317856613 335168221347678434598115)
                  ·
                    rfl

theorem cell22_2937320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 2, 4].length) (baseStart_2937320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937320 prefixEnd_2937320 := by exact prefixLift 2937320
  have htrace : WordTrace (prefixWord ++ tailWord_2937320) baseStart_2937320 baseEnd_2937320 := by
    simpa [prefixWord, tailWord_2937320, baseEnd_2937320] using wordTrace_append hprefix tailTrace_2937320
  have hstable : (prefixWord ++ tailWord_2937320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937320).length < 2 ^ (prefixWord ++ tailWord_2937320).sum := by decide
  have hdescent : baseEnd_2937320 < baseStart_2937320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937348 : List Nat := [2, 3, 2, 3, 1, 2, 3, 6]
def baseStart_2937348 : Nat := 118140960795 + 2937348 * 2 ^ 59
def prefixEnd_2937348 : Nat := 4983230072969 + 3 ^ 40 * 2937348 * 2
def baseEnd_2937348 : Nat := 111723805446139173788251

theorem tailTrace_2937348 : CollatzResearch.WordTrace tailWord_2937348 prefixEnd_2937348 111723805446139173788251 := by
  unfold tailWord_2937348
  simp only [CollatzResearch.WordTrace]
  refine ⟨53566941481248664972194349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71422588641664886629592465 53566941481248664972194349)
  ·
    refine ⟨20087603055468249364572881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53566941481248664972194349 20087603055468249364572881)
    ·
      refine ⟨15065702291601187023429661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20087603055468249364572881 15065702291601187023429661)
      ·
        refine ⟨5649638359350445133786123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15065702291601187023429661 5649638359350445133786123)
        ·
          refine ⟨8474457539025667700679185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5649638359350445133786123 8474457539025667700679185)
          ·
            refine ⟨6355843154269250775509389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8474457539025667700679185 6355843154269250775509389)
            ·
              refine ⟨2383441182850969040816021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6355843154269250775509389 2383441182850969040816021)
              ·
                refine ⟨111723805446139173788251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2383441182850969040816021 111723805446139173788251)
                ·
                  rfl

theorem cell22_2937348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 3, 6].length) (baseStart_2937348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937348 prefixEnd_2937348 := by exact prefixLift 2937348
  have htrace : WordTrace (prefixWord ++ tailWord_2937348) baseStart_2937348 baseEnd_2937348 := by
    simpa [prefixWord, tailWord_2937348, baseEnd_2937348] using wordTrace_append hprefix tailTrace_2937348
  have hstable : (prefixWord ++ tailWord_2937348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937348).length < 2 ^ (prefixWord ++ tailWord_2937348).sum := by decide
  have hdescent : baseEnd_2937348 < baseStart_2937348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937414 : List Nat := [6, 1, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2937414 : Nat := 118140960795 + 2937414 * 2 ^ 59
def prefixEnd_2937414 : Nat := 4983230072969 + 3 ^ 40 * 2937414 * 2
def baseEnd_2937414 : Nat := 1005536842164050391944057

theorem tailTrace_2937414 : CollatzResearch.WordTrace tailWord_2937414 prefixEnd_2937414 1005536842164050391944057 := by
  unfold tailWord_2937414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348009068133069475509103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71424193453505482144194197 3348009068133069475509103)
  ·
    refine ⟨5022013602199604213263655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3348009068133069475509103 5022013602199604213263655)
    ·
      refine ⟨7533020403299406319895483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5022013602199604213263655 7533020403299406319895483)
      ·
        refine ⟨11299530604949109479843225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7533020403299406319895483 11299530604949109479843225)
        ·
          refine ⟨8474647953711832109882419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11299530604949109479843225 8474647953711832109882419)
          ·
            refine ⟨12711971930567748164823629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474647953711832109882419 12711971930567748164823629)
            ·
              refine ⟨4766989473962905561808861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12711971930567748164823629 4766989473962905561808861)
              ·
                refine ⟨1787621052736089585678323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4766989473962905561808861 1787621052736089585678323)
                ·
                  refine ⟨2681431579104134378517485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787621052736089585678323 2681431579104134378517485)
                  ·
                    refine ⟨1005536842164050391944057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681431579104134378517485 1005536842164050391944057)
                    ·
                      rfl

theorem cell22_2937414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2937414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937414 prefixEnd_2937414 := by exact prefixLift 2937414
  have htrace : WordTrace (prefixWord ++ tailWord_2937414) baseStart_2937414 baseEnd_2937414 := by
    simpa [prefixWord, tailWord_2937414, baseEnd_2937414] using wordTrace_append hprefix tailTrace_2937414
  have hstable : (prefixWord ++ tailWord_2937414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937414).length < 2 ^ (prefixWord ++ tailWord_2937414).sum := by decide
  have hdescent : baseEnd_2937414 < baseStart_2937414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937496 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_2937496 : Nat := 118140960795 + 2937496 * 2 ^ 59
def prefixEnd_2937496 : Nat := 4983230072969 + 3 ^ 40 * 2937496 * 2
def baseEnd_2937496 : Nat := 1005564912439829511393805

theorem tailTrace_2937496 : CollatzResearch.WordTrace tailWord_2937496 prefixEnd_2937496 1005564912439829511393805 := by
  unfold tailWord_2937496
  simp only [CollatzResearch.WordTrace]
  refine ⟨53569640482980575610388171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71426187310640767480517561 53569640482980575610388171)
  ·
    refine ⟨80354460724470863415582257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53569640482980575610388171 80354460724470863415582257)
    ·
      refine ⟨60265845543353147561686693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80354460724470863415582257 60265845543353147561686693)
      ·
        refine ⟨11299846039378715167816255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60265845543353147561686693 11299846039378715167816255)
        ·
          refine ⟨16949769059068072751724383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11299846039378715167816255 16949769059068072751724383)
          ·
            refine ⟨25424653588602109127586575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16949769059068072751724383 25424653588602109127586575)
            ·
              refine ⟨38136980382903163691379863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25424653588602109127586575 38136980382903163691379863)
              ·
                refine ⟨57205470574354745537069795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38136980382903163691379863 57205470574354745537069795)
                ·
                  refine ⟨85808205861532118305604693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57205470574354745537069795 85808205861532118305604693)
                  ·
                    refine ⟨1005564912439829511393805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85808205861532118305604693 1005564912439829511393805)
                    ·
                      rfl

theorem cell22_2937496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_2937496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937496 prefixEnd_2937496 := by exact prefixLift 2937496
  have htrace : WordTrace (prefixWord ++ tailWord_2937496) baseStart_2937496 baseEnd_2937496 := by
    simpa [prefixWord, tailWord_2937496, baseEnd_2937496] using wordTrace_append hprefix tailTrace_2937496
  have hstable : (prefixWord ++ tailWord_2937496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937496).length < 2 ^ (prefixWord ++ tailWord_2937496).sum := by decide
  have hdescent : baseEnd_2937496 < baseStart_2937496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937532 : List Nat := [2, 2, 2, 3, 1, 1, 4, 3, 1, 3]
def baseStart_2937532 : Nat := 118140960795 + 2937532 * 2 ^ 59
def prefixEnd_2937532 : Nat := 4983230072969 + 3 ^ 40 * 2937532 * 2
def baseEnd_2937532 : Nat := 1005577235975537417493695

theorem tailTrace_2937532 : CollatzResearch.WordTrace tailWord_2937532 prefixEnd_2937532 1005577235975537417493695 := by
  unfold tailWord_2937532
  simp only [CollatzResearch.WordTrace]
  refine ⟨53570296996915364684543425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71427062662553819579391233 53570296996915364684543425)
  ·
    refine ⟨40177722747686523513407569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53570296996915364684543425 40177722747686523513407569)
    ·
      refine ⟨30133292060764892635055677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40177722747686523513407569 30133292060764892635055677)
      ·
        refine ⟨11299984522786834738145879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30133292060764892635055677 11299984522786834738145879)
        ·
          refine ⟨16949976784180252107218819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11299984522786834738145879 16949976784180252107218819)
          ·
            refine ⟨25424965176270378160828229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16949976784180252107218819 25424965176270378160828229)
            ·
              refine ⟨4767180970550695905155293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25424965176270378160828229 4767180970550695905155293)
              ·
                refine ⟨1787692863956510964433235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4767180970550695905155293 1787692863956510964433235)
                ·
                  refine ⟨2681539295934766446649853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787692863956510964433235 2681539295934766446649853)
                  ·
                    refine ⟨1005577235975537417493695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681539295934766446649853 1005577235975537417493695)
                    ·
                      rfl

theorem cell22_2937532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_2937532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937532 prefixEnd_2937532 := by exact prefixLift 2937532
  have htrace : WordTrace (prefixWord ++ tailWord_2937532) baseStart_2937532 baseEnd_2937532 := by
    simpa [prefixWord, tailWord_2937532, baseEnd_2937532] using wordTrace_append hprefix tailTrace_2937532
  have hstable : (prefixWord ++ tailWord_2937532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937532).length < 2 ^ (prefixWord ++ tailWord_2937532).sum := by decide
  have hdescent : baseEnd_2937532 < baseStart_2937532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937549 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2937549 : Nat := 118140960795 + 2937549 * 2 ^ 59
def prefixEnd_2937549 : Nat := 4983230072969 + 3 ^ 40 * 2937549 * 2
def baseEnd_2937549 : Nat := 1005583055422955039818643

theorem tailTrace_2937549 : CollatzResearch.WordTrace tailWord_2937549 prefixEnd_2937549 1005583055422955039818643 := by
  unfold tailWord_2937549
  simp only [CollatzResearch.WordTrace]
  refine ⟨107141214034769141272455701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71427476023179427514970467 107141214034769141272455701)
  ·
    refine ⟨5022244407879803497146361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107141214034769141272455701 5022244407879803497146361)
    ·
      refine ⟨3766683305909852622859771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5022244407879803497146361 3766683305909852622859771)
      ·
        refine ⟨5650024958864778934289657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3766683305909852622859771 5650024958864778934289657)
        ·
          refine ⟨4237518719148584200717243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5650024958864778934289657 4237518719148584200717243)
          ·
            refine ⟨6356278078722876301075865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237518719148584200717243 6356278078722876301075865)
            ·
              refine ⟨4767208559042157225806899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6356278078722876301075865 4767208559042157225806899)
              ·
                refine ⟨7150812838563235838710349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767208559042157225806899 7150812838563235838710349)
                ·
                  refine ⟨2681554814461213439516381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7150812838563235838710349 2681554814461213439516381)
                  ·
                    refine ⟨1005583055422955039818643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681554814461213439516381 1005583055422955039818643)
                    ·
                      rfl

theorem cell22_2937549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2937549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937549 prefixEnd_2937549 := by exact prefixLift 2937549
  have htrace : WordTrace (prefixWord ++ tailWord_2937549) baseStart_2937549 baseEnd_2937549 := by
    simpa [prefixWord, tailWord_2937549, baseEnd_2937549] using wordTrace_append hprefix tailTrace_2937549
  have hstable : (prefixWord ++ tailWord_2937549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937549).length < 2 ^ (prefixWord ++ tailWord_2937549).sum := by decide
  have hdescent : baseEnd_2937549 < baseStart_2937549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937573 : List Nat := [1, 3, 1, 4, 1, 2, 2, 2, 6]
def baseStart_2937573 : Nat := 118140960795 + 2937573 * 2 ^ 59
def prefixEnd_2937573 : Nat := 4983230072969 + 3 ^ 40 * 2937573 * 2
def baseEnd_2937573 : Nat := 335197090371142325739523

theorem tailTrace_2937573 : CollatzResearch.WordTrace tailWord_2937573 prefixEnd_2937573 335197090371142325739523 := by
  unfold tailWord_2937573
  simp only [CollatzResearch.WordTrace]
  refine ⟨107142089386682193371329373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71428059591121462247552915 107142089386682193371329373)
  ·
    refine ⟨40178283520005822514248515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107142089386682193371329373 40178283520005822514248515)
    ·
      refine ⟨60267425280008733771372773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40178283520005822514248515 60267425280008733771372773)
      ·
        refine ⟨11300142240001637582132395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60267425280008733771372773 11300142240001637582132395)
        ·
          refine ⟨16950213360002456373198593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11300142240001637582132395 16950213360002456373198593)
          ·
            refine ⟨12712660020001842279898945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16950213360002456373198593 12712660020001842279898945)
            ·
              refine ⟨9534495015001381709924209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12712660020001842279898945 9534495015001381709924209)
              ·
                refine ⟨7150871261251036282443157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9534495015001381709924209 7150871261251036282443157)
                ·
                  refine ⟨335197090371142325739523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7150871261251036282443157 335197090371142325739523)
                  ·
                    rfl

theorem cell22_2937573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_2937573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937573 prefixEnd_2937573 := by exact prefixLift 2937573
  have htrace : WordTrace (prefixWord ++ tailWord_2937573) baseStart_2937573 baseEnd_2937573 := by
    simpa [prefixWord, tailWord_2937573, baseEnd_2937573] using wordTrace_append hprefix tailTrace_2937573
  have hstable : (prefixWord ++ tailWord_2937573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937573).length < 2 ^ (prefixWord ++ tailWord_2937573).sum := by decide
  have hdescent : baseEnd_2937573 < baseStart_2937573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937667 : List Nat := [1, 1, 1, 3, 1, 4, 3, 4, 1, 3]
def baseStart_2937667 : Nat := 118140960795 + 2937667 * 2 ^ 59
def prefixEnd_2937667 : Nat := 4983230072969 + 3 ^ 40 * 2937667 * 2
def baseEnd_2937667 : Nat := 1005623449234442065368281

theorem tailTrace_2937667 : CollatzResearch.WordTrace tailWord_2937667 prefixEnd_2937667 1005623449234442065368281 := by
  unfold tailWord_2937667
  simp only [CollatzResearch.WordTrace]
  refine ⟨107145517848341647425251255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71430345232227764950167503 107145517848341647425251255)
  ·
    refine ⟨160718276772512471137876883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107145517848341647425251255 160718276772512471137876883)
    ·
      refine ⟨241077415158768706706815325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160718276772512471137876883 241077415158768706706815325)
      ·
        refine ⟨90404030684538265015055747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241077415158768706706815325 90404030684538265015055747)
        ·
          refine ⟨135606046026807397522583621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90404030684538265015055747 135606046026807397522583621)
          ·
            refine ⟨25426133630026387035484429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135606046026807397522583621 25426133630026387035484429)
            ·
              refine ⟨9534800111259895138306661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25426133630026387035484429 9534800111259895138306661)
              ·
                refine ⟨1787775020861230338432499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9534800111259895138306661 1787775020861230338432499)
                ·
                  refine ⟨2681662531291845507648749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787775020861230338432499 2681662531291845507648749)
                  ·
                    refine ⟨1005623449234442065368281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681662531291845507648749 1005623449234442065368281)
                    ·
                      rfl

theorem cell22_2937667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 1, 3].length) (baseStart_2937667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937667 prefixEnd_2937667 := by exact prefixLift 2937667
  have htrace : WordTrace (prefixWord ++ tailWord_2937667) baseStart_2937667 baseEnd_2937667 := by
    simpa [prefixWord, tailWord_2937667, baseEnd_2937667] using wordTrace_append hprefix tailTrace_2937667
  have hstable : (prefixWord ++ tailWord_2937667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937667).length < 2 ^ (prefixWord ++ tailWord_2937667).sum := by decide
  have hdescent : baseEnd_2937667 < baseStart_2937667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937708 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 8]
def baseStart_2937708 : Nat := 118140960795 + 2937708 * 2 ^ 59
def prefixEnd_2937708 : Nat := 4983230072969 + 3 ^ 40 * 2937708 * 2
def baseEnd_2937708 : Nat := 335212494790777208364385

theorem tailTrace_2937708 : CollatzResearch.WordTrace tailWord_2937708 prefixEnd_2937708 335212494790777208364385 := by
  unfold tailWord_2937708
  simp only [CollatzResearch.WordTrace]
  refine ⟨53573506620596555713746889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71431342160795407618329185 53573506620596555713746889)
  ·
    refine ⟨40180129965447416785310167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53573506620596555713746889 40180129965447416785310167)
    ·
      refine ⟨60270194948171125177965251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40180129965447416785310167 60270194948171125177965251)
      ·
        refine ⟨90405292422256687766947877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60270194948171125177965251 90405292422256687766947877)
        ·
          refine ⟨16950992329173128956302727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90405292422256687766947877 16950992329173128956302727)
          ·
            refine ⟨25426488493759693434454091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16950992329173128956302727 25426488493759693434454091)
            ·
              refine ⟨38139732740639540151681137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25426488493759693434454091 38139732740639540151681137)
              ·
                refine ⟨28604799555479655113760853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38139732740639540151681137 28604799555479655113760853)
                ·
                  refine ⟨335212494790777208364385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28604799555479655113760853 335212494790777208364385)
                  ·
                    rfl

theorem cell22_2937708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_2937708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937708 prefixEnd_2937708 := by exact prefixLift 2937708
  have htrace : WordTrace (prefixWord ++ tailWord_2937708) baseStart_2937708 baseEnd_2937708 := by
    simpa [prefixWord, tailWord_2937708, baseEnd_2937708] using wordTrace_append hprefix tailTrace_2937708
  have hstable : (prefixWord ++ tailWord_2937708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937708).length < 2 ^ (prefixWord ++ tailWord_2937708).sum := by decide
  have hdescent : baseEnd_2937708 < baseStart_2937708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937723 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 3, 5]
def baseStart_2937723 : Nat := 118140960795 + 2937723 * 2 ^ 59
def prefixEnd_2937723 : Nat := 4983230072969 + 3 ^ 40 * 2937723 * 2
def baseEnd_2937723 : Nat := 1005642619178876585968109

theorem tailTrace_2937723 : CollatzResearch.WordTrace tailWord_2937723 prefixEnd_2937723 1005642619178876585968109 := by
  unfold tailWord_2937723
  simp only [CollatzResearch.WordTrace]
  refine ⟨107147560336138768989289823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71431706890759179326193215 107147560336138768989289823)
  ·
    refine ⟨160721340504208153483934735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107147560336138768989289823 160721340504208153483934735)
    ·
      refine ⟨241082010756312230225902103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160721340504208153483934735 241082010756312230225902103)
      ·
        refine ⟨361623016134468345338853155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241082010756312230225902103 361623016134468345338853155)
        ·
          refine ⟨542434524201702518008279733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361623016134468345338853155 542434524201702518008279733)
          ·
            refine ⟨50853236643909611063276225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 542434524201702518008279733 50853236643909611063276225)
            ·
              refine ⟨38139927482932208297457169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50853236643909611063276225 38139927482932208297457169)
              ·
                refine ⟨28604945612199156223092877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38139927482932208297457169 28604945612199156223092877)
                ·
                  refine ⟨10726854604574683583659829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28604945612199156223092877 10726854604574683583659829)
                  ·
                    refine ⟨1005642619178876585968109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10726854604574683583659829 1005642619178876585968109)
                    ·
                      rfl

theorem cell22_2937723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_2937723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937723 prefixEnd_2937723 := by exact prefixLift 2937723
  have htrace : WordTrace (prefixWord ++ tailWord_2937723) baseStart_2937723 baseEnd_2937723 := by
    simpa [prefixWord, tailWord_2937723, baseEnd_2937723] using wordTrace_append hprefix tailTrace_2937723
  have hstable : (prefixWord ++ tailWord_2937723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937723).length < 2 ^ (prefixWord ++ tailWord_2937723).sum := by decide
  have hdescent : baseEnd_2937723 < baseStart_2937723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937740 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_2937740 : Nat := 118140960795 + 2937740 * 2 ^ 59
def prefixEnd_2937740 : Nat := 4983230072969 + 3 ^ 40 * 2937740 * 2
def baseEnd_2937740 : Nat := 1005648438626294208293057

theorem tailTrace_2937740 : CollatzResearch.WordTrace tailWord_2937740 prefixEnd_2937740 1005648438626294208293057 := by
  unfold tailWord_2937740
  simp only [CollatzResearch.WordTrace]
  refine ⟨53574090188538590446329337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71432120251384787261772449 53574090188538590446329337)
  ·
    refine ⟨40180567641403942834747003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53574090188538590446329337 40180567641403942834747003)
    ·
      refine ⟨60270851462105914252120505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40180567641403942834747003 60270851462105914252120505)
      ·
        refine ⟨45203138596579435689090379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60270851462105914252120505 45203138596579435689090379)
        ·
          refine ⟨67804707894869153533635569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45203138596579435689090379 67804707894869153533635569)
          ·
            refine ⟨50853530921151865150226677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67804707894869153533635569 50853530921151865150226677)
            ·
              refine ⟨4767518523857987357833751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50853530921151865150226677 4767518523857987357833751)
              ·
                refine ⟨7151277785786981036750627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767518523857987357833751 7151277785786981036750627)
                ·
                  refine ⟨10726916678680471555125941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7151277785786981036750627 10726916678680471555125941)
                  ·
                    refine ⟨1005648438626294208293057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10726916678680471555125941 1005648438626294208293057)
                    ·
                      rfl

theorem cell22_2937740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_2937740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937740 prefixEnd_2937740 := by exact prefixLift 2937740
  have htrace : WordTrace (prefixWord ++ tailWord_2937740) baseStart_2937740 baseEnd_2937740 := by
    simpa [prefixWord, tailWord_2937740, baseEnd_2937740] using wordTrace_append hprefix tailTrace_2937740
  have hstable : (prefixWord ++ tailWord_2937740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937740).length < 2 ^ (prefixWord ++ tailWord_2937740).sum := by decide
  have hdescent : baseEnd_2937740 < baseStart_2937740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937759 : List Nat := [1, 1, 2, 5, 2, 3, 1, 3, 4]
def baseStart_2937759 : Nat := 118140960795 + 2937759 * 2 ^ 59
def prefixEnd_2937759 : Nat := 4983230072969 + 3 ^ 40 * 2937759 * 2
def baseEnd_2937759 : Nat := 335218314238194830689333

theorem tailTrace_2937759 : CollatzResearch.WordTrace tailWord_2937759 prefixEnd_2937759 335218314238194830689333 := by
  unfold tailWord_2937759
  simp only [CollatzResearch.WordTrace]
  refine ⟨107148873364008347137600331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71432582242672231425066887 107148873364008347137600331)
  ·
    refine ⟨160723310046012520706400497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107148873364008347137600331 160723310046012520706400497)
    ·
      refine ⟨120542482534509390529800373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160723310046012520706400497 120542482534509390529800373)
      ·
        refine ⟨11300857737610255362168785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120542482534509390529800373 11300857737610255362168785)
        ·
          refine ⟨8475643303207691521626589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11300857737610255362168785 8475643303207691521626589)
          ·
            refine ⟨3178366238702884320609971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8475643303207691521626589 3178366238702884320609971)
            ·
              refine ⟨4767549358054326480914957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178366238702884320609971 4767549358054326480914957)
              ·
                refine ⟨1787831009270372430343109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4767549358054326480914957 1787831009270372430343109)
                ·
                  refine ⟨335218314238194830689333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1787831009270372430343109 335218314238194830689333)
                  ·
                    rfl

theorem cell22_2937759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 4].length) (baseStart_2937759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937759 prefixEnd_2937759 := by exact prefixLift 2937759
  have htrace : WordTrace (prefixWord ++ tailWord_2937759) baseStart_2937759 baseEnd_2937759 := by
    simpa [prefixWord, tailWord_2937759, baseEnd_2937759] using wordTrace_append hprefix tailTrace_2937759
  have hstable : (prefixWord ++ tailWord_2937759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937759).length < 2 ^ (prefixWord ++ tailWord_2937759).sum := by decide
  have hdescent : baseEnd_2937759 < baseStart_2937759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937879 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 1, 4]
def baseStart_2937879 : Nat := 118140960795 + 2937879 * 2 ^ 59
def prefixEnd_2937879 : Nat := 4983230072969 + 3 ^ 40 * 2937879 * 2
def baseEnd_2937879 : Nat := 1005696021166944179067631

theorem tailTrace_2937879 : CollatzResearch.WordTrace tailWord_2937879 prefixEnd_2937879 1005696021166944179067631 := by
  unfold tailWord_2937879
  simp only [CollatzResearch.WordTrace]
  refine ⟨107153250123573607631968691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71435500082382405087979127 107153250123573607631968691)
  ·
    refine ⟨160729875185360411447953037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107153250123573607631968691 160729875185360411447953037)
    ·
      refine ⟨60273703194510154292982389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160729875185360411447953037 60273703194510154292982389)
      ·
        refine ⟨5650659674485326964967099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60273703194510154292982389 5650659674485326964967099)
        ·
          refine ⟨8475989511727990447450649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5650659674485326964967099 8475989511727990447450649)
          ·
            refine ⟨6356992133795992835587987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8475989511727990447450649 6356992133795992835587987)
            ·
              refine ⟨9535488200693989253381981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6356992133795992835587987 9535488200693989253381981)
              ·
                refine ⟨3575808075260245970018243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9535488200693989253381981 3575808075260245970018243)
                ·
                  refine ⟨5363712112890368955027365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575808075260245970018243 5363712112890368955027365)
                  ·
                    refine ⟨1005696021166944179067631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5363712112890368955027365 1005696021166944179067631)
                    ·
                      rfl

theorem cell22_2937879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_2937879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937879 prefixEnd_2937879 := by exact prefixLift 2937879
  have htrace : WordTrace (prefixWord ++ tailWord_2937879) baseStart_2937879 baseEnd_2937879 := by
    simpa [prefixWord, tailWord_2937879, baseEnd_2937879] using wordTrace_append hprefix tailTrace_2937879
  have hstable : (prefixWord ++ tailWord_2937879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937879).length < 2 ^ (prefixWord ++ tailWord_2937879).sum := by decide
  have hdescent : baseEnd_2937879 < baseStart_2937879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937905 : List Nat := [1, 2, 2, 3, 1, 2, 2, 9]
def baseStart_2937905 : Nat := 118140960795 + 2937905 * 2 ^ 59
def prefixEnd_2937905 : Nat := 4983230072969 + 3 ^ 40 * 2937905 * 2
def baseEnd_2937905 : Nat := 111744991277587641990839

theorem tailTrace_2937905 : CollatzResearch.WordTrace tailWord_2937905 prefixEnd_2937905 111744991277587641990839 := by
  unfold tailWord_2937905
  simp only [CollatzResearch.WordTrace]
  refine ⟨107154198421479414072415169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71436132280986276048276779 107154198421479414072415169)
  ·
    refine ⟨80365648816109560554311377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107154198421479414072415169 80365648816109560554311377)
    ·
      refine ⟨60274236612082170415733533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80365648816109560554311377 60274236612082170415733533)
      ·
        refine ⟨22602838729530813905900075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60274236612082170415733533 22602838729530813905900075)
        ·
          refine ⟨33904258094296220858850113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22602838729530813905900075 33904258094296220858850113)
          ·
            refine ⟨25428193570722165644137585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33904258094296220858850113 25428193570722165644137585)
            ·
              refine ⟨19071145178041624233103189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25428193570722165644137585 19071145178041624233103189)
              ·
                refine ⟨111744991277587641990839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19071145178041624233103189 111744991277587641990839)
                ·
                  rfl

theorem cell22_2937905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 9].length) (baseStart_2937905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937905 prefixEnd_2937905 := by exact prefixLift 2937905
  have htrace : WordTrace (prefixWord ++ tailWord_2937905) baseStart_2937905 baseEnd_2937905 := by
    simpa [prefixWord, tailWord_2937905, baseEnd_2937905] using wordTrace_append hprefix tailTrace_2937905
  have hstable : (prefixWord ++ tailWord_2937905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937905).length < 2 ^ (prefixWord ++ tailWord_2937905).sum := by decide
  have hdescent : baseEnd_2937905 < baseStart_2937905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937920 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_2937920 : Nat := 118140960795 + 2937920 * 2 ^ 59
def prefixEnd_2937920 : Nat := 4983230072969 + 3 ^ 40 * 2937920 * 2
def baseEnd_2937920 : Nat := 1005710056304833738792505

theorem tailTrace_2937920 : CollatzResearch.WordTrace tailWord_2937920 prefixEnd_2937920 1005710056304833738792505 := by
  unfold tailWord_2937920
  simp only [CollatzResearch.WordTrace]
  refine ⟨53577372758212535817105607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71436497010950047756140809 53577372758212535817105607)
  ·
    refine ⟨80366059137318803725658411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53577372758212535817105607 80366059137318803725658411)
    ·
      refine ⟨120549088705978205588487617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80366059137318803725658411 120549088705978205588487617)
      ·
        refine ⟨90411816529483654191365713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120549088705978205588487617 90411816529483654191365713)
        ·
          refine ⟨67808862397112740643524285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90411816529483654191365713 67808862397112740643524285)
          ·
            refine ⟨25428323398917277741321607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67808862397112740643524285 25428323398917277741321607)
            ·
              refine ⟨38142485098375916611982411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25428323398917277741321607 38142485098375916611982411)
              ·
                refine ⟨57213727647563874917973617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38142485098375916611982411 57213727647563874917973617)
                ·
                  refine ⟨42910295735672906188480213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57213727647563874917973617 42910295735672906188480213)
                  ·
                    refine ⟨1005710056304833738792505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42910295735672906188480213 1005710056304833738792505)
                    ·
                      rfl

theorem cell22_2937920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_2937920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937920 prefixEnd_2937920 := by exact prefixLift 2937920
  have htrace : WordTrace (prefixWord ++ tailWord_2937920) baseStart_2937920 baseEnd_2937920 := by
    simpa [prefixWord, tailWord_2937920, baseEnd_2937920] using wordTrace_append hprefix tailTrace_2937920
  have hstable : (prefixWord ++ tailWord_2937920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937920).length < 2 ^ (prefixWord ++ tailWord_2937920).sum := by decide
  have hdescent : baseEnd_2937920 < baseStart_2937920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937926 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2937926 : Nat := 118140960795 + 2937926 * 2 ^ 59
def prefixEnd_2937926 : Nat := 4983230072969 + 3 ^ 40 * 2937926 * 2
def baseEnd_2937926 : Nat := 1005712110227451723142487

theorem tailTrace_2937926 : CollatzResearch.WordTrace tailWord_2937926 prefixEnd_2937926 1005712110227451723142487 := by
  unfold tailWord_2937926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348592636075104208091551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71436642902935556439286421 3348592636075104208091551)
  ·
    refine ⟨5022888954112656312137327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3348592636075104208091551 5022888954112656312137327)
    ·
      refine ⟨7534333431168984468205991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5022888954112656312137327 7534333431168984468205991)
      ·
        refine ⟨11301500146753476702308987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7534333431168984468205991 11301500146753476702308987)
        ·
          refine ⟨16952250220130215053463481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11301500146753476702308987 16952250220130215053463481)
          ·
            refine ⟨12714187665097661290097611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16952250220130215053463481 12714187665097661290097611)
            ·
              refine ⟨19071281497646491935146417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12714187665097661290097611 19071281497646491935146417)
              ·
                refine ⟨14303461123234868951359813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19071281497646491935146417 14303461123234868951359813)
                ·
                  refine ⟨2681898960606537928379965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14303461123234868951359813 2681898960606537928379965)
                  ·
                    refine ⟨1005712110227451723142487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681898960606537928379965 1005712110227451723142487)
                    ·
                      rfl

theorem cell22_2937926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2937926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937926 prefixEnd_2937926 := by exact prefixLift 2937926
  have htrace : WordTrace (prefixWord ++ tailWord_2937926) baseStart_2937926 baseEnd_2937926 := by
    simpa [prefixWord, tailWord_2937926, baseEnd_2937926] using wordTrace_append hprefix tailTrace_2937926
  have hstable : (prefixWord ++ tailWord_2937926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937926).length < 2 ^ (prefixWord ++ tailWord_2937926).sum := by decide
  have hdescent : baseEnd_2937926 < baseStart_2937926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937937 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 5, 3]
def baseStart_2937937 : Nat := 118140960795 + 2937937 * 2 ^ 59
def prefixEnd_2937937 : Nat := 4983230072969 + 3 ^ 40 * 2937937 * 2
def baseEnd_2937937 : Nat := 1005715875752251361117453

theorem tailTrace_2937937 : CollatzResearch.WordTrace tailWord_2937937 prefixEnd_2937937 1005715875752251361117453 := by
  unfold tailWord_2937937
  simp only [CollatzResearch.WordTrace]
  refine ⟨107155365557363483537580065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71436910371575655691720043 107155365557363483537580065)
  ·
    refine ⟨80366524168022612653185049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107155365557363483537580065 80366524168022612653185049)
    ·
      refine ⟨60274893126016959489888787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80366524168022612653185049 60274893126016959489888787)
      ·
        refine ⟨90412339689025439234833181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60274893126016959489888787 90412339689025439234833181)
        ·
          refine ⟨33904627383384539713062443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90412339689025439234833181 33904627383384539713062443)
          ·
            refine ⟨50856941075076809569593665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33904627383384539713062443 50856941075076809569593665)
            ·
              refine ⟨38142705806307607177195249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50856941075076809569593665 38142705806307607177195249)
              ·
                refine ⟨28607029354730705382896437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38142705806307607177195249 28607029354730705382896437)
                ·
                  refine ⟨2681909002006003629646541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28607029354730705382896437 2681909002006003629646541)
                  ·
                    refine ⟨1005715875752251361117453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681909002006003629646541 1005715875752251361117453)
                    ·
                      rfl

theorem cell22_2937937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_2937937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937937 prefixEnd_2937937 := by exact prefixLift 2937937
  have htrace : WordTrace (prefixWord ++ tailWord_2937937) baseStart_2937937 baseEnd_2937937 := by
    simpa [prefixWord, tailWord_2937937, baseEnd_2937937] using wordTrace_append hprefix tailTrace_2937937
  have hstable : (prefixWord ++ tailWord_2937937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937937).length < 2 ^ (prefixWord ++ tailWord_2937937).sum := by decide
  have hdescent : baseEnd_2937937 < baseStart_2937937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937960 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 2, 3]
def baseStart_2937960 : Nat := 118140960795 + 2937960 * 2 ^ 59
def prefixEnd_2937960 : Nat := 4983230072969 + 3 ^ 40 * 2937960 * 2
def baseEnd_2937960 : Nat := 1005723749122286967792383

theorem tailTrace_2937960 : CollatzResearch.WordTrace tailWord_2937960 prefixEnd_2937960 1005723749122286967792383 := by
  unfold tailWord_2937960
  simp only [CollatzResearch.WordTrace]
  refine ⟨53578102218140079232833667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71437469624186772310444889 53578102218140079232833667)
  ·
    refine ⟨80367153327210118849250501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53578102218140079232833667 80367153327210118849250501)
    ·
      refine ⟨15068841248851897284234469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80367153327210118849250501 15068841248851897284234469)
      ·
        refine ⟨2825407734159730740793963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15068841248851897284234469 2825407734159730740793963)
        ·
          refine ⟨4238111601239596111190945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825407734159730740793963 4238111601239596111190945)
          ·
            refine ⟨3178583700929697083393209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238111601239596111190945 3178583700929697083393209)
            ·
              refine ⟨2383937775697272812544907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178583700929697083393209 2383937775697272812544907)
              ·
                refine ⟨3575906663545909218817361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383937775697272812544907 3575906663545909218817361)
                ·
                  refine ⟨2681929997659431914113021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3575906663545909218817361 2681929997659431914113021)
                  ·
                    refine ⟨1005723749122286967792383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681929997659431914113021 1005723749122286967792383)
                    ·
                      rfl

theorem cell22_2937960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_2937960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937960 prefixEnd_2937960 := by exact prefixLift 2937960
  have htrace : WordTrace (prefixWord ++ tailWord_2937960) baseStart_2937960 baseEnd_2937960 := by
    simpa [prefixWord, tailWord_2937960, baseEnd_2937960] using wordTrace_append hprefix tailTrace_2937960
  have hstable : (prefixWord ++ tailWord_2937960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937960).length < 2 ^ (prefixWord ++ tailWord_2937960).sum := by decide
  have hdescent : baseEnd_2937960 < baseStart_2937960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937967 : List Nat := [1, 1, 2, 1, 3, 3, 3, 3, 5]
def baseStart_2937967 : Nat := 118140960795 + 2937967 * 2 ^ 59
def prefixEnd_2937967 : Nat := 4983230072969 + 3 ^ 40 * 2937967 * 2
def baseEnd_2937967 : Nat := 335242048455113760955787

theorem tailTrace_2937967 : CollatzResearch.WordTrace tailWord_2937967 prefixEnd_2937967 335242048455113760955787 := by
  unfold tailWord_2937967
  simp only [CollatzResearch.WordTrace]
  refine ⟨107156459747254798661172155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71437639831503199107448103 107156459747254798661172155)
  ·
    refine ⟨160734689620882197991758233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107156459747254798661172155 160734689620882197991758233)
    ·
      refine ⟨120551017215661648493818675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160734689620882197991758233 120551017215661648493818675)
      ·
        refine ⟨180826525823492472740728013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120551017215661648493818675 180826525823492472740728013)
        ·
          refine ⟨67809947183809677277773005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180826525823492472740728013 67809947183809677277773005)
          ·
            refine ⟨25428730193928628979164877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67809947183809677277773005 25428730193928628979164877)
            ·
              refine ⟨9535773822723235867186829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25428730193928628979164877 9535773822723235867186829)
              ·
                refine ⟨3575915183521213450195061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9535773822723235867186829 3575915183521213450195061)
                ·
                  refine ⟨335242048455113760955787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3575915183521213450195061 335242048455113760955787)
                  ·
                    rfl

theorem cell22_2937967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 5].length) (baseStart_2937967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2937967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2937967 prefixEnd_2937967 := by exact prefixLift 2937967
  have htrace : WordTrace (prefixWord ++ tailWord_2937967) baseStart_2937967 baseEnd_2937967 := by
    simpa [prefixWord, tailWord_2937967, baseEnd_2937967] using wordTrace_append hprefix tailTrace_2937967
  have hstable : (prefixWord ++ tailWord_2937967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937967).length < 2 ^ (prefixWord ++ tailWord_2937967).sum := by decide
  have hdescent : baseEnd_2937967 < baseStart_2937967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938044 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_2938044 : Nat := 118140960795 + 2938044 * 2 ^ 59
def prefixEnd_2938044 : Nat := 4983230072969 + 3 ^ 40 * 2938044 * 2
def baseEnd_2938044 : Nat := 1005752504038938748692125

theorem tailTrace_2938044 : CollatzResearch.WordTrace tailWord_2938044 prefixEnd_2938044 1005752504038938748692125 := by
  unfold tailWord_2938044
  simp only [CollatzResearch.WordTrace]
  refine ⟨53579634083987920405862593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71439512111983893874483457 53579634083987920405862593)
  ·
    refine ⟨40184725562990940304396945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53579634083987920405862593 40184725562990940304396945)
    ·
      refine ⟨30138544172243205228297709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40184725562990940304396945 30138544172243205228297709)
      ·
        refine ⟨11301954064591201960611641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30138544172243205228297709 11301954064591201960611641)
        ·
          refine ⟨8476465548443401470458731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11301954064591201960611641 8476465548443401470458731)
          ·
            refine ⟨12714698322665102205688097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8476465548443401470458731 12714698322665102205688097)
            ·
              refine ⟨9536023741998826654266073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12714698322665102205688097 9536023741998826654266073)
              ·
                refine ⟨7152017806499119990699555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9536023741998826654266073 7152017806499119990699555)
                ·
                  refine ⟨10728026709748679986049333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7152017806499119990699555 10728026709748679986049333)
                  ·
                    refine ⟨1005752504038938748692125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10728026709748679986049333 1005752504038938748692125)
                    ·
                      rfl

theorem cell22_2938044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_2938044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938044 prefixEnd_2938044 := by exact prefixLift 2938044
  have htrace : WordTrace (prefixWord ++ tailWord_2938044) baseStart_2938044 baseEnd_2938044 := by
    simpa [prefixWord, tailWord_2938044, baseEnd_2938044] using wordTrace_append hprefix tailTrace_2938044
  have hstable : (prefixWord ++ tailWord_2938044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938044).length < 2 ^ (prefixWord ++ tailWord_2938044).sum := by decide
  have hdescent : baseEnd_2938044 < baseStart_2938044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938046 : List Nat := [4, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_2938046 : Nat := 118140960795 + 2938046 * 2 ^ 59
def prefixEnd_2938046 : Nat := 4983230072969 + 3 ^ 40 * 2938046 * 2
def baseEnd_2938046 : Nat := 335251062893270470047373

theorem tailTrace_2938046 : CollatzResearch.WordTrace tailWord_2938046 prefixEnd_2938046 335251062893270470047373 := by
  unfold tailWord_2938046
  simp only [CollatzResearch.WordTrace]
  refine ⟨13394917639246074394162249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71439560742645730102198661 13394917639246074394162249)
  ·
    refine ⟨10046188229434555795621687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13394917639246074394162249 10046188229434555795621687)
    ·
      refine ⟨15069282344151833693432531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10046188229434555795621687 15069282344151833693432531)
      ·
        refine ⟨22603923516227750540148797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15069282344151833693432531 22603923516227750540148797)
        ·
          refine ⟨8476471318585406452555799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22603923516227750540148797 8476471318585406452555799)
          ·
            refine ⟨12714706977878109678833699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8476471318585406452555799 12714706977878109678833699)
            ·
              refine ⟨19072060466817164518250549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12714706977878109678833699 19072060466817164518250549)
              ·
                refine ⟨1788005668764109173585989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19072060466817164518250549 1788005668764109173585989)
                ·
                  refine ⟨335251062893270470047373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1788005668764109173585989 335251062893270470047373)
                  ·
                    rfl

theorem cell22_2938046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_2938046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938046 prefixEnd_2938046 := by exact prefixLift 2938046
  have htrace : WordTrace (prefixWord ++ tailWord_2938046) baseStart_2938046 baseEnd_2938046 := by
    simpa [prefixWord, tailWord_2938046, baseEnd_2938046] using wordTrace_append hprefix tailTrace_2938046
  have hstable : (prefixWord ++ tailWord_2938046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938046).length < 2 ^ (prefixWord ++ tailWord_2938046).sum := by decide
  have hdescent : baseEnd_2938046 < baseStart_2938046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938048 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 1, 4]
def baseStart_2938048 : Nat := 118140960795 + 2938048 * 2 ^ 59
def prefixEnd_2938048 : Nat := 4983230072969 + 3 ^ 40 * 2938048 * 2
def baseEnd_2938048 : Nat := 1005753873320684071592113

theorem tailTrace_2938048 : CollatzResearch.WordTrace tailWord_2938048 prefixEnd_2938048 1005753873320684071592113 := by
  unfold tailWord_2938048
  simp only [CollatzResearch.WordTrace]
  refine ⟨53579707029980674747435399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71439609373307566329913865 53579707029980674747435399)
  ·
    refine ⟨80369560544971012121153099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53579707029980674747435399 80369560544971012121153099)
    ·
      refine ⟨120554340817456518181729649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80369560544971012121153099 120554340817456518181729649)
      ·
        refine ⟨90415755613092388636297237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120554340817456518181729649 90415755613092388636297237)
        ·
          refine ⟨4238238544363705717326433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90415755613092388636297237 4238238544363705717326433)
          ·
            refine ⟨3178678908272779287994825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238238544363705717326433 3178678908272779287994825)
            ·
              refine ⟨2384009181204584465996119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178678908272779287994825 2384009181204584465996119)
              ·
                refine ⟨3576013771806876698994179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384009181204584465996119 3576013771806876698994179)
                ·
                  refine ⟨5364020657710315048491269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576013771806876698994179 5364020657710315048491269)
                  ·
                    refine ⟨1005753873320684071592113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5364020657710315048491269 1005753873320684071592113)
                    ·
                      rfl

theorem cell22_2938048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 1, 4].length) (baseStart_2938048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938048 prefixEnd_2938048 := by exact prefixLift 2938048
  have htrace : WordTrace (prefixWord ++ tailWord_2938048) baseStart_2938048 baseEnd_2938048 := by
    simpa [prefixWord, tailWord_2938048, baseEnd_2938048] using wordTrace_append hprefix tailTrace_2938048
  have hstable : (prefixWord ++ tailWord_2938048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938048).length < 2 ^ (prefixWord ++ tailWord_2938048).sum := by decide
  have hdescent : baseEnd_2938048 < baseStart_2938048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938136 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 5]
def baseStart_2938136 : Nat := 118140960795 + 2938136 * 2 ^ 59
def prefixEnd_2938136 : Nat := 4983230072969 + 3 ^ 40 * 2938136 * 2
def baseEnd_2938136 : Nat := 335261332506360391797281

theorem tailTrace_2938136 : CollatzResearch.WordTrace tailWord_2938136 prefixEnd_2938136 335261332506360391797281 := by
  unfold tailWord_2938136
  simp only [CollatzResearch.WordTrace]
  refine ⟨53581311841821270262037131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71441749122428360349382841 53581311841821270262037131)
  ·
    refine ⟨80371967762731905393055697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53581311841821270262037131 80371967762731905393055697)
    ·
      refine ⟨60278975822048929044791773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80371967762731905393055697 60278975822048929044791773)
      ·
        refine ⟨22604615933268348391796915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60278975822048929044791773 22604615933268348391796915)
        ·
          refine ⟨33906923899902522587695373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22604615933268348391796915 33906923899902522587695373)
          ·
            refine ⟨12715096462463445970385765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33906923899902522587695373 12715096462463445970385765)
            ·
              refine ⟨2384080586711896119447331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12715096462463445970385765 2384080586711896119447331)
              ·
                refine ⟨3576120880067844179170997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384080586711896119447331 3576120880067844179170997)
                ·
                  refine ⟨335261332506360391797281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3576120880067844179170997 335261332506360391797281)
                  ·
                    rfl

theorem cell22_2938136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 5].length) (baseStart_2938136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938136 prefixEnd_2938136 := by exact prefixLift 2938136
  have htrace : WordTrace (prefixWord ++ tailWord_2938136) baseStart_2938136 baseEnd_2938136 := by
    simpa [prefixWord, tailWord_2938136, baseEnd_2938136] using wordTrace_append hprefix tailTrace_2938136
  have hstable : (prefixWord ++ tailWord_2938136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938136).length < 2 ^ (prefixWord ++ tailWord_2938136).sum := by decide
  have hdescent : baseEnd_2938136 < baseStart_2938136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938194 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_2938194 : Nat := 118140960795 + 2938194 * 2 ^ 59
def prefixEnd_2938194 : Nat := 4983230072969 + 3 ^ 40 * 2938194 * 2
def baseEnd_2938194 : Nat := 1005803852104388357441665

theorem tailTrace_2938194 : CollatzResearch.WordTrace tailWord_2938194 prefixEnd_2938194 1005803852104388357441665 := by
  unfold tailWord_2938194
  simp only [CollatzResearch.WordTrace]
  refine ⟨26791184779358104107421409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71443159411621610953123757 26791184779358104107421409)
  ·
    refine ⟨20093388584518578080566057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26791184779358104107421409 20093388584518578080566057)
    ·
      refine ⟨15070041438388933560424543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20093388584518578080566057 15070041438388933560424543)
      ·
        refine ⟨22605062157583400340636815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15070041438388933560424543 22605062157583400340636815)
        ·
          refine ⟨33907593236375100510955223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22605062157583400340636815 33907593236375100510955223)
          ·
            refine ⟨50861389854562650766432835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33907593236375100510955223 50861389854562650766432835)
            ·
              refine ⟨76292084781843976149649253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50861389854562650766432835 76292084781843976149649253)
              ·
                refine ⟨14304765896595745528059235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76292084781843976149649253 14304765896595745528059235)
                ·
                  refine ⟨21457148844893618292088853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14304765896595745528059235 21457148844893618292088853)
                  ·
                    refine ⟨1005803852104388357441665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21457148844893618292088853 1005803852104388357441665)
                    ·
                      rfl

theorem cell22_2938194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_2938194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938194 prefixEnd_2938194 := by exact prefixLift 2938194
  have htrace : WordTrace (prefixWord ++ tailWord_2938194) baseStart_2938194 baseEnd_2938194 := by
    simpa [prefixWord, tailWord_2938194, baseEnd_2938194] using wordTrace_append hprefix tailTrace_2938194
  have hstable : (prefixWord ++ tailWord_2938194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938194).length < 2 ^ (prefixWord ++ tailWord_2938194).sum := by decide
  have hdescent : baseEnd_2938194 < baseStart_2938194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938196 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_2938196 : Nat := 118140960795 + 2938196 * 2 ^ 59
def prefixEnd_2938196 : Nat := 4983230072969 + 3 ^ 40 * 2938196 * 2
def baseEnd_2938196 : Nat := 1005804536745261018891659

theorem tailTrace_2938196 : CollatzResearch.WordTrace tailWord_2938196 prefixEnd_2938196 1005804536745261018891659 := by
  unfold tailWord_2938196
  simp only [CollatzResearch.WordTrace]
  refine ⟨53582406031712585385629221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71443208042283447180838961 53582406031712585385629221)
  ·
    refine ⟨10046701130946109759805479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53582406031712585385629221 10046701130946109759805479)
    ·
      refine ⟨15070051696419164639708219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10046701130946109759805479 15070051696419164639708219)
      ·
        refine ⟨22605077544628746959562329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15070051696419164639708219 22605077544628746959562329)
        ·
          refine ⟨16953808158471560219671747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22605077544628746959562329 16953808158471560219671747)
          ·
            refine ⟨25430712237707340329507621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16953808158471560219671747 25430712237707340329507621)
            ·
              refine ⟨4768258544570126311782679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25430712237707340329507621 4768258544570126311782679)
              ·
                refine ⟨7152387816855189467674019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768258544570126311782679 7152387816855189467674019)
                ·
                  refine ⟨10728581725282784201511029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7152387816855189467674019 10728581725282784201511029)
                  ·
                    refine ⟨1005804536745261018891659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10728581725282784201511029 1005804536745261018891659)
                    ·
                      rfl

theorem cell22_2938196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_2938196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938196 prefixEnd_2938196 := by exact prefixLift 2938196
  have htrace : WordTrace (prefixWord ++ tailWord_2938196) baseStart_2938196 baseEnd_2938196 := by
    simpa [prefixWord, tailWord_2938196, baseEnd_2938196] using wordTrace_append hprefix tailTrace_2938196
  have hstable : (prefixWord ++ tailWord_2938196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938196).length < 2 ^ (prefixWord ++ tailWord_2938196).sum := by decide
  have hdescent : baseEnd_2938196 < baseStart_2938196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938211 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 2, 4]
def baseStart_2938211 : Nat := 118140960795 + 2938211 * 2 ^ 59
def prefixEnd_2938211 : Nat := 4983230072969 + 3 ^ 40 * 2938211 * 2
def baseEnd_2938211 : Nat := 1005809671551805979766613

theorem tailTrace_2938211 : CollatzResearch.WordTrace tailWord_2938211 prefixEnd_2938211 1005809671551805979766613 := by
  unfold tailWord_2938211
  simp only [CollatzResearch.WordTrace]
  refine ⟨107165359158370828333054487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71443572772247218888702991 107165359158370828333054487)
  ·
    refine ⟨160748038737556242499581731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107165359158370828333054487 160748038737556242499581731)
    ·
      refine ⟨241122058106334363749372597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160748038737556242499581731 241122058106334363749372597)
      ·
        refine ⟨22605192947468846601503681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241122058106334363749372597 22605192947468846601503681)
        ·
          refine ⟨16953894710601634951127761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22605192947468846601503681 16953894710601634951127761)
          ·
            refine ⟨12715421032951226213345821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16953894710601634951127761 12715421032951226213345821)
            ·
              refine ⟨4768282887356709830004683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12715421032951226213345821 4768282887356709830004683)
              ·
                refine ⟨7152424331035064745007025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768282887356709830004683 7152424331035064745007025)
                ·
                  refine ⟨5364318248276298558755269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7152424331035064745007025 5364318248276298558755269)
                  ·
                    refine ⟨1005809671551805979766613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5364318248276298558755269 1005809671551805979766613)
                    ·
                      rfl

theorem cell22_2938211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 4].length) (baseStart_2938211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938211 prefixEnd_2938211 := by exact prefixLift 2938211
  have htrace : WordTrace (prefixWord ++ tailWord_2938211) baseStart_2938211 baseEnd_2938211 := by
    simpa [prefixWord, tailWord_2938211, baseEnd_2938211] using wordTrace_append hprefix tailTrace_2938211
  have hstable : (prefixWord ++ tailWord_2938211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938211).length < 2 ^ (prefixWord ++ tailWord_2938211).sum := by decide
  have hdescent : baseEnd_2938211 < baseStart_2938211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938301 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_2938301 : Nat := 118140960795 + 2938301 * 2 ^ 59
def prefixEnd_2938301 : Nat := 4983230072969 + 3 ^ 40 * 2938301 * 2
def baseEnd_2938301 : Nat := 1005840480391075745016337

theorem tailTrace_2938301 : CollatzResearch.WordTrace tailWord_2938301 prefixEnd_2938301 1005840480391075745016337 := by
  unfold tailWord_2938301
  simp only [CollatzResearch.WordTrace]
  refine ⟨107168641728044773703830757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71445761152029849135887171 107168641728044773703830757)
  ·
    refine ⟨20094120324008395069468267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107168641728044773703830757 20094120324008395069468267)
    ·
      refine ⟨30141180486012592604202401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20094120324008395069468267 30141180486012592604202401)
      ·
        refine ⟨22605885364509444453151801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30141180486012592604202401 22605885364509444453151801)
        ·
          refine ⟨16954414023382083339863851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22605885364509444453151801 16954414023382083339863851)
          ·
            refine ⟨25431621035073125009795777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16954414023382083339863851 25431621035073125009795777)
            ·
              refine ⟨19073715776304843757346833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25431621035073125009795777 19073715776304843757346833)
              ·
                refine ⟨14305286832228632818010125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19073715776304843757346833 14305286832228632818010125)
                ·
                  refine ⟨5364482562085737306753797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14305286832228632818010125 5364482562085737306753797)
                  ·
                    refine ⟨1005840480391075745016337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5364482562085737306753797 1005840480391075745016337)
                    ·
                      rfl

theorem cell22_2938301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_2938301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938301 prefixEnd_2938301 := by exact prefixLift 2938301
  have htrace : WordTrace (prefixWord ++ tailWord_2938301) baseStart_2938301 baseEnd_2938301 := by
    simpa [prefixWord, tailWord_2938301, baseEnd_2938301] using wordTrace_append hprefix tailTrace_2938301
  have hstable : (prefixWord ++ tailWord_2938301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938301).length < 2 ^ (prefixWord ++ tailWord_2938301).sum := by decide
  have hdescent : baseEnd_2938301 < baseStart_2938301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938318 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_2938318 : Nat := 118140960795 + 2938318 * 2 ^ 59
def prefixEnd_2938318 : Nat := 4983230072969 + 3 ^ 40 * 2938318 * 2
def baseEnd_2938318 : Nat := 1005846299838493367341285

theorem tailTrace_2938318 : CollatzResearch.WordTrace tailWord_2938318 prefixEnd_2938318 1005846299838493367341285 := by
  unfold tailWord_2938318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13396157721122898200899951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71446174512655457071466405 13396157721122898200899951)
  ·
    refine ⟨20094236581684347301349927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13396157721122898200899951 20094236581684347301349927)
    ·
      refine ⟨30141354872526520952024891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20094236581684347301349927 30141354872526520952024891)
      ·
        refine ⟨45212032308789781428037337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30141354872526520952024891 45212032308789781428037337)
        ·
          refine ⟨33909024231592336071028003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45212032308789781428037337 33909024231592336071028003)
          ·
            refine ⟨50863536347388504106542005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33909024231592336071028003 50863536347388504106542005)
            ·
              refine ⟨4768456532567672259988313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50863536347388504106542005 4768456532567672259988313)
              ·
                refine ⟨3576342399425754194991235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4768456532567672259988313 3576342399425754194991235)
                ·
                  refine ⟨5364513599138631292486853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576342399425754194991235 5364513599138631292486853)
                  ·
                    refine ⟨1005846299838493367341285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5364513599138631292486853 1005846299838493367341285)
                    ·
                      rfl

theorem cell22_2938318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_2938318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938318 prefixEnd_2938318 := by exact prefixLift 2938318
  have htrace : WordTrace (prefixWord ++ tailWord_2938318) baseStart_2938318 baseEnd_2938318 := by
    simpa [prefixWord, tailWord_2938318, baseEnd_2938318] using wordTrace_append hprefix tailTrace_2938318
  have hstable : (prefixWord ++ tailWord_2938318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938318).length < 2 ^ (prefixWord ++ tailWord_2938318).sum := by decide
  have hdescent : baseEnd_2938318 < baseStart_2938318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938378 : List Nat := [3, 1, 2, 2, 2, 3, 3, 6]
def baseStart_2938378 : Nat := 118140960795 + 2938378 * 2 ^ 59
def prefixEnd_2938378 : Nat := 4983230072969 + 3 ^ 40 * 2938378 * 2
def baseEnd_2938378 : Nat := 111762982118297023426789

theorem tailTrace_2938378 : CollatzResearch.WordTrace tailWord_2938378 prefixEnd_2938378 111762982118297023426789 := by
  unfold tailWord_2938378
  simp only [CollatzResearch.WordTrace]
  refine ⟨26792862537191453963595947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71447633432510543902922525 26792862537191453963595947)
  ·
    refine ⟨40189293805787180945393921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26792862537191453963595947 40189293805787180945393921)
    ·
      refine ⟨30141970354340385709045441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40189293805787180945393921 30141970354340385709045441)
      ·
        refine ⟨22606477765755289281784081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30141970354340385709045441 22606477765755289281784081)
        ·
          refine ⟨16954858324316466961338061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22606477765755289281784081 16954858324316466961338061)
          ·
            refine ⟨6358071871618675110501773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16954858324316466961338061 6358071871618675110501773)
            ·
              refine ⟨2384276951857003166438165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6358071871618675110501773 2384276951857003166438165)
              ·
                refine ⟨111762982118297023426789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2384276951857003166438165 111762982118297023426789)
                ·
                  rfl

theorem cell22_2938378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_2938378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938378 prefixEnd_2938378 := by exact prefixLift 2938378
  have htrace : WordTrace (prefixWord ++ tailWord_2938378) baseStart_2938378 baseEnd_2938378 := by
    simpa [prefixWord, tailWord_2938378, baseEnd_2938378] using wordTrace_append hprefix tailTrace_2938378
  have hstable : (prefixWord ++ tailWord_2938378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938378).length < 2 ^ (prefixWord ++ tailWord_2938378).sum := by decide
  have hdescent : baseEnd_2938378 < baseStart_2938378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938380 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_2938380 : Nat := 118140960795 + 2938380 * 2 ^ 59
def prefixEnd_2938380 : Nat := 4983230072969 + 3 ^ 40 * 2938380 * 2
def baseEnd_2938380 : Nat := 1005867523705545872291095

theorem tailTrace_2938380 : CollatzResearch.WordTrace tailWord_2938380 prefixEnd_2938380 1005867523705545872291095 := by
  unfold tailWord_2938380
  simp only [CollatzResearch.WordTrace]
  refine ⟨53585761547379285097978297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71447682063172380130637729 53585761547379285097978297)
  ·
    refine ⟨40189321160534463823483723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53585761547379285097978297 40189321160534463823483723)
    ·
      refine ⟨60283981740801695735225585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40189321160534463823483723 60283981740801695735225585)
      ·
        refine ⟨45212986305601271801419189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60283981740801695735225585 45212986305601271801419189)
        ·
          refine ⟨4238717466150119231383049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45212986305601271801419189 4238717466150119231383049)
          ·
            refine ⟨3179038099612589423537287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238717466150119231383049 3179038099612589423537287)
            ·
              refine ⟨4768557149418884135305931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179038099612589423537287 4768557149418884135305931)
              ·
                refine ⟨7152835724128326202958897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768557149418884135305931 7152835724128326202958897)
                ·
                  refine ⟨5364626793096244652219173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7152835724128326202958897 5364626793096244652219173)
                  ·
                    refine ⟨1005867523705545872291095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5364626793096244652219173 1005867523705545872291095)
                    ·
                      rfl

theorem cell22_2938380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_2938380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938380 prefixEnd_2938380 := by exact prefixLift 2938380
  have htrace : WordTrace (prefixWord ++ tailWord_2938380) baseStart_2938380 baseEnd_2938380 := by
    simpa [prefixWord, tailWord_2938380, baseEnd_2938380] using wordTrace_append hprefix tailTrace_2938380
  have hstable : (prefixWord ++ tailWord_2938380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938380).length < 2 ^ (prefixWord ++ tailWord_2938380).sum := by decide
  have hdescent : baseEnd_2938380 < baseStart_2938380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938410 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2938410 : Nat := 118140960795 + 2938410 * 2 ^ 59
def prefixEnd_2938410 : Nat := 4983230072969 + 3 ^ 40 * 2938410 * 2
def baseEnd_2938410 : Nat := 1005877793318635794041003

theorem tailTrace_2938410 : CollatzResearch.WordTrace tailWord_2938410 prefixEnd_2938410 1005877793318635794041003 := by
  unfold tailWord_2938410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26793154321162471329887171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71448411523099923546365789 26793154321162471329887171)
  ·
    refine ⟨40189731481743706994830757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26793154321162471329887171 40189731481743706994830757)
    ·
      refine ⟨7535574652826945061530767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40189731481743706994830757 7535574652826945061530767)
      ·
        refine ⟨11303361979240417592296151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7535574652826945061530767 11303361979240417592296151)
        ·
          refine ⟨16955042968860626388444227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11303361979240417592296151 16955042968860626388444227)
          ·
            refine ⟨25432564453290939582666341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16955042968860626388444227 25432564453290939582666341)
            ·
              refine ⟨4768605834992051171749939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25432564453290939582666341 4768605834992051171749939)
              ·
                refine ⟨7152908752488076757624909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768605834992051171749939 7152908752488076757624909)
                ·
                  refine ⟨2682340782183028784109341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7152908752488076757624909 2682340782183028784109341)
                  ·
                    refine ⟨1005877793318635794041003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2682340782183028784109341 1005877793318635794041003)
                    ·
                      rfl

theorem cell22_2938410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2938410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938410 prefixEnd_2938410 := by exact prefixLift 2938410
  have htrace : WordTrace (prefixWord ++ tailWord_2938410) baseStart_2938410 baseEnd_2938410 := by
    simpa [prefixWord, tailWord_2938410, baseEnd_2938410] using wordTrace_append hprefix tailTrace_2938410
  have hstable : (prefixWord ++ tailWord_2938410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938410).length < 2 ^ (prefixWord ++ tailWord_2938410).sum := by decide
  have hdescent : baseEnd_2938410 < baseStart_2938410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938461 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2938461 : Nat := 118140960795 + 2938461 * 2 ^ 59
def prefixEnd_2938461 : Nat := 4983230072969 + 3 ^ 40 * 2938461 * 2
def baseEnd_2938461 : Nat := 1005895251660888661015847

theorem tailTrace_2938461 : CollatzResearch.WordTrace tailWord_2938461 prefixEnd_2938461 1005895251660888661015847 := by
  unfold tailWord_2938461
  simp only [CollatzResearch.WordTrace]
  refine ⟨107174477407465121029655237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71449651604976747353103491 107174477407465121029655237)
  ·
    refine ⟨20095214513899710193060357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107174477407465121029655237 20095214513899710193060357)
    ·
      refine ⟨3767852721356195661198817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20095214513899710193060357 3767852721356195661198817)
      ·
        refine ⟨2825889541017146745899113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3767852721356195661198817 2825889541017146745899113)
        ·
          refine ⟨2119417155762860059424335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2825889541017146745899113 2119417155762860059424335)
          ·
            refine ⟨3179125733644290089136503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119417155762860059424335 3179125733644290089136503)
            ·
              refine ⟨4768688600466435133704755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179125733644290089136503 4768688600466435133704755)
              ·
                refine ⟨7153032900699652700557133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768688600466435133704755 7153032900699652700557133)
                ·
                  refine ⟨2682387337762369762708925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7153032900699652700557133 2682387337762369762708925)
                  ·
                    refine ⟨1005895251660888661015847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2682387337762369762708925 1005895251660888661015847)
                    ·
                      rfl

theorem cell22_2938461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2938461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938461 prefixEnd_2938461 := by exact prefixLift 2938461
  have htrace : WordTrace (prefixWord ++ tailWord_2938461) baseStart_2938461 baseEnd_2938461 := by
    simpa [prefixWord, tailWord_2938461, baseEnd_2938461] using wordTrace_append hprefix tailTrace_2938461
  have hstable : (prefixWord ++ tailWord_2938461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938461).length < 2 ^ (prefixWord ++ tailWord_2938461).sum := by decide
  have hdescent : baseEnd_2938461 < baseStart_2938461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938468 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 6]
def baseStart_2938468 : Nat := 118140960795 + 2938468 * 2 ^ 59
def prefixEnd_2938468 : Nat := 4983230072969 + 3 ^ 40 * 2938468 * 2
def baseEnd_2938468 : Nat := 335299215967980992030275

theorem tailTrace_2938468 : CollatzResearch.WordTrace tailWord_2938468 prefixEnd_2938468 335299215967980992030275 := by
  unfold tailWord_2938468
  simp only [CollatzResearch.WordTrace]
  refine ⟨53587366359219880612580029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71449821812293174150106705 53587366359219880612580029)
  ·
    refine ⟨20095262384707455229717511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53587366359219880612580029 20095262384707455229717511)
    ·
      refine ⟨30142893577061182844576267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20095262384707455229717511 30142893577061182844576267)
      ·
        refine ⟨45214340365591774266864401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30142893577061182844576267 45214340365591774266864401)
        ·
          refine ⟨33910755274193830700148301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45214340365591774266864401 33910755274193830700148301)
          ·
            refine ⟨12716533227822686512555613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33910755274193830700148301 12716533227822686512555613)
            ·
              refine ⟨4768699960433507442208355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12716533227822686512555613 4768699960433507442208355)
              ·
                refine ⟨7153049940650261163312533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768699960433507442208355 7153049940650261163312533)
                ·
                  refine ⟨335299215967980992030275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7153049940650261163312533 335299215967980992030275)
                  ·
                    rfl

theorem cell22_2938468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_2938468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938468 prefixEnd_2938468 := by exact prefixLift 2938468
  have htrace : WordTrace (prefixWord ++ tailWord_2938468) baseStart_2938468 baseEnd_2938468 := by
    simpa [prefixWord, tailWord_2938468, baseEnd_2938468] using wordTrace_append hprefix tailTrace_2938468
  have hstable : (prefixWord ++ tailWord_2938468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938468).length < 2 ^ (prefixWord ++ tailWord_2938468).sum := by decide
  have hdescent : baseEnd_2938468 < baseStart_2938468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938481 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_2938481 : Nat := 118140960795 + 2938481 * 2 ^ 59
def prefixEnd_2938481 : Nat := 4983230072969 + 3 ^ 40 * 2938481 * 2
def baseEnd_2938481 : Nat := 1005902098069615275515785

theorem tailTrace_2938481 : CollatzResearch.WordTrace tailWord_2938481 prefixEnd_2938481 1005902098069615275515785 := by
  unfold tailWord_2938481
  simp only [CollatzResearch.WordTrace]
  refine ⟨107175206867392664445383297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71450137911595109630255531 107175206867392664445383297)
  ·
    refine ⟨80381405150544498334037473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107175206867392664445383297 80381405150544498334037473)
    ·
      refine ⟨60286053862908373750528105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80381405150544498334037473 60286053862908373750528105)
      ·
        refine ⟨45214540397181280312896079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60286053862908373750528105 45214540397181280312896079)
        ·
          refine ⟨67821810595771920469344119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45214540397181280312896079 67821810595771920469344119)
          ·
            refine ⟨101732715893657880704016179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67821810595771920469344119 101732715893657880704016179)
            ·
              refine ⟨152599073840486821056024269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101732715893657880704016179 152599073840486821056024269)
              ·
                refine ⟨57224652690182557896009101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152599073840486821056024269 57224652690182557896009101)
                ·
                  refine ⟨21459244758818459211003413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57224652690182557896009101 21459244758818459211003413)
                  ·
                    refine ⟨1005902098069615275515785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21459244758818459211003413 1005902098069615275515785)
                    ·
                      rfl

theorem cell22_2938481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_2938481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938481 prefixEnd_2938481 := by exact prefixLift 2938481
  have htrace : WordTrace (prefixWord ++ tailWord_2938481) baseStart_2938481 baseEnd_2938481 := by
    simpa [prefixWord, tailWord_2938481, baseEnd_2938481] using wordTrace_append hprefix tailTrace_2938481
  have hstable : (prefixWord ++ tailWord_2938481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938481).length < 2 ^ (prefixWord ++ tailWord_2938481).sum := by decide
  have hdescent : baseEnd_2938481 < baseStart_2938481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938496 : List Nat := [2, 1, 1, 2, 1, 4, 1, 10]
def baseStart_2938496 : Nat := 118140960795 + 2938496 * 2 ^ 59
def prefixEnd_2938496 : Nat := 4983230072969 + 3 ^ 40 * 2938496 * 2
def baseEnd_2938496 : Nat := 111767470319573359598971

theorem tailTrace_2938496 : CollatzResearch.WordTrace tailWord_2938496 prefixEnd_2938496 111767470319573359598971 := by
  unfold tailWord_2938496
  simp only [CollatzResearch.WordTrace]
  refine ⟨53587876981169161003589671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71450502641558881338119561 53587876981169161003589671)
  ·
    refine ⟨80381815471753741505384507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53587876981169161003589671 80381815471753741505384507)
    ·
      refine ⟨120572723207630612258076761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80381815471753741505384507 120572723207630612258076761)
      ·
        refine ⟨90429542405722959193557571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120572723207630612258076761 90429542405722959193557571)
        ·
          refine ⟨135644313608584438790336357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90429542405722959193557571 135644313608584438790336357)
          ·
            refine ⟨25433308801609582273188067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135644313608584438790336357 25433308801609582273188067)
            ·
              refine ⟨38149963202414373409782101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25433308801609582273188067 38149963202414373409782101)
              ·
                refine ⟨111767470319573359598971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38149963202414373409782101 111767470319573359598971)
                ·
                  rfl

theorem cell22_2938496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 10].length) (baseStart_2938496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938496 prefixEnd_2938496 := by exact prefixLift 2938496
  have htrace : WordTrace (prefixWord ++ tailWord_2938496) baseStart_2938496 baseEnd_2938496 := by
    simpa [prefixWord, tailWord_2938496, baseEnd_2938496] using wordTrace_append hprefix tailTrace_2938496
  have hstable : (prefixWord ++ tailWord_2938496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938496).length < 2 ^ (prefixWord ++ tailWord_2938496).sum := by decide
  have hdescent : baseEnd_2938496 < baseStart_2938496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938500 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_2938500 : Nat := 118140960795 + 2938500 * 2 ^ 59
def prefixEnd_2938500 : Nat := 4983230072969 + 3 ^ 40 * 2938500 * 2
def baseEnd_2938500 : Nat := 1005908602157905559290727

theorem tailTrace_2938500 : CollatzResearch.WordTrace tailWord_2938500 prefixEnd_2938500 1005908602157905559290727 := by
  unfold tailWord_2938500
  simp only [CollatzResearch.WordTrace]
  refine ⟨53587949927161915345162477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71450599902882553793549969 53587949927161915345162477)
  ·
    refine ⟨20095481222685718254435929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53587949927161915345162477 20095481222685718254435929)
    ·
      refine ⟨15071610917014288690826947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20095481222685718254435929 15071610917014288690826947)
      ·
        refine ⟨22607416375521433036240421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15071610917014288690826947 22607416375521433036240421)
        ·
          refine ⟨4238890570410268694295079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22607416375521433036240421 4238890570410268694295079)
          ·
            refine ⟨6358335855615403041442619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4238890570410268694295079 6358335855615403041442619)
            ·
              refine ⟨9537503783423104562163929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6358335855615403041442619 9537503783423104562163929)
              ·
                refine ⟨7153127837567328421622947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9537503783423104562163929 7153127837567328421622947)
                ·
                  refine ⟨10729691756350992632434421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7153127837567328421622947 10729691756350992632434421)
                  ·
                    refine ⟨1005908602157905559290727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10729691756350992632434421 1005908602157905559290727)
                    ·
                      rfl

theorem cell22_2938500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_2938500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938500 prefixEnd_2938500 := by exact prefixLift 2938500
  have htrace : WordTrace (prefixWord ++ tailWord_2938500) baseStart_2938500 baseEnd_2938500 := by
    simpa [prefixWord, tailWord_2938500, baseEnd_2938500] using wordTrace_append hprefix tailTrace_2938500
  have hstable : (prefixWord ++ tailWord_2938500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938500).length < 2 ^ (prefixWord ++ tailWord_2938500).sum := by decide
  have hdescent : baseEnd_2938500 < baseStart_2938500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938504 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 1, 4]
def baseStart_2938504 : Nat := 118140960795 + 2938504 * 2 ^ 59
def prefixEnd_2938504 : Nat := 4983230072969 + 3 ^ 40 * 2938504 * 2
def baseEnd_2938504 : Nat := 1005909971439650882190715

theorem tailTrace_2938504 : CollatzResearch.WordTrace tailWord_2938504 prefixEnd_2938504 1005909971439650882190715 := by
  unfold tailWord_2938504
  simp only [CollatzResearch.WordTrace]
  refine ⟨53588022873154669686735283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71450697164206226248980377 53588022873154669686735283)
  ·
    refine ⟨80382034309732004530102925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53588022873154669686735283 80382034309732004530102925)
    ·
      refine ⟨30143262866149501698788597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80382034309732004530102925 30143262866149501698788597)
      ·
        refine ⟨2825930893701515784261431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30143262866149501698788597 2825930893701515784261431)
        ·
          refine ⟨4238896340552273676392147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825930893701515784261431 4238896340552273676392147)
          ·
            refine ⟨6358344510828410514588221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4238896340552273676392147 6358344510828410514588221)
            ·
              refine ⟨2384379191560653942970583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6358344510828410514588221 2384379191560653942970583)
              ·
                refine ⟨3576568787340980914455875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384379191560653942970583 3576568787340980914455875)
                ·
                  refine ⟨5364853181011471371683813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576568787340980914455875 5364853181011471371683813)
                  ·
                    refine ⟨1005909971439650882190715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5364853181011471371683813 1005909971439650882190715)
                    ·
                      rfl

theorem cell22_2938504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_2938504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938504 prefixEnd_2938504 := by exact prefixLift 2938504
  have htrace : WordTrace (prefixWord ++ tailWord_2938504) baseStart_2938504 baseEnd_2938504 := by
    simpa [prefixWord, tailWord_2938504, baseEnd_2938504] using wordTrace_append hprefix tailTrace_2938504
  have hstable : (prefixWord ++ tailWord_2938504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938504).length < 2 ^ (prefixWord ++ tailWord_2938504).sum := by decide
  have hdescent : baseEnd_2938504 < baseStart_2938504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938549 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2938549 : Nat := 118140960795 + 2938549 * 2 ^ 59
def prefixEnd_2938549 : Nat := 4983230072969 + 3 ^ 40 * 2938549 * 2
def baseEnd_2938549 : Nat := 1005925375859285764815577

theorem tailTrace_2938549 : CollatzResearch.WordTrace tailWord_2938549 prefixEnd_2938549 1005925375859285764815577 := by
  unfold tailWord_2938549
  simp only [CollatzResearch.WordTrace]
  refine ⟨107177687031146312058858701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71451791354097541372572467 107177687031146312058858701)
  ·
    refine ⟨40191632636679867022072013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107177687031146312058858701 40191632636679867022072013)
    ·
      refine ⟨15071862238754950133277005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40191632636679867022072013 15071862238754950133277005)
      ·
        refine ⟨5651948339533106299978877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15071862238754950133277005 5651948339533106299978877)
        ·
          refine ⟨2119480627324914862492079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5651948339533106299978877 2119480627324914862492079)
          ·
            refine ⟨3179220940987372293738119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119480627324914862492079 3179220940987372293738119)
            ·
              refine ⟨4768831411481058440607179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179220940987372293738119 4768831411481058440607179)
              ·
                refine ⟨7153247117221587660910769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768831411481058440607179 7153247117221587660910769)
                ·
                  refine ⟨5364935337916190745683077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7153247117221587660910769 5364935337916190745683077)
                  ·
                    refine ⟨1005925375859285764815577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5364935337916190745683077 1005925375859285764815577)
                    ·
                      rfl

theorem cell22_2938549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2938549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938549 prefixEnd_2938549 := by exact prefixLift 2938549
  have htrace : WordTrace (prefixWord ++ tailWord_2938549) baseStart_2938549 baseEnd_2938549 := by
    simpa [prefixWord, tailWord_2938549, baseEnd_2938549] using wordTrace_append hprefix tailTrace_2938549
  have hstable : (prefixWord ++ tailWord_2938549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938549).length < 2 ^ (prefixWord ++ tailWord_2938549).sum := by decide
  have hdescent : baseEnd_2938549 < baseStart_2938549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938603 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 6]
def baseStart_2938603 : Nat := 118140960795 + 2938603 * 2 ^ 59
def prefixEnd_2938603 : Nat := 4983230072969 + 3 ^ 40 * 2938603 * 2
def baseEnd_2938603 : Nat := 335314620387615874655137

theorem tailTrace_2938603 : CollatzResearch.WordTrace tailWord_2938603 prefixEnd_2938603 335314620387615874655137 := by
  unfold tailWord_2938603
  simp only [CollatzResearch.WordTrace]
  refine ⟨107179656572950679281324463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71453104381967119520882975 107179656572950679281324463)
  ·
    refine ⟨160769484859426018921986695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107179656572950679281324463 160769484859426018921986695)
    ·
      refine ⟨241154227289139028382980043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160769484859426018921986695 241154227289139028382980043)
      ·
        refine ⟨361731340933708542574470065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241154227289139028382980043 361731340933708542574470065)
        ·
          refine ⟨271298505700281406930852549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361731340933708542574470065 271298505700281406930852549)
          ·
            refine ⟨50868469818802763799534853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271298505700281406930852549 50868469818802763799534853)
            ·
              refine ⟨9537838091025518212412785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50868469818802763799534853 9537838091025518212412785)
              ·
                refine ⟨7153378568269138659309589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9537838091025518212412785 7153378568269138659309589)
                ·
                  refine ⟨335314620387615874655137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7153378568269138659309589 335314620387615874655137)
                  ·
                    rfl

theorem cell22_2938603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 6].length) (baseStart_2938603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938603 prefixEnd_2938603 := by exact prefixLift 2938603
  have htrace : WordTrace (prefixWord ++ tailWord_2938603) baseStart_2938603 baseEnd_2938603 := by
    simpa [prefixWord, tailWord_2938603, baseEnd_2938603] using wordTrace_append hprefix tailTrace_2938603
  have hstable : (prefixWord ++ tailWord_2938603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938603).length < 2 ^ (prefixWord ++ tailWord_2938603).sum := by decide
  have hdescent : baseEnd_2938603 < baseStart_2938603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938618 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_2938618 : Nat := 118140960795 + 2938618 * 2 ^ 59
def prefixEnd_2938618 : Nat := 4983230072969 + 3 ^ 40 * 2938618 * 2
def baseEnd_2938618 : Nat := 1005948995969392584840365

theorem tailTrace_2938618 : CollatzResearch.WordTrace tailWord_2938618 prefixEnd_2938618 1005948995969392584840365 := by
  unfold tailWord_2938618
  simp only [CollatzResearch.WordTrace]
  refine ⟨26795050916974084210780127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71453469111930891228747005 26795050916974084210780127)
  ·
    refine ⟨40192576375461126316170191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26795050916974084210780127 40192576375461126316170191)
    ·
      refine ⟨60288864563191689474255287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40192576375461126316170191 60288864563191689474255287)
      ·
        refine ⟨90433296844787534211382931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60288864563191689474255287 90433296844787534211382931)
        ·
          refine ⟨135649945267181301317074397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90433296844787534211382931 135649945267181301317074397)
          ·
            refine ⟨50868729475192987993902899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135649945267181301317074397 50868729475192987993902899)
            ·
              refine ⟨76303094212789481990854349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50868729475192987993902899 76303094212789481990854349)
              ·
                refine ⟨28613660329796055746570381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76303094212789481990854349 28613660329796055746570381)
                ·
                  refine ⟨10730122623673520904963893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28613660329796055746570381 10730122623673520904963893)
                  ·
                    refine ⟨1005948995969392584840365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10730122623673520904963893 1005948995969392584840365)
                    ·
                      rfl

theorem cell22_2938618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_2938618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938618 prefixEnd_2938618 := by exact prefixLift 2938618
  have htrace : WordTrace (prefixWord ++ tailWord_2938618) baseStart_2938618 baseEnd_2938618 := by
    simpa [prefixWord, tailWord_2938618, baseEnd_2938618] using wordTrace_append hprefix tailTrace_2938618
  have hstable : (prefixWord ++ tailWord_2938618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938618).length < 2 ^ (prefixWord ++ tailWord_2938618).sum := by decide
  have hdescent : baseEnd_2938618 < baseStart_2938618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938635 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 4, 3]
def baseStart_2938635 : Nat := 118140960795 + 2938635 * 2 ^ 59
def prefixEnd_2938635 : Nat := 4983230072969 + 3 ^ 40 * 2938635 * 2
def baseEnd_2938635 : Nat := 1005954815416810207165313

theorem tailTrace_2938635 : CollatzResearch.WordTrace tailWord_2938635 prefixEnd_2938635 1005954815416810207165313 := by
  unfold tailWord_2938635
  simp only [CollatzResearch.WordTrace]
  refine ⟨107180823708834748746489359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71453882472556499164326239 107180823708834748746489359)
  ·
    refine ⟨160771235563252123119734039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107180823708834748746489359 160771235563252123119734039)
    ·
      refine ⟨241156853344878184679601059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160771235563252123119734039 241156853344878184679601059)
      ·
        refine ⟨361735280017317277019401589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241156853344878184679601059 361735280017317277019401589)
        ·
          refine ⟨33912682501623494720568899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 361735280017317277019401589 33912682501623494720568899)
          ·
            refine ⟨50869023752435242080853349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33912682501623494720568899 50869023752435242080853349)
            ·
              refine ⟨9537941953581607890160003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50869023752435242080853349 9537941953581607890160003)
              ·
                refine ⟨14306912930372411835240005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9537941953581607890160003 14306912930372411835240005)
                ·
                  refine ⟨2682546174444827219107501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14306912930372411835240005 2682546174444827219107501)
                  ·
                    refine ⟨1005954815416810207165313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2682546174444827219107501 1005954815416810207165313)
                    ·
                      rfl

theorem cell22_2938635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 3].length) (baseStart_2938635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938635 prefixEnd_2938635 := by exact prefixLift 2938635
  have htrace : WordTrace (prefixWord ++ tailWord_2938635) baseStart_2938635 baseEnd_2938635 := by
    simpa [prefixWord, tailWord_2938635, baseEnd_2938635] using wordTrace_append hprefix tailTrace_2938635
  have hstable : (prefixWord ++ tailWord_2938635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938635).length < 2 ^ (prefixWord ++ tailWord_2938635).sum := by decide
  have hdescent : baseEnd_2938635 < baseStart_2938635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938648 : List Nat := [2, 1, 2, 3, 1, 1, 3, 9]
def baseStart_2938648 : Nat := 118140960795 + 2938648 * 2 ^ 59
def prefixEnd_2938648 : Nat := 4983230072969 + 3 ^ 40 * 2938648 * 2
def baseEnd_2938648 : Nat := 111773251731386945176697

theorem tailTrace_2938648 : CollatzResearch.WordTrace tailWord_2938648 prefixEnd_2938648 111773251731386945176697 := by
  unfold tailWord_2938648
  simp only [CollatzResearch.WordTrace]
  refine ⟨53590648928893825983356299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71454198571858434644475065 53590648928893825983356299)
  ·
    refine ⟨80385973393340738975034449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53590648928893825983356299 80385973393340738975034449)
    ·
      refine ⟨60289480045005554231275837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80385973393340738975034449 60289480045005554231275837)
      ·
        refine ⟨22608555016877082836728439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60289480045005554231275837 22608555016877082836728439)
        ·
          refine ⟨33912832525315624255092659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22608555016877082836728439 33912832525315624255092659)
          ·
            refine ⟨50869248787973436382638989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33912832525315624255092659 50869248787973436382638989)
            ·
              refine ⟨19075968295490038643489621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50869248787973436382638989 19075968295490038643489621)
              ·
                refine ⟨111773251731386945176697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19075968295490038643489621 111773251731386945176697)
                ·
                  rfl

theorem cell22_2938648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 9].length) (baseStart_2938648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938648 prefixEnd_2938648 := by exact prefixLift 2938648
  have htrace : WordTrace (prefixWord ++ tailWord_2938648) baseStart_2938648 baseEnd_2938648 := by
    simpa [prefixWord, tailWord_2938648, baseEnd_2938648] using wordTrace_append hprefix tailTrace_2938648
  have hstable : (prefixWord ++ tailWord_2938648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938648).length < 2 ^ (prefixWord ++ tailWord_2938648).sum := by decide
  have hdescent : baseEnd_2938648 < baseStart_2938648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938652 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_2938652 : Nat := 118140960795 + 2938652 * 2 ^ 59
def prefixEnd_2938652 : Nat := 4983230072969 + 3 ^ 40 * 2938652 * 2
def baseEnd_2938652 : Nat := 1005960634864227829490261

theorem tailTrace_2938652 : CollatzResearch.WordTrace tailWord_2938652 prefixEnd_2938652 1005960634864227829490261 := by
  unfold tailWord_2938652
  simp only [CollatzResearch.WordTrace]
  refine ⟨53590721874886580324929105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71454295833182107099905473 53590721874886580324929105)
  ·
    refine ⟨40193041406164935243696829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53590721874886580324929105 40193041406164935243696829)
    ·
      refine ⟨15072390527311850716386311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40193041406164935243696829 15072390527311850716386311)
      ·
        refine ⟨22608585790967776074579467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15072390527311850716386311 22608585790967776074579467)
        ·
          refine ⟨33912878686451664111869201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22608585790967776074579467 33912878686451664111869201)
          ·
            refine ⟨25434659014838748083901901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33912878686451664111869201 25434659014838748083901901)
            ·
              refine ⟨9537997130564530531463213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25434659014838748083901901 9537997130564530531463213)
              ·
                refine ⟨3576748923961698949298705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9537997130564530531463213 3576748923961698949298705)
                ·
                  refine ⟨2682561692971274211974029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3576748923961698949298705 2682561692971274211974029)
                  ·
                    refine ⟨1005960634864227829490261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2682561692971274211974029 1005960634864227829490261)
                    ·
                      rfl

theorem cell22_2938652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_2938652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938652 prefixEnd_2938652 := by exact prefixLift 2938652
  have htrace : WordTrace (prefixWord ++ tailWord_2938652) baseStart_2938652 baseEnd_2938652 := by
    simpa [prefixWord, tailWord_2938652, baseEnd_2938652] using wordTrace_append hprefix tailTrace_2938652
  have hstable : (prefixWord ++ tailWord_2938652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938652).length < 2 ^ (prefixWord ++ tailWord_2938652).sum := by decide
  have hdescent : baseEnd_2938652 < baseStart_2938652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938755 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 6]
def baseStart_2938755 : Nat := 118140960795 + 2938755 * 2 ^ 59
def prefixEnd_2938755 : Nat := 4983230072969 + 3 ^ 40 * 2938755 * 2
def baseEnd_2938755 : Nat := 335331964623056631388315

theorem tailTrace_2938755 : CollatzResearch.WordTrace tailWord_2938755 prefixEnd_2938755 335331964623056631388315 := by
  unfold tailWord_2938755
  simp only [CollatzResearch.WordTrace]
  refine ⟨107185200468400009240857719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71456800312266672827238479 107185200468400009240857719)
  ·
    refine ⟨160777800702600013861286579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107185200468400009240857719 160777800702600013861286579)
    ·
      refine ⟨241166701053900020791929869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160777800702600013861286579 241166701053900020791929869)
      ·
        refine ⟨90437512895212507796973701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241166701053900020791929869 90437512895212507796973701)
        ·
          refine ⟨16957033667852345211932569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90437512895212507796973701 16957033667852345211932569)
          ·
            refine ⟨12717775250889258908949427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16957033667852345211932569 12717775250889258908949427)
            ·
              refine ⟨19076662876333888363424141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12717775250889258908949427 19076662876333888363424141)
              ·
                refine ⟨7153748578625208136284053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19076662876333888363424141 7153748578625208136284053)
                ·
                  refine ⟨335331964623056631388315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7153748578625208136284053 335331964623056631388315)
                  ·
                    rfl

theorem cell22_2938755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 6].length) (baseStart_2938755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938755 prefixEnd_2938755 := by exact prefixLift 2938755
  have htrace : WordTrace (prefixWord ++ tailWord_2938755) baseStart_2938755 baseEnd_2938755 := by
    simpa [prefixWord, tailWord_2938755, baseEnd_2938755] using wordTrace_append hprefix tailTrace_2938755
  have hstable : (prefixWord ++ tailWord_2938755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938755).length < 2 ^ (prefixWord ++ tailWord_2938755).sum := by decide
  have hdescent : baseEnd_2938755 < baseStart_2938755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938772 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2938772 : Nat := 118140960795 + 2938772 * 2 ^ 59
def prefixEnd_2938772 : Nat := 4983230072969 + 3 ^ 40 * 2938772 * 2
def baseEnd_2938772 : Nat := 335333904438862505496631

theorem tailTrace_2938772 : CollatzResearch.WordTrace tailWord_2938772 prefixEnd_2938772 335333904438862505496631 := by
  unfold tailWord_2938772
  simp only [CollatzResearch.WordTrace]
  refine ⟨53592910254669210572113285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71457213672892280762817713 53592910254669210572113285)
  ·
    refine ⟨10048670672750476982271241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53592910254669210572113285 10048670672750476982271241)
    ·
      refine ⟨7536503004562857736703431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10048670672750476982271241 7536503004562857736703431)
      ·
        refine ⟨11304754506844286605055147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7536503004562857736703431 11304754506844286605055147)
        ·
          refine ⟨16957131760266429907582721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11304754506844286605055147 16957131760266429907582721)
          ·
            refine ⟨12717848820199822430687041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16957131760266429907582721 12717848820199822430687041)
            ·
              refine ⟨9538386615149866823015281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12717848820199822430687041 9538386615149866823015281)
              ·
                refine ⟨7153789961362400117261461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9538386615149866823015281 7153789961362400117261461)
                ·
                  refine ⟨335333904438862505496631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7153789961362400117261461 335333904438862505496631)
                  ·
                    rfl

theorem cell22_2938772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2938772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938772 prefixEnd_2938772 := by exact prefixLift 2938772
  have htrace : WordTrace (prefixWord ++ tailWord_2938772) baseStart_2938772 baseEnd_2938772 := by
    simpa [prefixWord, tailWord_2938772, baseEnd_2938772] using wordTrace_append hprefix tailTrace_2938772
  have hstable : (prefixWord ++ tailWord_2938772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938772).length < 2 ^ (prefixWord ++ tailWord_2938772).sum := by decide
  have hdescent : baseEnd_2938772 < baseStart_2938772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938782 : List Nat := [4, 3, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2938782 : Nat := 118140960795 + 2938782 * 2 ^ 59
def prefixEnd_2938782 : Nat := 4983230072969 + 3 ^ 40 * 2938782 * 2
def baseEnd_2938782 : Nat := 1006005136520950823739863

theorem tailTrace_2938782 : CollatzResearch.WordTrace tailWord_2938782 prefixEnd_2938782 1006005136520950823739863 := by
  unfold tailWord_2938782
  simp only [CollatzResearch.WordTrace]
  refine ⟨13398273154912774106511325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71457456826201461901393733 13398273154912774106511325)
  ·
    refine ⟨5024352433092290289941747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13398273154912774106511325 5024352433092290289941747)
    ·
      refine ⟨7536528649638435434912621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5024352433092290289941747 7536528649638435434912621)
      ·
        refine ⟨2826198243614413288092233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7536528649638435434912621 2826198243614413288092233)
        ·
          refine ⟨2119648682710809966069175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2826198243614413288092233 2119648682710809966069175)
          ·
            refine ⟨3179473024066214949103763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119648682710809966069175 3179473024066214949103763)
            ·
              refine ⟨4769209536099322423655645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179473024066214949103763 4769209536099322423655645)
              ·
                refine ⟨1788453576037245908870867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4769209536099322423655645 1788453576037245908870867)
                ·
                  refine ⟨2682680364055868863306301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788453576037245908870867 2682680364055868863306301)
                  ·
                    refine ⟨1006005136520950823739863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2682680364055868863306301 1006005136520950823739863)
                    ·
                      rfl

theorem cell22_2938782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2938782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938782 prefixEnd_2938782 := by exact prefixLift 2938782
  have htrace : WordTrace (prefixWord ++ tailWord_2938782) baseStart_2938782 baseEnd_2938782 := by
    simpa [prefixWord, tailWord_2938782, baseEnd_2938782] using wordTrace_append hprefix tailTrace_2938782
  have hstable : (prefixWord ++ tailWord_2938782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938782).length < 2 ^ (prefixWord ++ tailWord_2938782).sum := by decide
  have hdescent : baseEnd_2938782 < baseStart_2938782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938832 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 3, 3]
def baseStart_2938832 : Nat := 118140960795 + 2938832 * 2 ^ 59
def prefixEnd_2938832 : Nat := 4983230072969 + 3 ^ 40 * 2938832 * 2
def baseEnd_2938832 : Nat := 1006022252542767359989709

theorem tailTrace_2938832 : CollatzResearch.WordTrace tailWord_2938832 prefixEnd_2938832 1006022252542767359989709 := by
  unfold tailWord_2938832
  simp only [CollatzResearch.WordTrace]
  refine ⟨53594004444560525695705375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71458672592747367594273833 53594004444560525695705375)
  ·
    refine ⟨80391006666840788543558063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53594004444560525695705375 80391006666840788543558063)
    ·
      refine ⟨120586510000261182815337095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80391006666840788543558063 120586510000261182815337095)
      ·
        refine ⟨180879765000391774223005643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120586510000261182815337095 180879765000391774223005643)
        ·
          refine ⟨271319647500587661334508465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180879765000391774223005643 271319647500587661334508465)
          ·
            refine ⟨203489735625440746000881349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271319647500587661334508465 203489735625440746000881349)
            ·
              refine ⟨38154325429770139875165253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203489735625440746000881349 38154325429770139875165253)
              ·
                refine ⟨7153936018081901226593485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38154325429770139875165253 7153936018081901226593485)
                ·
                  refine ⟨2682726006780712959972557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7153936018081901226593485 2682726006780712959972557)
                  ·
                    refine ⟨1006022252542767359989709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2682726006780712959972557 1006022252542767359989709)
                    ·
                      rfl

theorem cell22_2938832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_2938832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938832 prefixEnd_2938832 := by exact prefixLift 2938832
  have htrace : WordTrace (prefixWord ++ tailWord_2938832) baseStart_2938832 baseEnd_2938832 := by
    simpa [prefixWord, tailWord_2938832, baseEnd_2938832] using wordTrace_append hprefix tailTrace_2938832
  have hstable : (prefixWord ++ tailWord_2938832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938832).length < 2 ^ (prefixWord ++ tailWord_2938832).sum := by decide
  have hdescent : baseEnd_2938832 < baseStart_2938832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938860 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_2938860 : Nat := 118140960795 + 2938860 * 2 ^ 59
def prefixEnd_2938860 : Nat := 4983230072969 + 3 ^ 40 * 2938860 * 2
def baseEnd_2938860 : Nat := 1006031837514984620289623

theorem tailTrace_2938860 : CollatzResearch.WordTrace tailWord_2938860 prefixEnd_2938860 1006031837514984620289623 := by
  unfold tailWord_2938860
  simp only [CollatzResearch.WordTrace]
  refine ⟨53594515066509806086715017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71459353422013074782286689 53594515066509806086715017)
  ·
    refine ⟨40195886299882354565036263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53594515066509806086715017 40195886299882354565036263)
    ·
      refine ⟨60293829449823531847554395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40195886299882354565036263 60293829449823531847554395)
      ·
        refine ⟨90440744174735297771331593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60293829449823531847554395 90440744174735297771331593)
        ·
          refine ⟨67830558131051473328498695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90440744174735297771331593 67830558131051473328498695)
          ·
            refine ⟨101745837196577209992748043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67830558131051473328498695 101745837196577209992748043)
            ·
              refine ⟨152618755794865814989122065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101745837196577209992748043 152618755794865814989122065)
              ·
                refine ⟨114464066846149361241841549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152618755794865814989122065 114464066846149361241841549)
                ·
                  refine ⟨42924025067306010465690581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114464066846149361241841549 42924025067306010465690581)
                  ·
                    refine ⟨1006031837514984620289623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42924025067306010465690581 1006031837514984620289623)
                    ·
                      rfl

theorem cell22_2938860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_2938860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938860 prefixEnd_2938860 := by exact prefixLift 2938860
  have htrace : WordTrace (prefixWord ++ tailWord_2938860) baseStart_2938860 baseEnd_2938860 := by
    simpa [prefixWord, tailWord_2938860, baseEnd_2938860] using wordTrace_append hprefix tailTrace_2938860
  have hstable : (prefixWord ++ tailWord_2938860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938860).length < 2 ^ (prefixWord ++ tailWord_2938860).sum := by decide
  have hdescent : baseEnd_2938860 < baseStart_2938860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938892 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_2938892 : Nat := 118140960795 + 2938892 * 2 ^ 59
def prefixEnd_2938892 : Nat := 4983230072969 + 3 ^ 40 * 2938892 * 2
def baseEnd_2938892 : Nat := 1006042791768947203489525

theorem tailTrace_2938892 : CollatzResearch.WordTrace tailWord_2938892 prefixEnd_2938892 1006042791768947203489525 := by
  unfold tailWord_2938892
  simp only [CollatzResearch.WordTrace]
  refine ⟨53595098634451840819297465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71460131512602454425729953 53595098634451840819297465)
  ·
    refine ⟨40196323975838880614473099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53595098634451840819297465 40196323975838880614473099)
    ·
      refine ⟨60294485963758320921709649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40196323975838880614473099 60294485963758320921709649)
      ·
        refine ⟨45220864472818740691282237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60294485963758320921709649 45220864472818740691282237)
        ·
          refine ⟨16957824177307027759230839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45220864472818740691282237 16957824177307027759230839)
          ·
            refine ⟨25436736265960541638846259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16957824177307027759230839 25436736265960541638846259)
            ·
              refine ⟨38155104398940812458269389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25436736265960541638846259 38155104398940812458269389)
              ·
                refine ⟨14308164149602804671851021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38155104398940812458269389 14308164149602804671851021)
                ·
                  refine ⟨5365561556101051751944133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14308164149602804671851021 5365561556101051751944133)
                  ·
                    refine ⟨1006042791768947203489525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5365561556101051751944133 1006042791768947203489525)
                    ·
                      rfl

theorem cell22_2938892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_2938892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2938892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2938892 prefixEnd_2938892 := by exact prefixLift 2938892
  have htrace : WordTrace (prefixWord ++ tailWord_2938892) baseStart_2938892 baseEnd_2938892 := by
    simpa [prefixWord, tailWord_2938892, baseEnd_2938892] using wordTrace_append hprefix tailTrace_2938892
  have hstable : (prefixWord ++ tailWord_2938892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938892).length < 2 ^ (prefixWord ++ tailWord_2938892).sum := by decide
  have hdescent : baseEnd_2938892 < baseStart_2938892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939031 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 5]
def baseStart_2939031 : Nat := 118140960795 + 2939031 * 2 ^ 59
def prefixEnd_2939031 : Nat := 4983230072969 + 3 ^ 40 * 2939031 * 2
def baseEnd_2939031 : Nat := 335363458103199058088033

theorem tailTrace_2939031 : CollatzResearch.WordTrace tailWord_2939031 prefixEnd_2939031 335363458103199058088033 := by
  unfold tailWord_2939031
  simp only [CollatzResearch.WordTrace]
  refine ⟨107195267015400108377904947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71463511343600072251936631 107195267015400108377904947)
  ·
    refine ⟨160792900523100162566857421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107195267015400108377904947 160792900523100162566857421)
    ·
      refine ⟨60297337696162560962571533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160792900523100162566857421 60297337696162560962571533)
      ·
        refine ⟨22611501636060960360964325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60297337696162560962571533 22611501636060960360964325)
        ·
          refine ⟨4239656556761430067680811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22611501636060960360964325 4239656556761430067680811)
          ·
            refine ⟨6359484835142145101521217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239656556761430067680811 6359484835142145101521217)
            ·
              refine ⟨4769613626356608826140913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6359484835142145101521217 4769613626356608826140913)
              ·
                refine ⟨3577210219767456619605685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769613626356608826140913 3577210219767456619605685)
                ·
                  refine ⟨335363458103199058088033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3577210219767456619605685 335363458103199058088033)
                  ·
                    rfl

theorem cell22_2939031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 5].length) (baseStart_2939031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939031 prefixEnd_2939031 := by exact prefixLift 2939031
  have htrace : WordTrace (prefixWord ++ tailWord_2939031) baseStart_2939031 baseEnd_2939031 := by
    simpa [prefixWord, tailWord_2939031, baseEnd_2939031] using wordTrace_append hprefix tailTrace_2939031
  have hstable : (prefixWord ++ tailWord_2939031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939031).length < 2 ^ (prefixWord ++ tailWord_2939031).sum := by decide
  have hdescent : baseEnd_2939031 < baseStart_2939031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939087 : List Nat := [1, 1, 2, 1, 1, 3, 13]
def baseStart_2939087 : Nat := 118140960795 + 2939087 * 2 ^ 59
def prefixEnd_2939087 : Nat := 4983230072969 + 3 ^ 40 * 2939087 * 2
def baseEnd_2939087 : Nat := 37263316453853025735701

theorem tailTrace_2939087 : CollatzResearch.WordTrace tailWord_2939087 prefixEnd_2939087 37263316453853025735701 := by
  unfold tailWord_2939087
  simp only [CollatzResearch.WordTrace]
  refine ⟨107197309503197229941943515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71464873002131486627962343 107197309503197229941943515)
  ·
    refine ⟨160795964254795844912915273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107197309503197229941943515 160795964254795844912915273)
    ·
      refine ⟨120596973191096883684686455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160795964254795844912915273 120596973191096883684686455)
      ·
        refine ⟨180895459786645325527029683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120596973191096883684686455 180895459786645325527029683)
        ·
          refine ⟨271343189679967988290544525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180895459786645325527029683 271343189679967988290544525)
          ·
            refine ⟨101753696129987995608954197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271343189679967988290544525 101753696129987995608954197)
            ·
              refine ⟨37263316453853025735701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 101753696129987995608954197 37263316453853025735701)
              ·
                rfl

theorem cell22_2939087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 13].length) (baseStart_2939087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939087 prefixEnd_2939087 := by exact prefixLift 2939087
  have htrace : WordTrace (prefixWord ++ tailWord_2939087) baseStart_2939087 baseEnd_2939087 := by
    simpa [prefixWord, tailWord_2939087, baseEnd_2939087] using wordTrace_append hprefix tailTrace_2939087
  have hstable : (prefixWord ++ tailWord_2939087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939087).length < 2 ^ (prefixWord ++ tailWord_2939087).sum := by decide
  have hdescent : baseEnd_2939087 < baseStart_2939087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939089 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_2939089 : Nat := 118140960795 + 2939089 * 2 ^ 59
def prefixEnd_2939089 : Nat := 4983230072969 + 3 ^ 40 * 2939089 * 2
def baseEnd_2939089 : Nat := 1006110228894904356313921

theorem tailTrace_2939089 : CollatzResearch.WordTrace tailWord_2939089 prefixEnd_2939089 1006110228894904356313921 := by
  unfold tailWord_2939089
  simp only [CollatzResearch.WordTrace]
  refine ⟨107197382449189984283516321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71464921632793322855677547 107197382449189984283516321)
  ·
    refine ⟨80398036836892488212637241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107197382449189984283516321 80398036836892488212637241)
    ·
      refine ⟨60298527627669366159477931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80398036836892488212637241 60298527627669366159477931)
      ·
        refine ⟨90447791441504049239216897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60298527627669366159477931 90447791441504049239216897)
        ·
          refine ⟨67835843581128036929412673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90447791441504049239216897 67835843581128036929412673)
          ·
            refine ⟨50876882685846027697059505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67835843581128036929412673 50876882685846027697059505)
            ·
              refine ⟨38157662014384520772794629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50876882685846027697059505 38157662014384520772794629)
              ·
                refine ⟨7154561627697097644898993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38157662014384520772794629 7154561627697097644898993)
                ·
                  refine ⟨5365921220772823233674245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7154561627697097644898993 5365921220772823233674245)
                  ·
                    refine ⟨1006110228894904356313921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5365921220772823233674245 1006110228894904356313921)
                    ·
                      rfl

theorem cell22_2939089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_2939089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939089 prefixEnd_2939089 := by exact prefixLift 2939089
  have htrace : WordTrace (prefixWord ++ tailWord_2939089) baseStart_2939089 baseEnd_2939089 := by
    simpa [prefixWord, tailWord_2939089, baseEnd_2939089] using wordTrace_append hprefix tailTrace_2939089
  have hstable : (prefixWord ++ tailWord_2939089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939089).length < 2 ^ (prefixWord ++ tailWord_2939089).sum := by decide
  have hdescent : baseEnd_2939089 < baseStart_2939089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939153 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 3, 3]
def baseStart_2939153 : Nat := 118140960795 + 2939153 * 2 ^ 59
def prefixEnd_2939153 : Nat := 4983230072969 + 3 ^ 40 * 2939153 * 2
def baseEnd_2939153 : Nat := 1006132137402829522713725

theorem tailTrace_2939153 : CollatzResearch.WordTrace tailWord_2939153 prefixEnd_2939153 1006132137402829522713725 := by
  unfold tailWord_2939153
  simp only [CollatzResearch.WordTrace]
  refine ⟨107199716720958123213846113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71466477813972082142564075 107199716720958123213846113)
  ·
    refine ⟨80399787540718592410384585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107199716720958123213846113 80399787540718592410384585)
    ·
      refine ⟨60299840655538944307788439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80399787540718592410384585 60299840655538944307788439)
      ·
        refine ⟨90449760983308416461682659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60299840655538944307788439 90449760983308416461682659)
        ·
          refine ⟨135674641474962624692523989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90449760983308416461682659 135674641474962624692523989)
          ·
            refine ⟨3179874409569436516231031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 135674641474962624692523989 3179874409569436516231031)
            ·
              refine ⟨4769811614354154774346547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179874409569436516231031 4769811614354154774346547)
              ·
                refine ⟨7154717421531232161519821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4769811614354154774346547 7154717421531232161519821)
                ·
                  refine ⟨2683019033074212060569933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7154717421531232161519821 2683019033074212060569933)
                  ·
                    refine ⟨1006132137402829522713725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683019033074212060569933 1006132137402829522713725)
                    ·
                      rfl

theorem cell22_2939153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_2939153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939153 prefixEnd_2939153 := by exact prefixLift 2939153
  have htrace : WordTrace (prefixWord ++ tailWord_2939153) baseStart_2939153 baseEnd_2939153 := by
    simpa [prefixWord, tailWord_2939153, baseEnd_2939153] using wordTrace_append hprefix tailTrace_2939153
  have hstable : (prefixWord ++ tailWord_2939153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939153).length < 2 ^ (prefixWord ++ tailWord_2939153).sum := by decide
  have hdescent : baseEnd_2939153 < baseStart_2939153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939164 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_2939164 : Nat := 118140960795 + 2939164 * 2 ^ 59
def prefixEnd_2939164 : Nat := 4983230072969 + 3 ^ 40 * 2939164 * 2
def baseEnd_2939164 : Nat := 1006135902927629160688691

theorem tailTrace_2939164 : CollatzResearch.WordTrace tailWord_2939164 prefixEnd_2939164 1006135902927629160688691 := by
  unfold tailWord_2939164
  simp only [CollatzResearch.WordTrace]
  refine ⟨53600058961959136046248273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71466745282612181394997697 53600058961959136046248273)
  ·
    refine ⟨40200044221469352034686205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53600058961959136046248273 40200044221469352034686205)
    ·
      refine ⟨15075016583051007013007327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40200044221469352034686205 15075016583051007013007327)
      ·
        refine ⟨22612524874576510519510991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15075016583051007013007327 22612524874576510519510991)
        ·
          refine ⟨33918787311864765779266487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22612524874576510519510991 33918787311864765779266487)
          ·
            refine ⟨50878180967797148668899731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33918787311864765779266487 50878180967797148668899731)
            ·
              refine ⟨76317271451695723003349597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50878180967797148668899731 76317271451695723003349597)
              ·
                refine ⟨28618976794385896126256099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76317271451695723003349597 28618976794385896126256099)
                ·
                  refine ⟨42928465191578844189384149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28618976794385896126256099 42928465191578844189384149)
                  ·
                    refine ⟨1006135902927629160688691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42928465191578844189384149 1006135902927629160688691)
                    ·
                      rfl

theorem cell22_2939164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_2939164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939164 prefixEnd_2939164 := by exact prefixLift 2939164
  have htrace : WordTrace (prefixWord ++ tailWord_2939164) baseStart_2939164 baseEnd_2939164 := by
    simpa [prefixWord, tailWord_2939164, baseEnd_2939164] using wordTrace_append hprefix tailTrace_2939164
  have hstable : (prefixWord ++ tailWord_2939164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939164).length < 2 ^ (prefixWord ++ tailWord_2939164).sum := by decide
  have hdescent : baseEnd_2939164 < baseStart_2939164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939209 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_2939209 : Nat := 118140960795 + 2939209 * 2 ^ 59
def prefixEnd_2939209 : Nat := 4983230072969 + 3 ^ 40 * 2939209 * 2
def baseEnd_2939209 : Nat := 1006151307347264043313553

theorem tailTrace_2939209 : CollatzResearch.WordTrace tailWord_2939209 prefixEnd_2939209 1006151307347264043313553 := by
  unfold tailWord_2939209
  simp only [CollatzResearch.WordTrace]
  refine ⟨107201759208755244777884681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71467839472503496518589787 107201759208755244777884681)
  ·
    refine ⟨80401319406566433583413511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107201759208755244777884681 80401319406566433583413511)
    ·
      refine ⟨120601979109849650375120267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80401319406566433583413511 120601979109849650375120267)
      ·
        refine ⟨180902968664774475562680401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120601979109849650375120267 180902968664774475562680401)
        ·
          refine ⟨135677226498580856672010301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180902968664774475562680401 135677226498580856672010301)
          ·
            refine ⟨50878959936967821252003863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135677226498580856672010301 50878959936967821252003863)
            ·
              refine ⟨76318439905451731878005795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50878959936967821252003863 76318439905451731878005795)
              ·
                refine ⟨114477659858177597817008693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76318439905451731878005795 114477659858177597817008693)
                ·
                  refine ⟨10732280611704149795344565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114477659858177597817008693 10732280611704149795344565)
                  ·
                    refine ⟨1006151307347264043313553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10732280611704149795344565 1006151307347264043313553)
                    ·
                      rfl

theorem cell22_2939209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_2939209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939209 prefixEnd_2939209 := by exact prefixLift 2939209
  have htrace : WordTrace (prefixWord ++ tailWord_2939209) baseStart_2939209 baseEnd_2939209 := by
    simpa [prefixWord, tailWord_2939209, baseEnd_2939209] using wordTrace_append hprefix tailTrace_2939209
  have hstable : (prefixWord ++ tailWord_2939209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939209).length < 2 ^ (prefixWord ++ tailWord_2939209).sum := by decide
  have hdescent : baseEnd_2939209 < baseStart_2939209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939226 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_2939226 : Nat := 118140960795 + 2939226 * 2 ^ 59
def prefixEnd_2939226 : Nat := 4983230072969 + 3 ^ 40 * 2939226 * 2
def baseEnd_2939226 : Nat := 1006157126794681665638501

theorem tailTrace_2939226 : CollatzResearch.WordTrace tailWord_2939226 prefixEnd_2939226 1006157126794681665638501 := by
  unfold tailWord_2939226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26800594812423414170313383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71468252833129104454169021 26800594812423414170313383)
  ·
    refine ⟨40200892218635121255470075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26800594812423414170313383 40200892218635121255470075)
    ·
      refine ⟨60301338327952681883205113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40200892218635121255470075 60301338327952681883205113)
      ·
        refine ⟨45226003745964511412403835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60301338327952681883205113 45226003745964511412403835)
        ·
          refine ⟨67839005618946767118605753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45226003745964511412403835 67839005618946767118605753)
          ·
            refine ⟨50879254214210075338954315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67839005618946767118605753 50879254214210075338954315)
            ·
              refine ⟨76318881321315113008431473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50879254214210075338954315 76318881321315113008431473)
              ·
                refine ⟨57239160990986334756323605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76318881321315113008431473 57239160990986334756323605)
                ·
                  refine ⟨2683085671452484441702669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57239160990986334756323605 2683085671452484441702669)
                  ·
                    refine ⟨1006157126794681665638501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683085671452484441702669 1006157126794681665638501)
                    ·
                      rfl

theorem cell22_2939226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_2939226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939226 prefixEnd_2939226 := by exact prefixLift 2939226
  have htrace : WordTrace (prefixWord ++ tailWord_2939226) baseStart_2939226 baseEnd_2939226 := by
    simpa [prefixWord, tailWord_2939226, baseEnd_2939226] using wordTrace_append hprefix tailTrace_2939226
  have hstable : (prefixWord ++ tailWord_2939226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939226).length < 2 ^ (prefixWord ++ tailWord_2939226).sum := by decide
  have hdescent : baseEnd_2939226 < baseStart_2939226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939331 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 3, 4]
def baseStart_2939331 : Nat := 118140960795 + 2939331 * 2 ^ 59
def prefixEnd_2939331 : Nat := 4983230072969 + 3 ^ 40 * 2939331 * 2
def baseEnd_2939331 : Nat := 1006193070440496391763179

theorem tailTrace_2939331 : CollatzResearch.WordTrace tailWord_2939331 prefixEnd_2939331 1006193070440496391763179 := by
  unfold tailWord_2939331
  simp only [CollatzResearch.WordTrace]
  refine ⟨107206208914313259613825847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71470805942875506409217231 107206208914313259613825847)
  ·
    refine ⟨160809313371469889420738771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107206208914313259613825847 160809313371469889420738771)
    ·
      refine ⟨241213970057204834131108157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160809313371469889420738771 241213970057204834131108157)
      ·
        refine ⟨90455238771451812799165559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 241213970057204834131108157 90455238771451812799165559)
        ·
          refine ⟨135682858157177719198748339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90455238771451812799165559 135682858157177719198748339)
          ·
            refine ⟨203524287235766578798122509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135682858157177719198748339 203524287235766578798122509)
            ·
              refine ⟨76321607713412467049295941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203524287235766578798122509 76321607713412467049295941)
              ·
                refine ⟨14310301446264837571742989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76321607713412467049295941 14310301446264837571742989)
                ·
                  refine ⟨5366363042349314089403621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14310301446264837571742989 5366363042349314089403621)
                  ·
                    refine ⟨1006193070440496391763179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5366363042349314089403621 1006193070440496391763179)
                    ·
                      rfl

theorem cell22_2939331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 4].length) (baseStart_2939331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939331 prefixEnd_2939331 := by exact prefixLift 2939331
  have htrace : WordTrace (prefixWord ++ tailWord_2939331) baseStart_2939331 baseEnd_2939331 := by
    simpa [prefixWord, tailWord_2939331, baseEnd_2939331] using wordTrace_append hprefix tailTrace_2939331
  have hstable : (prefixWord ++ tailWord_2939331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939331).length < 2 ^ (prefixWord ++ tailWord_2939331).sum := by decide
  have hdescent : baseEnd_2939331 < baseStart_2939331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939335 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 5]
def baseStart_2939335 : Nat := 118140960795 + 2939335 * 2 ^ 59
def prefixEnd_2939335 : Nat := 4983230072969 + 3 ^ 40 * 2939335 * 2
def baseEnd_2939335 : Nat := 335398146574080571554389

theorem tailTrace_2939335 : CollatzResearch.WordTrace tailWord_2939335 prefixEnd_2939335 335398146574080571554389 := by
  unfold tailWord_2939335
  simp only [CollatzResearch.WordTrace]
  refine ⟨107206354806298768296971459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71470903204199178864647639 107206354806298768296971459)
  ·
    refine ⟨160809532209448152445457189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107206354806298768296971459 160809532209448152445457189)
    ·
      refine ⟨30151787289271528583523223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160809532209448152445457189 30151787289271528583523223)
      ·
        refine ⟨45227680933907292875284835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30151787289271528583523223 45227680933907292875284835)
        ·
          refine ⟨67841521400860939312927253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45227680933907292875284835 67841521400860939312927253)
          ·
            refine ⟨3180071315665356530293465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67841521400860939312927253 3180071315665356530293465)
            ·
              refine ⟨2385053486749017397720099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180071315665356530293465 2385053486749017397720099)
              ·
                refine ⟨3577580230123526096580149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385053486749017397720099 3577580230123526096580149)
                ·
                  refine ⟨335398146574080571554389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3577580230123526096580149 335398146574080571554389)
                  ·
                    rfl

theorem cell22_2939335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 5].length) (baseStart_2939335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939335 prefixEnd_2939335 := by exact prefixLift 2939335
  have htrace : WordTrace (prefixWord ++ tailWord_2939335) baseStart_2939335 baseEnd_2939335 := by
    simpa [prefixWord, tailWord_2939335, baseEnd_2939335] using wordTrace_append hprefix tailTrace_2939335
  have hstable : (prefixWord ++ tailWord_2939335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939335).length < 2 ^ (prefixWord ++ tailWord_2939335).sum := by decide
  have hdescent : baseEnd_2939335 < baseStart_2939335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939423 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 7, 3]
def baseStart_2939423 : Nat := 118140960795 + 2939423 * 2 ^ 59
def prefixEnd_2939423 : Nat := 4983230072969 + 3 ^ 40 * 2939423 * 2
def baseEnd_2939423 : Nat := 1006224563920638818462897

theorem tailTrace_2939423 : CollatzResearch.WordTrace tailWord_2939423 prefixEnd_2939423 1006224563920638818462897 := by
  unfold tailWord_2939423
  simp only [CollatzResearch.WordTrace]
  refine ⟨107209564429979959326174923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71473042953319972884116615 107209564429979959326174923)
  ·
    refine ⟨160814346644969938989262385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107209564429979959326174923 160814346644969938989262385)
    ·
      refine ⟨120610759983727454241946789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160814346644969938989262385 120610759983727454241946789)
      ·
        refine ⟨22614517496948897670365023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120610759983727454241946789 22614517496948897670365023)
        ·
          refine ⟨33921776245423346505547535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22614517496948897670365023 33921776245423346505547535)
          ·
            refine ⟨50882664368135019758321303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33921776245423346505547535 50882664368135019758321303)
            ·
              refine ⟨76323996552202529637481955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50882664368135019758321303 76323996552202529637481955)
              ·
                refine ⟨114485994828303794456222933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76323996552202529637481955 114485994828303794456222933)
                ·
                  refine ⟨2683265503788370182567725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 114485994828303794456222933 2683265503788370182567725)
                  ·
                    refine ⟨1006224563920638818462897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683265503788370182567725 1006224563920638818462897)
                    ·
                      rfl

theorem cell22_2939423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_2939423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939423 prefixEnd_2939423 := by exact prefixLift 2939423
  have htrace : WordTrace (prefixWord ++ tailWord_2939423) baseStart_2939423 baseEnd_2939423 := by
    simpa [prefixWord, tailWord_2939423, baseEnd_2939423] using wordTrace_append hprefix tailTrace_2939423
  have hstable : (prefixWord ++ tailWord_2939423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939423).length < 2 ^ (prefixWord ++ tailWord_2939423).sum := by decide
  have hdescent : baseEnd_2939423 < baseStart_2939423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939451 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 5, 7]
def baseStart_2939451 : Nat := 118140960795 + 2939451 * 2 ^ 59
def prefixEnd_2939451 : Nat := 4983230072969 + 3 ^ 40 * 2939451 * 2
def baseEnd_2939451 : Nat := 1006234148892856078762811

theorem tailTrace_2939451 : CollatzResearch.WordTrace tailWord_2939451 prefixEnd_2939451 1006234148892856078762811 := by
  unfold tailWord_2939451
  simp only [CollatzResearch.WordTrace]
  refine ⟨107210585673878520108194207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71473723782585680072129471 107210585673878520108194207)
  ·
    refine ⟨160815878510817780162291311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107210585673878520108194207 160815878510817780162291311)
    ·
      refine ⟨241223817766226670243436967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160815878510817780162291311 241223817766226670243436967)
      ·
        refine ⟨361835726649340005365155451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241223817766226670243436967 361835726649340005365155451)
        ·
          refine ⟨542753589974010008047733177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361835726649340005365155451 542753589974010008047733177)
          ·
            refine ⟨407065192480507506035799883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542753589974010008047733177 407065192480507506035799883)
            ·
              refine ⟨610597788720761259053699825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407065192480507506035799883 610597788720761259053699825)
              ·
                refine ⟨457948341540570944290274869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610597788720761259053699825 457948341540570944290274869)
                ·
                  refine ⟨42932657019428526027213269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 457948341540570944290274869 42932657019428526027213269)
                  ·
                    refine ⟨1006234148892856078762811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42932657019428526027213269 1006234148892856078762811)
                    ·
                      rfl

theorem cell22_2939451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_2939451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939451 prefixEnd_2939451 := by exact prefixLift 2939451
  have htrace : WordTrace (prefixWord ++ tailWord_2939451) baseStart_2939451 baseEnd_2939451 := by
    simpa [prefixWord, tailWord_2939451, baseEnd_2939451] using wordTrace_append hprefix tailTrace_2939451
  have hstable : (prefixWord ++ tailWord_2939451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939451).length < 2 ^ (prefixWord ++ tailWord_2939451).sum := by decide
  have hdescent : baseEnd_2939451 < baseStart_2939451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939504 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 5]
def baseStart_2939504 : Nat := 118140960795 + 2939504 * 2 ^ 59
def prefixEnd_2939504 : Nat := 4983230072969 + 3 ^ 40 * 2939504 * 2
def baseEnd_2939504 : Nat := 335417430625327202395883

theorem tailTrace_2939504 : CollatzResearch.WordTrace tailWord_2939504 prefixEnd_2939504 335417430625327202395883 := by
  unfold tailWord_2939504
  simp only [CollatzResearch.WordTrace]
  refine ⟨53606259371343255079936783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71475012495124340106582377 53606259371343255079936783)
  ·
    refine ⟨80409389057014882619905175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53606259371343255079936783 80409389057014882619905175)
    ·
      refine ⟨120614083585522323929857763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80409389057014882619905175 120614083585522323929857763)
      ·
        refine ⟨180921125378283485894786645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120614083585522323929857763 180921125378283485894786645)
        ·
          refine ⟨2120169438026759600329531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 180921125378283485894786645 2120169438026759600329531)
          ·
            refine ⟨3180254157040139400494297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120169438026759600329531 3180254157040139400494297)
            ·
              refine ⟨2385190617780104550370723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180254157040139400494297 2385190617780104550370723)
              ·
                refine ⟨3577785926670156825556085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385190617780104550370723 3577785926670156825556085)
                ·
                  refine ⟨335417430625327202395883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3577785926670156825556085 335417430625327202395883)
                  ·
                    rfl

theorem cell22_2939504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 5].length) (baseStart_2939504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939504 prefixEnd_2939504 := by exact prefixLift 2939504
  have htrace : WordTrace (prefixWord ++ tailWord_2939504) baseStart_2939504 baseEnd_2939504 := by
    simpa [prefixWord, tailWord_2939504, baseEnd_2939504] using wordTrace_append hprefix tailTrace_2939504
  have hstable : (prefixWord ++ tailWord_2939504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939504).length < 2 ^ (prefixWord ++ tailWord_2939504).sum := by decide
  have hdescent : baseEnd_2939504 < baseStart_2939504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939620 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_2939620 : Nat := 118140960795 + 2939620 * 2 ^ 59
def prefixEnd_2939620 : Nat := 4983230072969 + 3 ^ 40 * 2939620 * 2
def baseEnd_2939620 : Nat := 1006292001046595971287293

theorem tailTrace_2939620 : CollatzResearch.WordTrace tailWord_2939620 prefixEnd_2939620 1006292001046595971287293 := by
  unfold tailWord_2939620
  simp only [CollatzResearch.WordTrace]
  refine ⟨53608374805133130985548157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71477833073510841314064209 53608374805133130985548157)
  ·
    refine ⟨20103140551924924119580559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53608374805133130985548157 20103140551924924119580559)
    ·
      refine ⟨30154710827887386179370839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20103140551924924119580559 30154710827887386179370839)
      ·
        refine ⟨45232066241831079269056259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30154710827887386179370839 45232066241831079269056259)
        ·
          refine ⟨67848099362746618903584389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45232066241831079269056259 67848099362746618903584389)
          ·
            refine ⟨12721518630514991044422073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67848099362746618903584389 12721518630514991044422073)
            ·
              refine ⟨9541138972886243283316555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12721518630514991044422073 9541138972886243283316555)
              ·
                refine ⟨14311708459329364924974833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9541138972886243283316555 14311708459329364924974833)
                ·
                  refine ⟨10733781344497023693731125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14311708459329364924974833 10733781344497023693731125)
                  ·
                    refine ⟨1006292001046595971287293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10733781344497023693731125 1006292001046595971287293)
                    ·
                      rfl

theorem cell22_2939620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_2939620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939620 prefixEnd_2939620 := by exact prefixLift 2939620
  have htrace : WordTrace (prefixWord ++ tailWord_2939620) baseStart_2939620 baseEnd_2939620 := by
    simpa [prefixWord, tailWord_2939620, baseEnd_2939620] using wordTrace_append hprefix tailTrace_2939620
  have hstable : (prefixWord ++ tailWord_2939620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939620).length < 2 ^ (prefixWord ++ tailWord_2939620).sum := by decide
  have hdescent : baseEnd_2939620 < baseStart_2939620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939652 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_2939652 : Nat := 118140960795 + 2939652 * 2 ^ 59
def prefixEnd_2939652 : Nat := 4983230072969 + 3 ^ 40 * 2939652 * 2
def baseEnd_2939652 : Nat := 1006302955300558554487195

theorem tailTrace_2939652 : CollatzResearch.WordTrace tailWord_2939652 prefixEnd_2939652 1006302955300558554487195 := by
  unfold tailWord_2939652
  simp only [CollatzResearch.WordTrace]
  refine ⟨53608958373075165718130605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71478611164100220957507473 53608958373075165718130605)
  ·
    refine ⟨20103359389903187144298977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53608958373075165718130605 20103359389903187144298977)
    ·
      refine ⟨15077519542427390358224233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20103359389903187144298977 15077519542427390358224233)
      ·
        refine ⟨11308139656820542768668175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15077519542427390358224233 11308139656820542768668175)
        ·
          refine ⟨16962209485230814153002263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11308139656820542768668175 16962209485230814153002263)
          ·
            refine ⟨25443314227846221229503395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16962209485230814153002263 25443314227846221229503395)
            ·
              refine ⟨38164971341769331844255093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25443314227846221229503395 38164971341769331844255093)
              ·
                refine ⟨3577966063290874860398915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38164971341769331844255093 3577966063290874860398915)
                ·
                  refine ⟨5366949094936312290598373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3577966063290874860398915 5366949094936312290598373)
                  ·
                    refine ⟨1006302955300558554487195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5366949094936312290598373 1006302955300558554487195)
                    ·
                      rfl

theorem cell22_2939652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_2939652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939652 prefixEnd_2939652 := by exact prefixLift 2939652
  have htrace : WordTrace (prefixWord ++ tailWord_2939652) baseStart_2939652 baseEnd_2939652 := by
    simpa [prefixWord, tailWord_2939652, baseEnd_2939652] using wordTrace_append hprefix tailTrace_2939652
  have hstable : (prefixWord ++ tailWord_2939652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939652).length < 2 ^ (prefixWord ++ tailWord_2939652).sum := by decide
  have hdescent : baseEnd_2939652 < baseStart_2939652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939697 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_2939697 : Nat := 118140960795 + 2939697 * 2 ^ 59
def prefixEnd_2939697 : Nat := 4983230072969 + 3 ^ 40 * 2939697 * 2
def baseEnd_2939697 : Nat := 1006318359720193437112057

theorem tailTrace_2939697 : CollatzResearch.WordTrace tailWord_2939697 prefixEnd_2939697 1006318359720193437112057 := by
  unfold tailWord_2939697
  simp only [CollatzResearch.WordTrace]
  refine ⟨107219558030987304121649345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71479705353991536081099563 107219558030987304121649345)
  ·
    refine ⟨80414668523240478091237009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107219558030987304121649345 80414668523240478091237009)
    ·
      refine ⟨60311001392430358568427757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80414668523240478091237009 60311001392430358568427757)
      ·
        refine ⟨22616625522161384463160409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60311001392430358568427757 22616625522161384463160409)
        ·
          refine ⟨16962469141621038347370307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22616625522161384463160409 16962469141621038347370307)
          ·
            refine ⟨25443703712431557521055461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16962469141621038347370307 25443703712431557521055461)
            ·
              refine ⟨4770694446080917035197899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25443703712431557521055461 4770694446080917035197899)
              ·
                refine ⟨7156041669121375552796849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4770694446080917035197899 7156041669121375552796849)
                ·
                  refine ⟨5367031251841031664597637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7156041669121375552796849 5367031251841031664597637)
                  ·
                    refine ⟨1006318359720193437112057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5367031251841031664597637 1006318359720193437112057)
                    ·
                      rfl

theorem cell22_2939697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_2939697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939697 prefixEnd_2939697 := by exact prefixLift 2939697
  have htrace : WordTrace (prefixWord ++ tailWord_2939697) baseStart_2939697 baseEnd_2939697 := by
    simpa [prefixWord, tailWord_2939697, baseEnd_2939697] using wordTrace_append hprefix tailTrace_2939697
  have hstable : (prefixWord ++ tailWord_2939697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939697).length < 2 ^ (prefixWord ++ tailWord_2939697).sum := by decide
  have hdescent : baseEnd_2939697 < baseStart_2939697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939718 : List Nat := [6, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2939718 : Nat := 118140960795 + 2939718 * 2 ^ 59
def prefixEnd_2939718 : Nat := 4983230072969 + 3 ^ 40 * 2939718 * 2
def baseEnd_2939718 : Nat := 335441849483118794112331

theorem tailTrace_2939718 : CollatzResearch.WordTrace tailWord_2939718 prefixEnd_2939718 335441849483118794112331 := by
  unfold tailWord_2939718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3350635123872225772130119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71480215975940816472109205 3350635123872225772130119)
  ·
    refine ⟨5025952685808338658195179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3350635123872225772130119 5025952685808338658195179)
    ·
      refine ⟨7538929028712507987292769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5025952685808338658195179 7538929028712507987292769)
      ·
        refine ⟨5654196771534380990469577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7538929028712507987292769 5654196771534380990469577)
        ·
          refine ⟨4240647578650785742852183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5654196771534380990469577 4240647578650785742852183)
          ·
            refine ⟨6360971367976178614278275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240647578650785742852183 6360971367976178614278275)
            ·
              refine ⟨9541457051964267921417413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6360971367976178614278275 9541457051964267921417413)
              ·
                refine ⟨1789023197243300235265765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9541457051964267921417413 1789023197243300235265765)
                ·
                  refine ⟨335441849483118794112331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789023197243300235265765 335441849483118794112331)
                  ·
                    rfl

theorem cell22_2939718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2939718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939718 prefixEnd_2939718 := by exact prefixLift 2939718
  have htrace : WordTrace (prefixWord ++ tailWord_2939718) baseStart_2939718 baseEnd_2939718 := by
    simpa [prefixWord, tailWord_2939718, baseEnd_2939718] using wordTrace_append hprefix tailTrace_2939718
  have hstable : (prefixWord ++ tailWord_2939718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939718).length < 2 ^ (prefixWord ++ tailWord_2939718).sum := by decide
  have hdescent : baseEnd_2939718 < baseStart_2939718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939729 : List Nat := [1, 2, 2, 1, 7, 1, 1, 7]
def baseStart_2939729 : Nat := 118140960795 + 2939729 * 2 ^ 59
def prefixEnd_2939729 : Nat := 4983230072969 + 3 ^ 40 * 2939729 * 2
def baseEnd_2939729 : Nat := 111814368219350668923551

theorem tailTrace_2939729 : CollatzResearch.WordTrace tailWord_2939729 prefixEnd_2939729 111814368219350668923551 := by
  unfold tailWord_2939729
  simp only [CollatzResearch.WordTrace]
  refine ⟨107220725166871373586814241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71480483444580915724542827 107220725166871373586814241)
  ·
    refine ⟨80415543875153530190110681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107220725166871373586814241 80415543875153530190110681)
    ·
      refine ⟨60311657906365147642583011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80415543875153530190110681 60311657906365147642583011)
      ·
        refine ⟨90467486859547721463874517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60311657906365147642583011 90467486859547721463874517)
        ·
          refine ⟨2120331723270649721809559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 90467486859547721463874517 2120331723270649721809559)
          ·
            refine ⟨3180497584905974582714339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120331723270649721809559 3180497584905974582714339)
            ·
              refine ⟨4770746377358961874071509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180497584905974582714339 4770746377358961874071509)
              ·
                refine ⟨111814368219350668923551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4770746377358961874071509 111814368219350668923551)
                ·
                  rfl

theorem cell22_2939729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 7].length) (baseStart_2939729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939729 prefixEnd_2939729 := by exact prefixLift 2939729
  have htrace : WordTrace (prefixWord ++ tailWord_2939729) baseStart_2939729 baseEnd_2939729 := by
    simpa [prefixWord, tailWord_2939729, baseEnd_2939729] using wordTrace_append hprefix tailTrace_2939729
  have hstable : (prefixWord ++ tailWord_2939729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939729).length < 2 ^ (prefixWord ++ tailWord_2939729).sum := by decide
  have hdescent : baseEnd_2939729 < baseStart_2939729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939761 : List Nat := [1, 2, 2, 2, 1, 5, 2, 3, 1, 3]
def baseStart_2939761 : Nat := 118140960795 + 2939761 * 2 ^ 59
def prefixEnd_2939761 : Nat := 4983230072969 + 3 ^ 40 * 2939761 * 2
def baseEnd_2939761 : Nat := 1006340268228118603511861

theorem tailTrace_2939761 : CollatzResearch.WordTrace tailWord_2939761 prefixEnd_2939761 1006340268228118603511861 := by
  unfold tailWord_2939761
  simp only [CollatzResearch.WordTrace]
  refine ⟨107221892302755443051979137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71481261535170295367986091 107221892302755443051979137)
  ·
    refine ⟨80416419227066582288984353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107221892302755443051979137 80416419227066582288984353)
    ·
      refine ⟨60312314420299936716738265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80416419227066582288984353 60312314420299936716738265)
      ·
        refine ⟨45234235815224952537553699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60312314420299936716738265 45234235815224952537553699)
        ·
          refine ⟨67851353722837428806330549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45234235815224952537553699 67851353722837428806330549)
          ·
            refine ⟨6361064411516008950593489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67851353722837428806330549 6361064411516008950593489)
            ·
              refine ⟨4770798308637006712945117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6361064411516008950593489 4770798308637006712945117)
              ·
                refine ⟨1789049365738877517354419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4770798308637006712945117 1789049365738877517354419)
                ·
                  refine ⟨2683574048608316276031629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789049365738877517354419 2683574048608316276031629)
                  ·
                    refine ⟨1006340268228118603511861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683574048608316276031629 1006340268228118603511861)
                    ·
                      rfl

theorem cell22_2939761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_2939761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939761 prefixEnd_2939761 := by exact prefixLift 2939761
  have htrace : WordTrace (prefixWord ++ tailWord_2939761) baseStart_2939761 baseEnd_2939761 := by
    simpa [prefixWord, tailWord_2939761, baseEnd_2939761] using wordTrace_append hprefix tailTrace_2939761
  have hstable : (prefixWord ++ tailWord_2939761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939761).length < 2 ^ (prefixWord ++ tailWord_2939761).sum := by decide
  have hdescent : baseEnd_2939761 < baseStart_2939761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939817 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 6, 3]
def baseStart_2939817 : Nat := 118140960795 + 2939817 * 2 ^ 59
def prefixEnd_2939817 : Nat := 4983230072969 + 3 ^ 40 * 2939817 * 2
def baseEnd_2939817 : Nat := 1006359438172553124111689

theorem tailTrace_2939817 : CollatzResearch.WordTrace tailWord_2939817 prefixEnd_2939817 1006359438172553124111689 := by
  unfold tailWord_2939817
  simp only [CollatzResearch.WordTrace]
  refine ⟨107223934790552564616017705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71482623193701709744011803 107223934790552564616017705)
  ·
    refine ⟨80417951092914423462013279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107223934790552564616017705 80417951092914423462013279)
    ·
      refine ⟨120626926639371635193019919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80417951092914423462013279 120626926639371635193019919)
      ·
        refine ⟨180940389959057452789529879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120626926639371635193019919 180940389959057452789529879)
        ·
          refine ⟨271410584938586179184294819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180940389959057452789529879 271410584938586179184294819)
          ·
            refine ⟨407115877407879268776442229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271410584938586179184294819 407115877407879268776442229)
            ·
              refine ⟨38167113506988681447791459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 407115877407879268776442229 38167113506988681447791459)
              ·
                refine ⟨57250670260483022171687189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38167113506988681447791459 57250670260483022171687189)
                ·
                  refine ⟨2683625168460141664297837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57250670260483022171687189 2683625168460141664297837)
                  ·
                    refine ⟨1006359438172553124111689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683625168460141664297837 1006359438172553124111689)
                    ·
                      rfl

theorem cell22_2939817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_2939817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939817 prefixEnd_2939817 := by exact prefixLift 2939817
  have htrace : WordTrace (prefixWord ++ tailWord_2939817) baseStart_2939817 baseEnd_2939817 := by
    simpa [prefixWord, tailWord_2939817, baseEnd_2939817] using wordTrace_append hprefix tailTrace_2939817
  have hstable : (prefixWord ++ tailWord_2939817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939817).length < 2 ^ (prefixWord ++ tailWord_2939817).sum := by decide
  have hdescent : baseEnd_2939817 < baseStart_2939817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939832 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_2939832 : Nat := 118140960795 + 2939832 * 2 ^ 59
def prefixEnd_2939832 : Nat := 4983230072969 + 3 ^ 40 * 2939832 * 2
def baseEnd_2939832 : Nat := 1006364572979098084986643

theorem tailTrace_2939832 : CollatzResearch.WordTrace tailWord_2939832 prefixEnd_2939832 1006364572979098084986643 := by
  unfold tailWord_2939832
  simp only [CollatzResearch.WordTrace]
  refine ⟨53612240942749111088906875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71482987923665481451875833 53612240942749111088906875)
  ·
    refine ⟨80418361414123666633360313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53612240942749111088906875 80418361414123666633360313)
    ·
      refine ⟨60313771060592749975020235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80418361414123666633360313 60313771060592749975020235)
      ·
        refine ⟨90470656590889124962530353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60313771060592749975020235 90470656590889124962530353)
        ·
          refine ⟨67852992443166843721897765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90470656590889124962530353 67852992443166843721897765)
          ·
            refine ⟨12722436083093783197855831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67852992443166843721897765 12722436083093783197855831)
            ·
              refine ⟨19083654124640674796783747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12722436083093783197855831 19083654124640674796783747)
              ·
                refine ⟨28625481186961012195175621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19083654124640674796783747 28625481186961012195175621)
                ·
                  refine ⟨5367277722555189786595429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28625481186961012195175621 5367277722555189786595429)
                  ·
                    refine ⟨1006364572979098084986643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5367277722555189786595429 1006364572979098084986643)
                    ·
                      rfl

theorem cell22_2939832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_2939832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939832 prefixEnd_2939832 := by exact prefixLift 2939832
  have htrace : WordTrace (prefixWord ++ tailWord_2939832) baseStart_2939832 baseEnd_2939832 := by
    simpa [prefixWord, tailWord_2939832, baseEnd_2939832] using wordTrace_append hprefix tailTrace_2939832
  have hstable : (prefixWord ++ tailWord_2939832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939832).length < 2 ^ (prefixWord ++ tailWord_2939832).sum := by decide
  have hdescent : baseEnd_2939832 < baseStart_2939832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939834 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_2939834 : Nat := 118140960795 + 2939834 * 2 ^ 59
def prefixEnd_2939834 : Nat := 4983230072969 + 3 ^ 40 * 2939834 * 2
def baseEnd_2939834 : Nat := 1006365257619970746436637

theorem tailTrace_2939834 : CollatzResearch.WordTrace tailWord_2939834 prefixEnd_2939834 1006365257619970746436637 := by
  unfold tailWord_2939834
  simp only [CollatzResearch.WordTrace]
  refine ⟨26806138707872744129846639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71483036554327317679591037 26806138707872744129846639)
  ·
    refine ⟨40209208061809116194769959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26806138707872744129846639 40209208061809116194769959)
    ·
      refine ⟨60313812092713674292154939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40209208061809116194769959 60313812092713674292154939)
      ·
        refine ⟨90470718139070511438232409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60313812092713674292154939 90470718139070511438232409)
        ·
          refine ⟨67853038604302883578674307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90470718139070511438232409 67853038604302883578674307)
          ·
            refine ⟨101779557906454325368011461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67853038604302883578674307 101779557906454325368011461)
            ·
              refine ⟨19083667107460186006502149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101779557906454325368011461 19083667107460186006502149)
              ·
                refine ⟨3578187582648784876219153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19083667107460186006502149 3578187582648784876219153)
                ·
                  refine ⟨2683640686986588657164365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3578187582648784876219153 2683640686986588657164365)
                  ·
                    refine ⟨1006365257619970746436637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683640686986588657164365 1006365257619970746436637)
                    ·
                      rfl

theorem cell22_2939834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_2939834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939834 prefixEnd_2939834 := by exact prefixLift 2939834
  have htrace : WordTrace (prefixWord ++ tailWord_2939834) baseStart_2939834 baseEnd_2939834 := by
    simpa [prefixWord, tailWord_2939834, baseEnd_2939834] using wordTrace_append hprefix tailTrace_2939834
  have hstable : (prefixWord ++ tailWord_2939834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939834).length < 2 ^ (prefixWord ++ tailWord_2939834).sum := by decide
  have hdescent : baseEnd_2939834 < baseStart_2939834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939851 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 2, 3]
def baseStart_2939851 : Nat := 118140960795 + 2939851 * 2 ^ 59
def prefixEnd_2939851 : Nat := 4983230072969 + 3 ^ 40 * 2939851 * 2
def baseEnd_2939851 : Nat := 1006371077067388368761585

theorem tailTrace_2939851 : CollatzResearch.WordTrace tailWord_2939851 prefixEnd_2939851 1006371077067388368761585 := by
  unfold tailWord_2939851
  simp only [CollatzResearch.WordTrace]
  refine ⟨107225174872429388422755407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71483449914952925615170271 107225174872429388422755407)
  ·
    refine ⟨160837762308644082634133111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107225174872429388422755407 160837762308644082634133111)
    ·
      refine ⟨241256643462966123951199667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160837762308644082634133111 241256643462966123951199667)
      ·
        refine ⟨361884965194449185926799501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241256643462966123951199667 361884965194449185926799501)
        ·
          refine ⟨135706861947918444722549813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361884965194449185926799501 135706861947918444722549813)
          ·
            refine ⟨12722518307617354192739045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135706861947918444722549813 12722518307617354192739045)
            ·
              refine ⟨2385472182678253911138571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12722518307617354192739045 2385472182678253911138571)
              ·
                refine ⟨3578208274017380866707857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385472182678253911138571 3578208274017380866707857)
                ·
                  refine ⟨2683656205513035650030893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3578208274017380866707857 2683656205513035650030893)
                  ·
                    refine ⟨1006371077067388368761585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683656205513035650030893 1006371077067388368761585)
                    ·
                      rfl

theorem cell22_2939851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 2, 3].length) (baseStart_2939851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939851 prefixEnd_2939851 := by exact prefixLift 2939851
  have htrace : WordTrace (prefixWord ++ tailWord_2939851) baseStart_2939851 baseEnd_2939851 := by
    simpa [prefixWord, tailWord_2939851, baseEnd_2939851] using wordTrace_append hprefix tailTrace_2939851
  have hstable : (prefixWord ++ tailWord_2939851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939851).length < 2 ^ (prefixWord ++ tailWord_2939851).sum := by decide
  have hdescent : baseEnd_2939851 < baseStart_2939851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939894 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2939894 : Nat := 118140960795 + 2939894 * 2 ^ 59
def prefixEnd_2939894 : Nat := 4983230072969 + 3 ^ 40 * 2939894 * 2
def baseEnd_2939894 : Nat := 1006385796846150589936453

theorem tailTrace_2939894 : CollatzResearch.WordTrace tailWord_2939894 prefixEnd_2939894 1006385796846150589936453 := by
  unfold tailWord_2939894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6701671450704600422910671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71484495474182404511047157 6701671450704600422910671)
  ·
    refine ⟨10052507176056900634366007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6701671450704600422910671 10052507176056900634366007)
    ·
      refine ⟨15078760764085350951549011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10052507176056900634366007 15078760764085350951549011)
      ·
        refine ⟨22618141146128026427323517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15078760764085350951549011 22618141146128026427323517)
        ·
          refine ⟨8481802929798009910246319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22618141146128026427323517 8481802929798009910246319)
          ·
            refine ⟨12722704394697014865369479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8481802929798009910246319 12722704394697014865369479)
            ·
              refine ⟨19084056592045522298054219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12722704394697014865369479 19084056592045522298054219)
              ·
                refine ⟨28626084888068283447081329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19084056592045522298054219 28626084888068283447081329)
                ·
                  refine ⟨21469563666051212585310997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28626084888068283447081329 21469563666051212585310997)
                  ·
                    refine ⟨1006385796846150589936453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21469563666051212585310997 1006385796846150589936453)
                    ·
                      rfl

theorem cell22_2939894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2939894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939894 prefixEnd_2939894 := by exact prefixLift 2939894
  have htrace : WordTrace (prefixWord ++ tailWord_2939894) baseStart_2939894 baseEnd_2939894 := by
    simpa [prefixWord, tailWord_2939894, baseEnd_2939894] using wordTrace_append hprefix tailTrace_2939894
  have hstable : (prefixWord ++ tailWord_2939894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939894).length < 2 ^ (prefixWord ++ tailWord_2939894).sum := by decide
  have hdescent : baseEnd_2939894 < baseStart_2939894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939943 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 5]
def baseStart_2939943 : Nat := 118140960795 + 2939943 * 2 ^ 59
def prefixEnd_2939943 : Nat := 4983230072969 + 3 ^ 40 * 2939943 * 2
def baseEnd_2939943 : Nat := 335467523515843598487101

theorem tailTrace_2939943 : CollatzResearch.WordTrace tailWord_2939943 prefixEnd_2939943 335467523515843598487101 := by
  unfold tailWord_2939943
  simp only [CollatzResearch.WordTrace]
  refine ⟨107228530388096088135104483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71485686925397392090069655 107228530388096088135104483)
  ·
    refine ⟨160842795582144132202656725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107228530388096088135104483 160842795582144132202656725)
    ·
      refine ⟨3769753021456503098499767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 160842795582144132202656725 3769753021456503098499767)
      ·
        refine ⟨5654629532184754647749651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3769753021456503098499767 5654629532184754647749651)
        ·
          refine ⟨8481944298277131971624477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5654629532184754647749651 8481944298277131971624477)
          ·
            refine ⟨3180729111853924489359179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8481944298277131971624477 3180729111853924489359179)
            ·
              refine ⟨4771093667780886734038769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180729111853924489359179 4771093667780886734038769)
              ·
                refine ⟨3578320250835665050529077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4771093667780886734038769 3578320250835665050529077)
                ·
                  refine ⟨335467523515843598487101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3578320250835665050529077 335467523515843598487101)
                  ·
                    rfl

theorem cell22_2939943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 5].length) (baseStart_2939943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939943 prefixEnd_2939943 := by exact prefixLift 2939943
  have htrace : WordTrace (prefixWord ++ tailWord_2939943) baseStart_2939943 baseEnd_2939943 := by
    simpa [prefixWord, tailWord_2939943, baseEnd_2939943] using wordTrace_append hprefix tailTrace_2939943
  have hstable : (prefixWord ++ tailWord_2939943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939943).length < 2 ^ (prefixWord ++ tailWord_2939943).sum := by decide
  have hdescent : baseEnd_2939943 < baseStart_2939943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939954 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_2939954 : Nat := 118140960795 + 2939954 * 2 ^ 59
def prefixEnd_2939954 : Nat := 4983230072969 + 3 ^ 40 * 2939954 * 2
def baseEnd_2939954 : Nat := 335468778690776811145423

theorem tailTrace_2939954 : CollatzResearch.WordTrace tailWord_2939954 prefixEnd_2939954 335468778690776811145423 := by
  unfold tailWord_2939954
  simp only [CollatzResearch.WordTrace]
  refine ⟨26807232897764059253438729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71485954394037491342503277 26807232897764059253438729)
  ·
    refine ⟨20105424673323044440079047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26807232897764059253438729 20105424673323044440079047)
    ·
      refine ⟨30158137009984566660118571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20105424673323044440079047 30158137009984566660118571)
      ·
        refine ⟨45237205514976849990177857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30158137009984566660118571 45237205514976849990177857)
        ·
          refine ⟨33927904136232637492633393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45237205514976849990177857 33927904136232637492633393)
          ·
            refine ⟨25445928102174478119475045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33927904136232637492633393 25445928102174478119475045)
            ·
              refine ⟨4771111519157714647401571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25445928102174478119475045 4771111519157714647401571)
              ·
                refine ⟨7156667278736571971102357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4771111519157714647401571 7156667278736571971102357)
                ·
                  refine ⟨335468778690776811145423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7156667278736571971102357 335468778690776811145423)
                  ·
                    rfl

theorem cell22_2939954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_2939954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939954 prefixEnd_2939954 := by exact prefixLift 2939954
  have htrace : WordTrace (prefixWord ++ tailWord_2939954) baseStart_2939954 baseEnd_2939954 := by
    simpa [prefixWord, tailWord_2939954, baseEnd_2939954] using wordTrace_append hprefix tailTrace_2939954
  have hstable : (prefixWord ++ tailWord_2939954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939954).length < 2 ^ (prefixWord ++ tailWord_2939954).sum := by decide
  have hdescent : baseEnd_2939954 < baseStart_2939954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939986 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_2939986 : Nat := 118140960795 + 2939986 * 2 ^ 59
def prefixEnd_2939986 : Nat := 4983230072969 + 3 ^ 40 * 2939986 * 2
def baseEnd_2939986 : Nat := 1006417290326293016636171

theorem tailTrace_2939986 : CollatzResearch.WordTrace tailWord_2939986 prefixEnd_2939986 1006417290326293016636171 := by
  unfold tailWord_2939986
  simp only [CollatzResearch.WordTrace]
  refine ⟨26807524681735076619729953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71486732484626870985946541 26807524681735076619729953)
  ·
    refine ⟨20105643511301307464797465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26807524681735076619729953 20105643511301307464797465)
    ·
      refine ⟨15079232633475980598598099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20105643511301307464797465 15079232633475980598598099)
      ·
        refine ⟨22618848950213970897897149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15079232633475980598598099 22618848950213970897897149)
        ·
          refine ⟨8482068356330239086711431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22618848950213970897897149 8482068356330239086711431)
          ·
            refine ⟨12723102534495358630067147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8482068356330239086711431 12723102534495358630067147)
            ·
              refine ⟨19084653801743037945100721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12723102534495358630067147 19084653801743037945100721)
              ·
                refine ⟨14313490351307278458825541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19084653801743037945100721 14313490351307278458825541)
                ·
                  refine ⟨2683779440870114711029789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14313490351307278458825541 2683779440870114711029789)
                  ·
                    refine ⟨1006417290326293016636171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683779440870114711029789 1006417290326293016636171)
                    ·
                      rfl

theorem cell22_2939986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_2939986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2939986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2939986 prefixEnd_2939986 := by exact prefixLift 2939986
  have htrace : WordTrace (prefixWord ++ tailWord_2939986) baseStart_2939986 baseEnd_2939986 := by
    simpa [prefixWord, tailWord_2939986, baseEnd_2939986] using wordTrace_append hprefix tailTrace_2939986
  have hstable : (prefixWord ++ tailWord_2939986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939986).length < 2 ^ (prefixWord ++ tailWord_2939986).sum := by decide
  have hdescent : baseEnd_2939986 < baseStart_2939986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940061 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 5]
def baseStart_2940061 : Nat := 118140960795 + 2940061 * 2 ^ 59
def prefixEnd_2940061 : Nat := 4983230072969 + 3 ^ 40 * 2940061 * 2
def baseEnd_2940061 : Nat := 335480988119672607003647

theorem tailTrace_2940061 : CollatzResearch.WordTrace tailWord_2940061 prefixEnd_2940061 335480988119672607003647 := by
  unfold tailWord_2940061
  simp only [CollatzResearch.WordTrace]
  refine ⟨107232834201668594287900037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71488556134445729525266691 107232834201668594287900037)
  ·
    refine ⟨20106156412812861428981257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107232834201668594287900037 20106156412812861428981257)
    ·
      refine ⟨15079617309609646071735943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20106156412812861428981257 15079617309609646071735943)
      ·
        refine ⟨22619425964414469107603915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15079617309609646071735943 22619425964414469107603915)
        ·
          refine ⟨33929138946621703661405873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22619425964414469107603915 33929138946621703661405873)
          ·
            refine ⟨25446854209966277746054405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33929138946621703661405873 25446854209966277746054405)
            ·
              refine ⟨4771285164368677077385201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25446854209966277746054405 4771285164368677077385201)
              ·
                refine ⟨3578463873276507808038901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4771285164368677077385201 3578463873276507808038901)
                ·
                  refine ⟨335480988119672607003647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3578463873276507808038901 335480988119672607003647)
                  ·
                    rfl

theorem cell22_2940061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_2940061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940061 prefixEnd_2940061 := by exact prefixLift 2940061
  have htrace : WordTrace (prefixWord ++ tailWord_2940061) baseStart_2940061 baseEnd_2940061 := by
    simpa [prefixWord, tailWord_2940061, baseEnd_2940061] using wordTrace_append hprefix tailTrace_2940061
  have hstable : (prefixWord ++ tailWord_2940061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940061).length < 2 ^ (prefixWord ++ tailWord_2940061).sum := by decide
  have hdescent : baseEnd_2940061 < baseStart_2940061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940089 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 8]
def baseStart_2940089 : Nat := 118140960795 + 2940089 * 2 ^ 59
def prefixEnd_2940089 : Nat := 4983230072969 + 3 ^ 40 * 2940089 * 2
def baseEnd_2940089 : Nat := 335484183110411693770285

theorem tailTrace_2940089 : CollatzResearch.WordTrace tailWord_2940089 prefixEnd_2940089 335484183110411693770285 := by
  unfold tailWord_2940089
  simp only [CollatzResearch.WordTrace]
  refine ⟨107233855445567155069919321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71489236963711436713279547 107233855445567155069919321)
  ·
    refine ⟨80425391584175366302439491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107233855445567155069919321 80425391584175366302439491)
    ·
      refine ⟨120638087376263049453659237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80425391584175366302439491 120638087376263049453659237)
      ·
        refine ⟨22619641383049321772561107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120638087376263049453659237 22619641383049321772561107)
        ·
          refine ⟨33929462074573982658841661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22619641383049321772561107 33929462074573982658841661)
          ·
            refine ⟨12723548277965243497065623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33929462074573982658841661 12723548277965243497065623)
            ·
              refine ⟨19085322416947865245598435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12723548277965243497065623 19085322416947865245598435)
              ·
                refine ⟨28627983625421797868397653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19085322416947865245598435 28627983625421797868397653)
                ·
                  refine ⟨335484183110411693770285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28627983625421797868397653 335484183110411693770285)
                  ·
                    rfl

theorem cell22_2940089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_2940089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940089 prefixEnd_2940089 := by exact prefixLift 2940089
  have htrace : WordTrace (prefixWord ++ tailWord_2940089) baseStart_2940089 baseEnd_2940089 := by
    simpa [prefixWord, tailWord_2940089, baseEnd_2940089] using wordTrace_append hprefix tailTrace_2940089
  have hstable : (prefixWord ++ tailWord_2940089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940089).length < 2 ^ (prefixWord ++ tailWord_2940089).sum := by decide
  have hdescent : baseEnd_2940089 < baseStart_2940089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940138 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 1, 5]
def baseStart_2940138 : Nat := 118140960795 + 2940138 * 2 ^ 59
def prefixEnd_2940138 : Nat := 4983230072969 + 3 ^ 40 * 2940138 * 2
def baseEnd_2940138 : Nat := 1006469323032615286835705

theorem tailTrace_2940138 : CollatzResearch.WordTrace tailWord_2940138 prefixEnd_2940138 1006469323032615286835705 := by
  unfold tailWord_2940138
  simp only [CollatzResearch.WordTrace]
  refine ⟨26808910655597409109613267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71490428414926424292302045 26808910655597409109613267)
  ·
    refine ⟨40213365983396113664419901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26808910655597409109613267 40213365983396113664419901)
    ·
      refine ⟨15080012243773542624157463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40213365983396113664419901 15080012243773542624157463)
      ·
        refine ⟨22620018365660313936236195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15080012243773542624157463 22620018365660313936236195)
        ·
          refine ⟨33930027548490470904354293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22620018365660313936236195 33930027548490470904354293)
          ·
            refine ⟨3180940082670981647283215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33930027548490470904354293 3180940082670981647283215)
            ·
              refine ⟨4771410124006472470924823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180940082670981647283215 4771410124006472470924823)
              ·
                refine ⟨7157115186009708706387235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4771410124006472470924823 7157115186009708706387235)
                ·
                  refine ⟨10735672779014563059580853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7157115186009708706387235 10735672779014563059580853)
                  ·
                    refine ⟨1006469323032615286835705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10735672779014563059580853 1006469323032615286835705)
                    ·
                      rfl

theorem cell22_2940138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_2940138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940138 prefixEnd_2940138 := by exact prefixLift 2940138
  have htrace : WordTrace (prefixWord ++ tailWord_2940138) baseStart_2940138 baseEnd_2940138 := by
    simpa [prefixWord, tailWord_2940138, baseEnd_2940138] using wordTrace_append hprefix tailTrace_2940138
  have hstable : (prefixWord ++ tailWord_2940138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940138).length < 2 ^ (prefixWord ++ tailWord_2940138).sum := by decide
  have hdescent : baseEnd_2940138 < baseStart_2940138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940168 : List Nat := [2, 1, 3, 2, 5, 1, 8]
def baseStart_2940168 : Nat := 118140960795 + 2940168 * 2 ^ 59
def prefixEnd_2940168 : Nat := 4983230072969 + 3 ^ 40 * 2940168 * 2
def baseEnd_2940168 : Nat := 37277021949840933651319

theorem tailTrace_2940168 : CollatzResearch.WordTrace tailWord_2940168 prefixEnd_2940168 37277021949840933651319 := by
  unfold tailWord_2940168
  simp only [CollatzResearch.WordTrace]
  refine ⟨53618368406140475781022579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71491157874853967708030105 53618368406140475781022579)
  ·
    refine ⟨80427552609210713671533869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53618368406140475781022579 80427552609210713671533869)
    ·
      refine ⟨30160332228454017626825201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80427552609210713671533869 30160332228454017626825201)
      ·
        refine ⟨22620249171340513220118901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30160332228454017626825201 22620249171340513220118901)
        ·
          refine ⟨2120648359813173114386147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22620249171340513220118901 2120648359813173114386147)
          ·
            refine ⟨3180972539719759671579221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120648359813173114386147 3180972539719759671579221)
            ·
              refine ⟨37277021949840933651319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3180972539719759671579221 37277021949840933651319)
              ·
                rfl

theorem cell22_2940168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 8].length) (baseStart_2940168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940168 prefixEnd_2940168 := by exact prefixLift 2940168
  have htrace : WordTrace (prefixWord ++ tailWord_2940168) baseStart_2940168 baseEnd_2940168 := by
    simpa [prefixWord, tailWord_2940168, baseEnd_2940168] using wordTrace_append hprefix tailTrace_2940168
  have hstable : (prefixWord ++ tailWord_2940168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940168).length < 2 ^ (prefixWord ++ tailWord_2940168).sum := by decide
  have hdescent : baseEnd_2940168 < baseStart_2940168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940241 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 6]
def baseStart_2940241 : Nat := 118140960795 + 2940241 * 2 ^ 59
def prefixEnd_2940241 : Nat := 4983230072969 + 3 ^ 40 * 2940241 * 2
def baseEnd_2940241 : Nat := 335501527345852450503463

theorem tailTrace_2940241 : CollatzResearch.WordTrace tailWord_2940241 prefixEnd_2940241 335501527345852450503463 := by
  unfold tailWord_2940241
  simp only [CollatzResearch.WordTrace]
  refine ⟨107239399341016485029452577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71492932894010990019635051 107239399341016485029452577)
  ·
    refine ⟨80429549505762363772089433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107239399341016485029452577 80429549505762363772089433)
    ·
      refine ⟨60322162129321772829067075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80429549505762363772089433 60322162129321772829067075)
      ·
        refine ⟨90483243193982659243600613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60322162129321772829067075 90483243193982659243600613)
        ·
          refine ⟨16965608098871748608175115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90483243193982659243600613 16965608098871748608175115)
          ·
            refine ⟨25448412148307622912262673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16965608098871748608175115 25448412148307622912262673)
            ·
              refine ⟨19086309111230717184197005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25448412148307622912262673 19086309111230717184197005)
              ·
                refine ⟨7157365916711518944073877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19086309111230717184197005 7157365916711518944073877)
                ·
                  refine ⟨335501527345852450503463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7157365916711518944073877 335501527345852450503463)
                  ·
                    rfl

theorem cell22_2940241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_2940241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940241 prefixEnd_2940241 := by exact prefixLift 2940241
  have htrace : WordTrace (prefixWord ++ tailWord_2940241) baseStart_2940241 baseEnd_2940241 := by
    simpa [prefixWord, tailWord_2940241, baseEnd_2940241] using wordTrace_append hprefix tailTrace_2940241
  have hstable : (prefixWord ++ tailWord_2940241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940241).length < 2 ^ (prefixWord ++ tailWord_2940241).sum := by decide
  have hdescent : baseEnd_2940241 < baseStart_2940241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940258 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 6]
def baseStart_2940258 : Nat := 118140960795 + 2940258 * 2 ^ 59
def prefixEnd_2940258 : Nat := 4983230072969 + 3 ^ 40 * 2940258 * 2
def baseEnd_2940258 : Nat := 335503467161658324611779

theorem tailTrace_2940258 : CollatzResearch.WordTrace tailWord_2940258 prefixEnd_2940258 335503467161658324611779 := by
  unfold tailWord_2940258
  simp only [CollatzResearch.WordTrace]
  refine ⟨26810004845488724233205357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71493346254636597955214285 26810004845488724233205357)
  ·
    refine ⟨10053751817058271587452009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26810004845488724233205357 10053751817058271587452009)
    ·
      refine ⟨7540313862793703690589007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10053751817058271587452009 7540313862793703690589007)
      ·
        refine ⟨11310470794190555535883511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7540313862793703690589007 11310470794190555535883511)
        ·
          refine ⟨16965706191285833303825267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11310470794190555535883511 16965706191285833303825267)
          ·
            refine ⟨25448559286928749955737901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16965706191285833303825267 25448559286928749955737901)
            ·
              refine ⟨9543209732598281233401713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25448559286928749955737901 9543209732598281233401713)
              ·
                refine ⟨7157407299448710925051285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9543209732598281233401713 7157407299448710925051285)
                ·
                  refine ⟨335503467161658324611779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7157407299448710925051285 335503467161658324611779)
                  ·
                    rfl

theorem cell22_2940258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_2940258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940258 prefixEnd_2940258 := by exact prefixLift 2940258
  have htrace : WordTrace (prefixWord ++ tailWord_2940258) baseStart_2940258 baseEnd_2940258 := by
    simpa [prefixWord, tailWord_2940258, baseEnd_2940258] using wordTrace_append hprefix tailTrace_2940258
  have hstable : (prefixWord ++ tailWord_2940258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940258).length < 2 ^ (prefixWord ++ tailWord_2940258).sum := by decide
  have hdescent : baseEnd_2940258 < baseStart_2940258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940271 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 1, 6]
def baseStart_2940271 : Nat := 118140960795 + 2940271 * 2 ^ 59
def prefixEnd_2940271 : Nat := 4983230072969 + 3 ^ 40 * 2940271 * 2
def baseEnd_2940271 : Nat := 1006514851650647273260297

theorem tailTrace_2940271 : CollatzResearch.WordTrace tailWord_2940271 prefixEnd_2940271 1006514851650647273260297 := by
  unfold tailWord_2940271
  simp only [CollatzResearch.WordTrace]
  refine ⟨107240493530907800153044667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71493662353938533435363111 107240493530907800153044667)
  ·
    refine ⟨160860740296361700229567001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107240493530907800153044667 160860740296361700229567001)
    ·
      refine ⟨120645555222271275172175251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160860740296361700229567001 120645555222271275172175251)
      ·
        refine ⟨180968332833406912758262877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120645555222271275172175251 180968332833406912758262877)
        ·
          refine ⟨67863124812527592284348579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180968332833406912758262877 67863124812527592284348579)
          ·
            refine ⟨101794687218791388426522869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67863124812527592284348579 101794687218791388426522869)
            ·
              refine ⟨9543251926761692664986519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101794687218791388426522869 9543251926761692664986519)
              ·
                refine ⟨14314877890142538997479779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9543251926761692664986519 14314877890142538997479779)
                ·
                  refine ⟨21472316835213808496219669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14314877890142538997479779 21472316835213808496219669)
                  ·
                    refine ⟨1006514851650647273260297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21472316835213808496219669 1006514851650647273260297)
                    ·
                      rfl

theorem cell22_2940271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_2940271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940271 prefixEnd_2940271 := by exact prefixLift 2940271
  have htrace : WordTrace (prefixWord ++ tailWord_2940271) baseStart_2940271 baseEnd_2940271 := by
    simpa [prefixWord, tailWord_2940271, baseEnd_2940271] using wordTrace_append hprefix tailTrace_2940271
  have hstable : (prefixWord ++ tailWord_2940271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940271).length < 2 ^ (prefixWord ++ tailWord_2940271).sum := by decide
  have hdescent : baseEnd_2940271 < baseStart_2940271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940361 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_2940361 : Nat := 118140960795 + 2940361 * 2 ^ 59
def prefixEnd_2940361 : Nat := 4983230072969 + 3 ^ 40 * 2940361 * 2
def baseEnd_2940361 : Nat := 1006545660489917038510021

theorem tailTrace_2940361 : CollatzResearch.WordTrace tailWord_2940361 prefixEnd_2940361 1006545660489917038510021 := by
  unfold tailWord_2940361
  simp only [CollatzResearch.WordTrace]
  refine ⟨107243776100581745523820937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71495850733721163682547291 107243776100581745523820937)
  ·
    refine ⟨80432832075436309142865703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107243776100581745523820937 80432832075436309142865703)
    ·
      refine ⟨120649248113154463714298555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80432832075436309142865703 120649248113154463714298555)
      ·
        refine ⟨180973872169731695571447833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120649248113154463714298555 180973872169731695571447833)
        ·
          refine ⟨135730404127298771678585875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180973872169731695571447833 135730404127298771678585875)
          ·
            refine ⟨203595606190948157517878813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135730404127298771678585875 203595606190948157517878813)
            ·
              refine ⟨76348352321605559069204555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203595606190948157517878813 76348352321605559069204555)
              ·
                refine ⟨114522528482408338603806833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76348352321605559069204555 114522528482408338603806833)
                ·
                  refine ⟨85891896361806253952855125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114522528482408338603806833 85891896361806253952855125)
                  ·
                    refine ⟨1006545660489917038510021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85891896361806253952855125 1006545660489917038510021)
                    ·
                      rfl

theorem cell22_2940361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_2940361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940361 prefixEnd_2940361 := by exact prefixLift 2940361
  have htrace : WordTrace (prefixWord ++ tailWord_2940361) baseStart_2940361 baseEnd_2940361 := by
    simpa [prefixWord, tailWord_2940361, baseEnd_2940361] using wordTrace_append hprefix tailTrace_2940361
  have hstable : (prefixWord ++ tailWord_2940361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940361).length < 2 ^ (prefixWord ++ tailWord_2940361).sum := by decide
  have hdescent : baseEnd_2940361 < baseStart_2940361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940410 : List Nat := [3, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_2940410 : Nat := 118140960795 + 2940410 * 2 ^ 59
def prefixEnd_2940410 : Nat := 4983230072969 + 3 ^ 40 * 2940410 * 2
def baseEnd_2940410 : Nat := 335520811397099081344957

theorem tailTrace_2940410 : CollatzResearch.WordTrace tailWord_2940410 prefixEnd_2940410 335520811397099081344957 := by
  unfold tailWord_2940410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26811390819351056723088671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71497042184936151261569789 26811390819351056723088671)
  ·
    refine ⟨40217086229026585084633007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26811390819351056723088671 40217086229026585084633007)
    ·
      refine ⟨60325629343539877626949511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40217086229026585084633007 60325629343539877626949511)
      ·
        refine ⟨90488444015309816440424267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60325629343539877626949511 90488444015309816440424267)
        ·
          refine ⟨135732666022964724660636401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90488444015309816440424267 135732666022964724660636401)
          ·
            refine ⟨101799499517223543495477301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135732666022964724660636401 101799499517223543495477301)
            ·
              refine ⟨9543703079739707202700997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101799499517223543495477301 9543703079739707202700997)
              ·
                refine ⟨1789444327451195100506437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9543703079739707202700997 1789444327451195100506437)
                ·
                  refine ⟨335520811397099081344957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789444327451195100506437 335520811397099081344957)
                  ·
                    rfl

theorem cell22_2940410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_2940410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940410 prefixEnd_2940410 := by exact prefixLift 2940410
  have htrace : WordTrace (prefixWord ++ tailWord_2940410) baseStart_2940410 baseEnd_2940410 := by
    simpa [prefixWord, tailWord_2940410, baseEnd_2940410] using wordTrace_append hprefix tailTrace_2940410
  have hstable : (prefixWord ++ tailWord_2940410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940410).length < 2 ^ (prefixWord ++ tailWord_2940410).sum := by decide
  have hdescent : baseEnd_2940410 < baseStart_2940410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940425 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 2, 3]
def baseStart_2940425 : Nat := 118140960795 + 2940425 * 2 ^ 59
def prefixEnd_2940425 : Nat := 4983230072969 + 3 ^ 40 * 2940425 * 2
def baseEnd_2940425 : Nat := 1006567568997842204909825

theorem tailTrace_2940425 : CollatzResearch.WordTrace tailWord_2940425 prefixEnd_2940425 1006567568997842204909825 := by
  unfold tailWord_2940425
  simp only [CollatzResearch.WordTrace]
  refine ⟨107246110372349884454150729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71497406914899922969433819 107246110372349884454150729)
  ·
    refine ⟨80434582779262413340613047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107246110372349884454150729 80434582779262413340613047)
    ·
      refine ⟨120651874168893620010919571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80434582779262413340613047 120651874168893620010919571)
      ·
        refine ⟨180977811253340430016379357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120651874168893620010919571 180977811253340430016379357)
        ·
          refine ⟨67866679220002661256142259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180977811253340430016379357 67866679220002661256142259)
          ·
            refine ⟨101800018830003991884213389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67866679220002661256142259 101800018830003991884213389)
            ·
              refine ⟨38175007061251496956580021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101800018830003991884213389 38175007061251496956580021)
              ·
                refine ⟨3578906911992327839679377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38175007061251496956580021 3578906911992327839679377)
                ·
                  refine ⟨2684180183994245879759533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3578906911992327839679377 2684180183994245879759533)
                  ·
                    refine ⟨1006567568997842204909825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2684180183994245879759533 1006567568997842204909825)
                    ·
                      rfl

theorem cell22_2940425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_2940425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940425 prefixEnd_2940425 := by exact prefixLift 2940425
  have htrace : WordTrace (prefixWord ++ tailWord_2940425) baseStart_2940425 baseEnd_2940425 := by
    simpa [prefixWord, tailWord_2940425, baseEnd_2940425] using wordTrace_append hprefix tailTrace_2940425
  have hstable : (prefixWord ++ tailWord_2940425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940425).length < 2 ^ (prefixWord ++ tailWord_2940425).sum := by decide
  have hdescent : baseEnd_2940425 < baseStart_2940425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940440 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_2940440 : Nat := 118140960795 + 2940440 * 2 ^ 59
def prefixEnd_2940440 : Nat := 4983230072969 + 3 ^ 40 * 2940440 * 2
def baseEnd_2940440 : Nat := 1006572703804387165784779

theorem tailTrace_2940440 : CollatzResearch.WordTrace tailWord_2940440 prefixEnd_2940440 1006572703804387165784779 := by
  unfold tailWord_2940440
  simp only [CollatzResearch.WordTrace]
  refine ⟨53623328733647771007973387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71497771644863694677297849 53623328733647771007973387)
  ·
    refine ⟨80434993100471656511960081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53623328733647771007973387 80434993100471656511960081)
    ·
      refine ⟨60326244825353742383970061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80434993100471656511960081 60326244825353742383970061)
      ·
        refine ⟨22622341809507653393988773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60326244825353742383970061 22622341809507653393988773)
        ·
          refine ⟨4241689089282685011372895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22622341809507653393988773 4241689089282685011372895)
          ·
            refine ⟨6362533633924027517059343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4241689089282685011372895 6362533633924027517059343)
            ·
              refine ⟨9543800450886041275589015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362533633924027517059343 9543800450886041275589015)
              ·
                refine ⟨14315700676329061913383523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9543800450886041275589015 14315700676329061913383523)
                ·
                  refine ⟨21473551014493592870075285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14315700676329061913383523 21473551014493592870075285)
                  ·
                    refine ⟨1006572703804387165784779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21473551014493592870075285 1006572703804387165784779)
                    ·
                      rfl

theorem cell22_2940440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_2940440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940440 prefixEnd_2940440 := by exact prefixLift 2940440
  have htrace : WordTrace (prefixWord ++ tailWord_2940440) baseStart_2940440 baseEnd_2940440 := by
    simpa [prefixWord, tailWord_2940440, baseEnd_2940440] using wordTrace_append hprefix tailTrace_2940440
  have hstable : (prefixWord ++ tailWord_2940440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940440).length < 2 ^ (prefixWord ++ tailWord_2940440).sum := by decide
  have hdescent : baseEnd_2940440 < baseStart_2940440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940534 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_2940534 : Nat := 118140960795 + 2940534 * 2 ^ 59
def prefixEnd_2940534 : Nat := 4983230072969 + 3 ^ 40 * 2940534 * 2
def baseEnd_2940534 : Nat := 335534960641800751311497

theorem tailTrace_2940534 : CollatzResearch.WordTrace tailWord_2940534 prefixEnd_2940534 335534960641800751311497 := by
  unfold tailWord_2940534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6703130370559687254366791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71500057285969997379912437 6703130370559687254366791)
  ·
    refine ⟨10054695555839530881550187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6703130370559687254366791 10054695555839530881550187)
    ·
      refine ⟨15082043333759296322325281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10054695555839530881550187 15082043333759296322325281)
      ·
        refine ⟨11311532500319472241743961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15082043333759296322325281 11311532500319472241743961)
        ·
          refine ⟨8483649375239604181307971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11311532500319472241743961 8483649375239604181307971)
          ·
            refine ⟨12725474062859406271961957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8483649375239604181307971 12725474062859406271961957)
            ·
              refine ⟨2386026386786138675992867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12725474062859406271961957 2386026386786138675992867)
              ·
                refine ⟨3579039580179208013989301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386026386786138675992867 3579039580179208013989301)
                ·
                  refine ⟨335534960641800751311497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579039580179208013989301 335534960641800751311497)
                  ·
                    rfl

theorem cell22_2940534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_2940534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940534 prefixEnd_2940534 := by exact prefixLift 2940534
  have htrace : WordTrace (prefixWord ++ tailWord_2940534) baseStart_2940534 baseEnd_2940534 := by
    simpa [prefixWord, tailWord_2940534, baseEnd_2940534] using wordTrace_append hprefix tailTrace_2940534
  have hstable : (prefixWord ++ tailWord_2940534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940534).length < 2 ^ (prefixWord ++ tailWord_2940534).sum := by decide
  have hdescent : baseEnd_2940534 < baseStart_2940534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940560 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 6, 3]
def baseStart_2940560 : Nat := 118140960795 + 2940560 * 2 ^ 59
def prefixEnd_2940560 : Nat := 4983230072969 + 3 ^ 40 * 2940560 * 2
def baseEnd_2940560 : Nat := 1006613782256746852784411

theorem tailTrace_2940560 : CollatzResearch.WordTrace tailWord_2940560 prefixEnd_2940560 1006613782256746852784411 := by
  unfold tailWord_2940560
  simp only [CollatzResearch.WordTrace]
  refine ⟨53625517113430401255157567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71500689484573868340210089 53625517113430401255157567)
  ·
    refine ⟨80438275670145601882736351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53625517113430401255157567 80438275670145601882736351)
    ·
      refine ⟨120657413505218402824104527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80438275670145601882736351 120657413505218402824104527)
      ·
        refine ⟨180986120257827604236156791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120657413505218402824104527 180986120257827604236156791)
        ·
          refine ⟨271479180386741406354235187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180986120257827604236156791 271479180386741406354235187)
          ·
            refine ⟨407218770580112109531352781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271479180386741406354235187 407218770580112109531352781)
            ·
              refine ⟨152707038967542041074257293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407218770580112109531352781 152707038967542041074257293)
              ·
                refine ⟨57265139612828265402846485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152707038967542041074257293 57265139612828265402846485)
                ·
                  refine ⟨2684303419351324940758429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57265139612828265402846485 2684303419351324940758429)
                  ·
                    refine ⟨1006613782256746852784411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2684303419351324940758429 1006613782256746852784411)
                    ·
                      rfl

theorem cell22_2940560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_2940560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940560 prefixEnd_2940560 := by exact prefixLift 2940560
  have htrace : WordTrace (prefixWord ++ tailWord_2940560) baseStart_2940560 baseEnd_2940560 := by
    simpa [prefixWord, tailWord_2940560, baseEnd_2940560] using wordTrace_append hprefix tailTrace_2940560
  have hstable : (prefixWord ++ tailWord_2940560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940560).length < 2 ^ (prefixWord ++ tailWord_2940560).sum := by decide
  have hdescent : baseEnd_2940560 < baseStart_2940560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940622 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_2940622 : Nat := 118140960795 + 2940622 * 2 ^ 59
def prefixEnd_2940622 : Nat := 4983230072969 + 3 ^ 40 * 2940622 * 2
def baseEnd_2940622 : Nat := 1006635006123799357734221

theorem tailTrace_2940622 : CollatzResearch.WordTrace tailWord_2940622 prefixEnd_2940622 1006635006123799357734221 := by
  unfold tailWord_2940622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13406661944079523387384015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71502197035090791399381413 13406661944079523387384015)
  ·
    refine ⟨20109992916119285081076023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13406661944079523387384015 20109992916119285081076023)
    ·
      refine ⟨30164989374178927621614035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20109992916119285081076023 30164989374178927621614035)
      ·
        refine ⟨45247484061268391432421053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30164989374178927621614035 45247484061268391432421053)
        ·
          refine ⟨16967806522975646787157895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45247484061268391432421053 16967806522975646787157895)
          ·
            refine ⟨25451709784463470180736843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16967806522975646787157895 25451709784463470180736843)
            ·
              refine ⟨38177564676695205271105265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25451709784463470180736843 38177564676695205271105265)
              ·
                refine ⟨28633173507521403953328949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38177564676695205271105265 28633173507521403953328949)
                ·
                  refine ⟨2684360016330131620624589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28633173507521403953328949 2684360016330131620624589)
                  ·
                    refine ⟨1006635006123799357734221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2684360016330131620624589 1006635006123799357734221)
                    ·
                      rfl

theorem cell22_2940622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_2940622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940622 prefixEnd_2940622 := by exact prefixLift 2940622
  have htrace : WordTrace (prefixWord ++ tailWord_2940622) baseStart_2940622 baseEnd_2940622 := by
    simpa [prefixWord, tailWord_2940622, baseEnd_2940622] using wordTrace_append hprefix tailTrace_2940622
  have hstable : (prefixWord ++ tailWord_2940622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940622).length < 2 ^ (prefixWord ++ tailWord_2940622).sum := by decide
  have hdescent : baseEnd_2940622 < baseStart_2940622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940639 : List Nat := [1, 1, 2, 3, 2, 2, 1, 6, 1, 3]
def baseStart_2940639 : Nat := 118140960795 + 2940639 * 2 ^ 59
def prefixEnd_2940639 : Nat := 4983230072969 + 3 ^ 40 * 2940639 * 2
def baseEnd_2940639 : Nat := 1006640825571216980059169

theorem tailTrace_2940639 : CollatzResearch.WordTrace tailWord_2940639 prefixEnd_2940639 1006640825571216980059169 := by
  unfold tailWord_2940639
  simp only [CollatzResearch.WordTrace]
  refine ⟨107253915593574599002440971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71502610395716399334960647 107253915593574599002440971)
  ·
    refine ⟨160880873390361898503661457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107253915593574599002440971 160880873390361898503661457)
    ·
      refine ⟨120660655042771423877746093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160880873390361898503661457 120660655042771423877746093)
      ·
        refine ⟨45247745641039283954154785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120660655042771423877746093 45247745641039283954154785)
        ·
          refine ⟨33935809230779462965616089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45247745641039283954154785 33935809230779462965616089)
          ·
            refine ⟨25451856923084597224212067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33935809230779462965616089 25451856923084597224212067)
            ·
              refine ⟨38177785384626895836318101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25451856923084597224212067 38177785384626895836318101)
              ·
                refine ⟨1789583689904385742327411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38177785384626895836318101 1789583689904385742327411)
                ·
                  refine ⟨2684375534856578613491117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789583689904385742327411 2684375534856578613491117)
                  ·
                    refine ⟨1006640825571216980059169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2684375534856578613491117 1006640825571216980059169)
                    ·
                      rfl

theorem cell22_2940639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 3].length) (baseStart_2940639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940639 prefixEnd_2940639 := by exact prefixLift 2940639
  have htrace : WordTrace (prefixWord ++ tailWord_2940639) baseStart_2940639 baseEnd_2940639 := by
    simpa [prefixWord, tailWord_2940639, baseEnd_2940639] using wordTrace_append hprefix tailTrace_2940639
  have hstable : (prefixWord ++ tailWord_2940639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940639).length < 2 ^ (prefixWord ++ tailWord_2940639).sum := by decide
  have hdescent : baseEnd_2940639 < baseStart_2940639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940690 : List Nat := [3, 2, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2940690 : Nat := 118140960795 + 2940690 * 2 ^ 59
def prefixEnd_2940690 : Nat := 4983230072969 + 3 ^ 40 * 2940690 * 2
def baseEnd_2940690 : Nat := 1006658283913469847034013

theorem tailTrace_2940690 : CollatzResearch.WordTrace tailWord_2940690 prefixEnd_2940690 1006658283913469847034013 := by
  unfold tailWord_2940690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26813943929097458678136881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71503850477593223141698349 26813943929097458678136881)
  ·
    refine ⟨20110457946823094008602661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26813943929097458678136881 20110457946823094008602661)
    ·
      refine ⟨3770710865029330126612999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20110457946823094008602661 3770710865029330126612999)
      ·
        refine ⟨5656066297543995189919499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770710865029330126612999 5656066297543995189919499)
        ·
          refine ⟨8484099446315992784879249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5656066297543995189919499 8484099446315992784879249)
          ·
            refine ⟨6363074584736994588659437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8484099446315992784879249 6363074584736994588659437)
            ·
              refine ⟨2386152969276372970747289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6363074584736994588659437 2386152969276372970747289)
              ·
                refine ⟨1789614726957279728060467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386152969276372970747289 1789614726957279728060467)
                ·
                  refine ⟨2684422090435919592090701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789614726957279728060467 2684422090435919592090701)
                  ·
                    refine ⟨1006658283913469847034013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2684422090435919592090701 1006658283913469847034013)
                    ·
                      rfl

theorem cell22_2940690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2940690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940690 prefixEnd_2940690 := by exact prefixLift 2940690
  have htrace : WordTrace (prefixWord ++ tailWord_2940690) baseStart_2940690 baseEnd_2940690 := by
    simpa [prefixWord, tailWord_2940690, baseEnd_2940690] using wordTrace_append hprefix tailTrace_2940690
  have hstable : (prefixWord ++ tailWord_2940690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940690).length < 2 ^ (prefixWord ++ tailWord_2940690).sum := by decide
  have hdescent : baseEnd_2940690 < baseStart_2940690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940748 : List Nat := [2, 2, 1, 3, 4, 2, 2, 2, 4]
def baseStart_2940748 : Nat := 118140960795 + 2940748 * 2 ^ 59
def prefixEnd_2940748 : Nat := 4983230072969 + 3 ^ 40 * 2940748 * 2
def baseEnd_2940748 : Nat := 335559379499592343027945

theorem tailTrace_2940748 : CollatzResearch.WordTrace tailWord_2940748 prefixEnd_2940748 335559379499592343027945 := by
  unfold tailWord_2940748
  simp only [CollatzResearch.WordTrace]
  refine ⟨53628945575089855309079449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71505260766786473745439265 53628945575089855309079449)
  ·
    refine ⟨40221709181317391481809587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53628945575089855309079449 40221709181317391481809587)
    ·
      refine ⟨60332563771976087222714381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40221709181317391481809587 60332563771976087222714381)
      ·
        refine ⟨22624711414491032708517893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60332563771976087222714381 22624711414491032708517893)
        ·
          refine ⟨4242133390217068632847105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22624711414491032708517893 4242133390217068632847105)
          ·
            refine ⟨3181600042662801474635329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242133390217068632847105 3181600042662801474635329)
            ·
              refine ⟨2386200031997101105976497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3181600042662801474635329 2386200031997101105976497)
              ·
                refine ⟨1789650023997825829482373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386200031997101105976497 1789650023997825829482373)
                ·
                  refine ⟨335559379499592343027945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789650023997825829482373 335559379499592343027945)
                  ·
                    rfl

theorem cell22_2940748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_2940748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940748 prefixEnd_2940748 := by exact prefixLift 2940748
  have htrace : WordTrace (prefixWord ++ tailWord_2940748) baseStart_2940748 baseEnd_2940748 := by
    simpa [prefixWord, tailWord_2940748, baseEnd_2940748] using wordTrace_append hprefix tailTrace_2940748
  have hstable : (prefixWord ++ tailWord_2940748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940748).length < 2 ^ (prefixWord ++ tailWord_2940748).sum := by decide
  have hdescent : baseEnd_2940748 < baseStart_2940748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940759 : List Nat := [1, 1, 3, 2, 5, 2, 1, 7]
def baseStart_2940759 : Nat := 118140960795 + 2940759 * 2 ^ 59
def prefixEnd_2940759 : Nat := 4983230072969 + 3 ^ 40 * 2940759 * 2
def baseEnd_2940759 : Nat := 111853544891508518562089

theorem tailTrace_2940759 : CollatzResearch.WordTrace tailWord_2940759 prefixEnd_2940759 111853544891508518562089 := by
  unfold tailWord_2940759
  simp only [CollatzResearch.WordTrace]
  refine ⟨107258292353139859496809331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71505528235426572997872887 107258292353139859496809331)
  ·
    refine ⟨160887438529709789245213997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107258292353139859496809331 160887438529709789245213997)
    ·
      refine ⟨60332789448641170966955249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160887438529709789245213997 60332789448641170966955249)
      ·
        refine ⟨45249592086480878225216437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60332789448641170966955249 45249592086480878225216437)
        ·
          refine ⟨4242149258107582333614041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45249592086480878225216437 4242149258107582333614041)
          ·
            refine ⟨3181611943580686750210531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242149258107582333614041 3181611943580686750210531)
            ·
              refine ⟨4772417915371030125315797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181611943580686750210531 4772417915371030125315797)
              ·
                refine ⟨111853544891508518562089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4772417915371030125315797 111853544891508518562089)
                ·
                  rfl

theorem cell22_2940759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 7].length) (baseStart_2940759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940759 prefixEnd_2940759 := by exact prefixLift 2940759
  have htrace : WordTrace (prefixWord ++ tailWord_2940759) baseStart_2940759 baseEnd_2940759 := by
    simpa [prefixWord, tailWord_2940759, baseEnd_2940759] using wordTrace_append hprefix tailTrace_2940759
  have hstable : (prefixWord ++ tailWord_2940759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940759).length < 2 ^ (prefixWord ++ tailWord_2940759).sum := by decide
  have hdescent : baseEnd_2940759 < baseStart_2940759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940778 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_2940778 : Nat := 118140960795 + 2940778 * 2 ^ 59
def prefixEnd_2940778 : Nat := 4983230072969 + 3 ^ 40 * 2940778 * 2
def baseEnd_2940778 : Nat := 1006688408111866950833743

theorem tailTrace_2940778 : CollatzResearch.WordTrace tailWord_2940778 prefixEnd_2940778 1006688408111866950833743 := by
  unfold tailWord_2940778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26814746335017756435437747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71505990226714017161167325 26814746335017756435437747)
  ·
    refine ⟨40222119502526634653156621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26814746335017756435437747 40222119502526634653156621)
    ·
      refine ⟨15083294813447487994933733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40222119502526634653156621 15083294813447487994933733)
      ·
        refine ⟨2828117777521403999050075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15083294813447487994933733 2828117777521403999050075)
        ·
          refine ⟨4242176666282105998575113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828117777521403999050075 4242176666282105998575113)
          ·
            refine ⟨3181632499711579498931335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242176666282105998575113 3181632499711579498931335)
            ·
              refine ⟨4772448749567369248397003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181632499711579498931335 4772448749567369248397003)
              ·
                refine ⟨7158673124351053872595505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4772448749567369248397003 7158673124351053872595505)
                ·
                  refine ⟨5369004843263290404446629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7158673124351053872595505 5369004843263290404446629)
                  ·
                    refine ⟨1006688408111866950833743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369004843263290404446629 1006688408111866950833743)
                    ·
                      rfl

theorem cell22_2940778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_2940778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940778 prefixEnd_2940778 := by exact prefixLift 2940778
  have htrace : WordTrace (prefixWord ++ tailWord_2940778) baseStart_2940778 baseEnd_2940778 := by
    simpa [prefixWord, tailWord_2940778, baseEnd_2940778] using wordTrace_append hprefix tailTrace_2940778
  have hstable : (prefixWord ++ tailWord_2940778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940778).length < 2 ^ (prefixWord ++ tailWord_2940778).sum := by decide
  have hdescent : baseEnd_2940778 < baseStart_2940778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940804 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 5]
def baseStart_2940804 : Nat := 118140960795 + 2940804 * 2 ^ 59
def prefixEnd_2940804 : Nat := 4983230072969 + 3 ^ 40 * 2940804 * 2
def baseEnd_2940804 : Nat := 335565769481070516561221

theorem tailTrace_2940804 : CollatzResearch.WordTrace tailWord_2940804 prefixEnd_2940804 335565769481070516561221 := by
  unfold tailWord_2940804
  simp only [CollatzResearch.WordTrace]
  refine ⟨53629966818988416091098733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71506622425317888121464977 53629966818988416091098733)
  ·
    refine ⟨20111237557120656034162025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53629966818988416091098733 20111237557120656034162025)
    ·
      refine ⟨15083428167840492025621519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20111237557120656034162025 15083428167840492025621519)
      ·
        refine ⟨22625142251760738038432279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15083428167840492025621519 22625142251760738038432279)
        ·
          refine ⟨33937713377641107057648419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22625142251760738038432279 33937713377641107057648419)
          ·
            refine ⟨50906570066461660586472629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33937713377641107057648419 50906570066461660586472629)
            ·
              refine ⟨4772490943730780679981809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50906570066461660586472629 4772490943730780679981809)
              ·
                refine ⟨3579368207798085509986357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4772490943730780679981809 3579368207798085509986357)
                ·
                  refine ⟨335565769481070516561221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579368207798085509986357 335565769481070516561221)
                  ·
                    rfl

theorem cell22_2940804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_2940804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940804 prefixEnd_2940804 := by exact prefixLift 2940804
  have htrace : WordTrace (prefixWord ++ tailWord_2940804) baseStart_2940804 baseEnd_2940804 := by
    simpa [prefixWord, tailWord_2940804, baseEnd_2940804] using wordTrace_append hprefix tailTrace_2940804
  have hstable : (prefixWord ++ tailWord_2940804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940804).length < 2 ^ (prefixWord ++ tailWord_2940804).sum := by decide
  have hdescent : baseEnd_2940804 < baseStart_2940804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940817 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_2940817 : Nat := 118140960795 + 2940817 * 2 ^ 59
def prefixEnd_2940817 : Nat := 4983230072969 + 3 ^ 40 * 2940817 * 2
def baseEnd_2940817 : Nat := 1006701758608883849108623

theorem tailTrace_2940817 : CollatzResearch.WordTrace tailWord_2940817 prefixEnd_2940817 1006701758608883849108623 := by
  unfold tailWord_2940817
  simp only [CollatzResearch.WordTrace]
  refine ⟨107260407786929735402420705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71506938524619823601613803 107260407786929735402420705)
  ·
    refine ⟨80445305840197301551815529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107260407786929735402420705 80445305840197301551815529)
    ·
      refine ⟨60333979380147976163861647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80445305840197301551815529 60333979380147976163861647)
      ·
        refine ⟨90500969070221964245792471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60333979380147976163861647 90500969070221964245792471)
        ·
          refine ⟨135751453605332946368688707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90500969070221964245792471 135751453605332946368688707)
          ·
            refine ⟨203627180407999419553033061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135751453605332946368688707 203627180407999419553033061)
            ·
              refine ⟨38180096326499891166193699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203627180407999419553033061 38180096326499891166193699)
              ·
                refine ⟨57270144489749836749290549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38180096326499891166193699 57270144489749836749290549)
                ·
                  refine ⟨5369076045914047195245989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57270144489749836749290549 5369076045914047195245989)
                  ·
                    refine ⟨1006701758608883849108623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369076045914047195245989 1006701758608883849108623)
                    ·
                      rfl

theorem cell22_2940817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_2940817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940817 prefixEnd_2940817 := by exact prefixLift 2940817
  have htrace : WordTrace (prefixWord ++ tailWord_2940817) baseStart_2940817 baseEnd_2940817 := by
    simpa [prefixWord, tailWord_2940817, baseEnd_2940817] using wordTrace_append hprefix tailTrace_2940817
  have hstable : (prefixWord ++ tailWord_2940817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940817).length < 2 ^ (prefixWord ++ tailWord_2940817).sum := by decide
  have hdescent : baseEnd_2940817 < baseStart_2940817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940847 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 3, 5]
def baseStart_2940847 : Nat := 118140960795 + 2940847 * 2 ^ 59
def prefixEnd_2940847 : Nat := 4983230072969 + 3 ^ 40 * 2940847 * 2
def baseEnd_2940847 : Nat := 1006712028221973770858531

theorem tailTrace_2940847 : CollatzResearch.WordTrace tailWord_2940847 prefixEnd_2940847 1006712028221973770858531 := by
  unfold tailWord_2940847
  simp only [CollatzResearch.WordTrace]
  refine ⟨107261501976821050526012795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71507667984547367017341863 107261501976821050526012795)
  ·
    refine ⟨160892252965231575789019193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107261501976821050526012795 160892252965231575789019193)
    ·
      refine ⟨120669189723923681841764395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160892252965231575789019193 120669189723923681841764395)
      ·
        refine ⟨181003784585885522762646593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120669189723923681841764395 181003784585885522762646593)
        ·
          refine ⟨135752838439414142071984945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181003784585885522762646593 135752838439414142071984945)
          ·
            refine ⟨101814628829560606553988709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135752838439414142071984945 101814628829560606553988709)
            ·
              refine ⟨19090242905542613728872883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101814628829560606553988709 19090242905542613728872883)
              ·
                refine ⟨28635364358313920593309325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19090242905542613728872883 28635364358313920593309325)
                ·
                  refine ⟨10738261634367720222490997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28635364358313920593309325 10738261634367720222490997)
                  ·
                    refine ⟨1006712028221973770858531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10738261634367720222490997 1006712028221973770858531)
                    ·
                      rfl

theorem cell22_2940847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_2940847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940847 prefixEnd_2940847 := by exact prefixLift 2940847
  have htrace : WordTrace (prefixWord ++ tailWord_2940847) baseStart_2940847 baseEnd_2940847 := by
    simpa [prefixWord, tailWord_2940847, baseEnd_2940847] using wordTrace_append hprefix tailTrace_2940847
  have hstable : (prefixWord ++ tailWord_2940847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940847).length < 2 ^ (prefixWord ++ tailWord_2940847).sum := by decide
  have hdescent : baseEnd_2940847 < baseStart_2940847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940864 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 4, 3]
def baseStart_2940864 : Nat := 118140960795 + 2940864 * 2 ^ 59
def prefixEnd_2940864 : Nat := 4983230072969 + 3 ^ 40 * 2940864 * 2
def baseEnd_2940864 : Nat := 1006717847669391393183479

theorem tailTrace_2940864 : CollatzResearch.WordTrace tailWord_2940864 prefixEnd_2940864 1006717847669391393183479 := by
  unfold tailWord_2940864
  simp only [CollatzResearch.WordTrace]
  refine ⟨53631061008879731214690823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71508081345172974952921097 53631061008879731214690823)
  ·
    refine ⟨80446591513319596822036235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53631061008879731214690823 80446591513319596822036235)
    ·
      refine ⟨120669887269979395233054353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80446591513319596822036235 120669887269979395233054353)
      ·
        refine ⟨90502415452484546424790765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120669887269979395233054353 90502415452484546424790765)
        ·
          refine ⟨33938405794681704909296537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90502415452484546424790765 33938405794681704909296537)
          ·
            refine ⟨25453804346011278681972403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33938405794681704909296537 25453804346011278681972403)
            ·
              refine ⟨38180706519016918022958605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25453804346011278681972403 38180706519016918022958605)
              ·
                refine ⟨14317764944631344258609477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38180706519016918022958605 14317764944631344258609477)
                ·
                  refine ⟨2684580927118377048489277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14317764944631344258609477 2684580927118377048489277)
                  ·
                    refine ⟨1006717847669391393183479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2684580927118377048489277 1006717847669391393183479)
                    ·
                      rfl

theorem cell22_2940864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_2940864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940864 prefixEnd_2940864 := by exact prefixLift 2940864
  have htrace : WordTrace (prefixWord ++ tailWord_2940864) baseStart_2940864 baseEnd_2940864 := by
    simpa [prefixWord, tailWord_2940864, baseEnd_2940864] using wordTrace_append hprefix tailTrace_2940864
  have hstable : (prefixWord ++ tailWord_2940864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940864).length < 2 ^ (prefixWord ++ tailWord_2940864).sum := by decide
  have hdescent : baseEnd_2940864 < baseStart_2940864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940898 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2940898 : Nat := 118140960795 + 2940898 * 2 ^ 59
def prefixEnd_2940898 : Nat := 4983230072969 + 3 ^ 40 * 2940898 * 2
def baseEnd_2940898 : Nat := 1006729486564226637833375

theorem tailTrace_2940898 : CollatzResearch.WordTrace tailWord_2940898 prefixEnd_2940898 1006729486564226637833375 := by
  unfold tailWord_2940898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26815840524909071559029837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71508908066424190824079565 26815840524909071559029837)
  ·
    refine ⟨10055940196840901834636189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26815840524909071559029837 10055940196840901834636189)
    ·
      refine ⟨3770977573815338187988571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10055940196840901834636189 3770977573815338187988571)
      ·
        refine ⟨5656466360723007281982857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770977573815338187988571 5656466360723007281982857)
        ·
          refine ⟨4242349770542255461487143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656466360723007281982857 4242349770542255461487143)
          ·
            refine ⟨6363524655813383192230715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242349770542255461487143 6363524655813383192230715)
            ·
              refine ⟨9545286983720074788346073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6363524655813383192230715 9545286983720074788346073)
              ·
                refine ⟨7158965237790056091259555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9545286983720074788346073 7158965237790056091259555)
                ·
                  refine ⟨10738447856685084136889333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7158965237790056091259555 10738447856685084136889333)
                  ·
                    refine ⟨1006729486564226637833375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10738447856685084136889333 1006729486564226637833375)
                    ·
                      rfl

theorem cell22_2940898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2940898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940898 prefixEnd_2940898 := by exact prefixLift 2940898
  have htrace : WordTrace (prefixWord ++ tailWord_2940898) baseStart_2940898 baseEnd_2940898 := by
    simpa [prefixWord, tailWord_2940898, baseEnd_2940898] using wordTrace_append hprefix tailTrace_2940898
  have hstable : (prefixWord ++ tailWord_2940898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940898).length < 2 ^ (prefixWord ++ tailWord_2940898).sum := by decide
  have hdescent : baseEnd_2940898 < baseStart_2940898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940907 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 4, 6]
def baseStart_2940907 : Nat := 118140960795 + 2940907 * 2 ^ 59
def prefixEnd_2940907 : Nat := 4983230072969 + 3 ^ 40 * 2940907 * 2
def baseEnd_2940907 : Nat := 1006732567448153614358347

theorem tailTrace_2940907 : CollatzResearch.WordTrace tailWord_2940907 prefixEnd_2940907 1006732567448153614358347 := by
  unfold tailWord_2940907
  simp only [CollatzResearch.WordTrace]
  refine ⟨107263690356603680773196975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71509126904402453848797983 107263690356603680773196975)
  ·
    refine ⟨160895535534905521159795463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107263690356603680773196975 160895535534905521159795463)
    ·
      refine ⟨241343303302358281739693195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160895535534905521159795463 241343303302358281739693195)
      ·
        refine ⟨362014954953537422609539793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241343303302358281739693195 362014954953537422609539793)
        ·
          refine ⟨271511216215153066957154845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362014954953537422609539793 271511216215153066957154845)
          ·
            refine ⟨101816706080682400108933067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271511216215153066957154845 101816706080682400108933067)
            ·
              refine ⟨152725059121023600163399601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101816706080682400108933067 152725059121023600163399601)
              ·
                refine ⟨114543794340767700122549701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152725059121023600163399601 114543794340767700122549701)
                ·
                  refine ⟨21476961438893943772978069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114543794340767700122549701 21476961438893943772978069)
                  ·
                    refine ⟨1006732567448153614358347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21476961438893943772978069 1006732567448153614358347)
                    ·
                      rfl

theorem cell22_2940907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_2940907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940907 prefixEnd_2940907 := by exact prefixLift 2940907
  have htrace : WordTrace (prefixWord ++ tailWord_2940907) baseStart_2940907 baseEnd_2940907 := by
    simpa [prefixWord, tailWord_2940907, baseEnd_2940907] using wordTrace_append hprefix tailTrace_2940907
  have hstable : (prefixWord ++ tailWord_2940907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940907).length < 2 ^ (prefixWord ++ tailWord_2940907).sum := by decide
  have hdescent : baseEnd_2940907 < baseStart_2940907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940939 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 5]
def baseStart_2940939 : Nat := 118140960795 + 2940939 * 2 ^ 59
def prefixEnd_2940939 : Nat := 4983230072969 + 3 ^ 40 * 2940939 * 2
def baseEnd_2940939 : Nat := 335581173900705399186083

theorem tailTrace_2940939 : CollatzResearch.WordTrace tailWord_2940939 prefixEnd_2940939 335581173900705399186083 := by
  unfold tailWord_2940939
  simp only [CollatzResearch.WordTrace]
  refine ⟨107264857492487750238361871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71509904994991833492241247 107264857492487750238361871)
  ·
    refine ⟨160897286238731625357542807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107264857492487750238361871 160897286238731625357542807)
    ·
      refine ⟨241345929358097438036314211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160897286238731625357542807 241345929358097438036314211)
      ·
        refine ⟨362018894037146157054471317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241345929358097438036314211 362018894037146157054471317)
        ·
          refine ⟨16969635657991226111928343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 362018894037146157054471317 16969635657991226111928343)
          ·
            refine ⟨25454453486986839167892515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16969635657991226111928343 25454453486986839167892515)
            ·
              refine ⟨38181680230480258751838773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25454453486986839167892515 38181680230480258751838773)
              ·
                refine ⟨3579532521607524257984885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38181680230480258751838773 3579532521607524257984885)
                ·
                  refine ⟨335581173900705399186083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579532521607524257984885 335581173900705399186083)
                  ·
                    rfl

theorem cell22_2940939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 5].length) (baseStart_2940939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940939 prefixEnd_2940939 := by exact prefixLift 2940939
  have htrace : WordTrace (prefixWord ++ tailWord_2940939) baseStart_2940939 baseEnd_2940939 := by
    simpa [prefixWord, tailWord_2940939, baseEnd_2940939] using wordTrace_append hprefix tailTrace_2940939
  have hstable : (prefixWord ++ tailWord_2940939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940939).length < 2 ^ (prefixWord ++ tailWord_2940939).sum := by decide
  have hdescent : baseEnd_2940939 < baseStart_2940939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2940990 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_2940990 : Nat := 118140960795 + 2940990 * 2 ^ 59
def prefixEnd_2940990 : Nat := 4983230072969 + 3 ^ 40 * 2940990 * 2
def baseEnd_2940990 : Nat := 335586993348123021511031

theorem tailTrace_2940990 : CollatzResearch.WordTrace tailWord_2940990 prefixEnd_2940990 335586993348123021511031 := by
  unfold tailWord_2940990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13408339701912873243558553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71511145076868657298978949 13408339701912873243558553)
  ·
    refine ⟨10056254776434654932668915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13408339701912873243558553 10056254776434654932668915)
    ·
      refine ⟨15084382164651982399003373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10056254776434654932668915 15084382164651982399003373)
      ·
        refine ⟨5656643311744493399626265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15084382164651982399003373 5656643311744493399626265)
        ·
          refine ⟨4242482483808370049719699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5656643311744493399626265 4242482483808370049719699)
          ·
            refine ⟨6363723725712555074579549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242482483808370049719699 6363723725712555074579549)
            ·
              refine ⟨2386396397142208152967331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6363723725712555074579549 2386396397142208152967331)
              ·
                refine ⟨3579594595713312229450997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386396397142208152967331 3579594595713312229450997)
                ·
                  refine ⟨335586993348123021511031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579594595713312229450997 335586993348123021511031)
                  ·
                    rfl

theorem cell22_2940990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_2940990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2940990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2940990 prefixEnd_2940990 := by exact prefixLift 2940990
  have htrace : WordTrace (prefixWord ++ tailWord_2940990) baseStart_2940990 baseEnd_2940990 := by
    simpa [prefixWord, tailWord_2940990, baseEnd_2940990] using wordTrace_append hprefix tailTrace_2940990
  have hstable : (prefixWord ++ tailWord_2940990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2940990).length < 2 ^ (prefixWord ++ tailWord_2940990).sum := by decide
  have hdescent : baseEnd_2940990 < baseStart_2940990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2940990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941016 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 4, 3]
def baseStart_2941016 : Nat := 118140960795 + 2941016 * 2 ^ 59
def prefixEnd_2941016 : Nat := 4983230072969 + 3 ^ 40 * 2941016 * 2
def baseEnd_2941016 : Nat := 1006769880375713663383013

theorem tailTrace_2941016 : CollatzResearch.WordTrace tailWord_2941016 prefixEnd_2941016 1006769880375713663383013 := by
  unfold tailWord_2941016
  simp only [CollatzResearch.WordTrace]
  refine ⟨53633832956604396194457451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71511777275472528259276601 53633832956604396194457451)
  ·
    refine ⟨80450749434906594291686177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53633832956604396194457451 80450749434906594291686177)
    ·
      refine ⟨60338062076179945718764633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80450749434906594291686177 60338062076179945718764633)
      ·
        refine ⟨45253546557134959289073475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60338062076179945718764633 45253546557134959289073475)
        ·
          refine ⟨67880319835702438933610213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45253546557134959289073475 67880319835702438933610213)
          ·
            refine ⟨12727559969194207300051915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67880319835702438933610213 12727559969194207300051915)
            ·
              refine ⟨19091339953791310950077873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12727559969194207300051915 19091339953791310950077873)
              ·
                refine ⟨14318504965343483212558405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19091339953791310950077873 14318504965343483212558405)
                ·
                  refine ⟨2684719681001903102354701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14318504965343483212558405 2684719681001903102354701)
                  ·
                    refine ⟨1006769880375713663383013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2684719681001903102354701 1006769880375713663383013)
                    ·
                      rfl

theorem cell22_2941016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_2941016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941016 prefixEnd_2941016 := by exact prefixLift 2941016
  have htrace : WordTrace (prefixWord ++ tailWord_2941016) baseStart_2941016 baseEnd_2941016 := by
    simpa [prefixWord, tailWord_2941016, baseEnd_2941016] using wordTrace_append hprefix tailTrace_2941016
  have hstable : (prefixWord ++ tailWord_2941016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941016).length < 2 ^ (prefixWord ++ tailWord_2941016).sum := by decide
  have hdescent : baseEnd_2941016 < baseStart_2941016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941029 : List Nat := [1, 3, 1, 3, 2, 2, 10]
def baseStart_2941029 : Nat := 118140960795 + 2941029 * 2 ^ 59
def prefixEnd_2941029 : Nat := 4983230072969 + 3 ^ 40 * 2941029 * 2
def baseEnd_2941029 : Nat := 37287938168199480103999

theorem tailTrace_2941029 : CollatzResearch.WordTrace tailWord_2941029 prefixEnd_2941029 37287938168199480103999 := by
  unfold tailWord_2941029
  simp only [CollatzResearch.WordTrace]
  refine ⟨107268140062161695609138141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71512093374774463739425427 107268140062161695609138141)
  ·
    refine ⟨40225552523310635853426803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107268140062161695609138141 40225552523310635853426803)
    ·
      refine ⟨60338328784965953780140205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40225552523310635853426803 60338328784965953780140205)
      ·
        refine ⟨22626873294362232667552577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60338328784965953780140205 22626873294362232667552577)
        ·
          refine ⟨16970154970771674500664433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22626873294362232667552577 16970154970771674500664433)
          ·
            refine ⟨12727616228078755875498325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16970154970771674500664433 12727616228078755875498325)
            ·
              refine ⟨37287938168199480103999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12727616228078755875498325 37287938168199480103999)
              ·
                rfl

theorem cell22_2941029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 10].length) (baseStart_2941029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941029 prefixEnd_2941029 := by exact prefixLift 2941029
  have htrace : WordTrace (prefixWord ++ tailWord_2941029) baseStart_2941029 baseEnd_2941029 := by
    simpa [prefixWord, tailWord_2941029, baseEnd_2941029] using wordTrace_append hprefix tailTrace_2941029
  have hstable : (prefixWord ++ tailWord_2941029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941029).length < 2 ^ (prefixWord ++ tailWord_2941029).sum := by decide
  have hdescent : baseEnd_2941029 < baseStart_2941029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941031 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2941031 : Nat := 118140960795 + 2941031 * 2 ^ 59
def prefixEnd_2941031 : Nat := 4983230072969 + 3 ^ 40 * 2941031 * 2
def baseEnd_2941031 : Nat := 1006775015182258624257967

theorem tailTrace_2941031 : CollatzResearch.WordTrace tailWord_2941031 prefixEnd_2941031 1006775015182258624257967 := by
  unfold tailWord_2941031
  simp only [CollatzResearch.WordTrace]
  refine ⟨107268213008154449950710947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71512142005436299967140631 107268213008154449950710947)
  ·
    refine ⟨160902319512231674926066421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107268213008154449950710947 160902319512231674926066421)
    ·
      refine ⟨15084592454271719524318727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160902319512231674926066421 15084592454271719524318727)
      ·
        refine ⟨22626888681407579286478091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15084592454271719524318727 22626888681407579286478091)
        ·
          refine ⟨33940333022111368929717137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22626888681407579286478091 33940333022111368929717137)
          ·
            refine ⟨25455249766583526697287853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33940333022111368929717137 25455249766583526697287853)
            ·
              refine ⟨9545718662468822511482945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25455249766583526697287853 9545718662468822511482945)
              ·
                refine ⟨7159288996851616883612209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9545718662468822511482945 7159288996851616883612209)
                ·
                  refine ⟨5369466747638712662709157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7159288996851616883612209 5369466747638712662709157)
                  ·
                    refine ⟨1006775015182258624257967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369466747638712662709157 1006775015182258624257967)
                    ·
                      rfl

theorem cell22_2941031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2941031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941031 prefixEnd_2941031 := by exact prefixLift 2941031
  have htrace : WordTrace (prefixWord ++ tailWord_2941031) baseStart_2941031 baseEnd_2941031 := by
    simpa [prefixWord, tailWord_2941031, baseEnd_2941031] using wordTrace_append hprefix tailTrace_2941031
  have hstable : (prefixWord ++ tailWord_2941031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941031).length < 2 ^ (prefixWord ++ tailWord_2941031).sum := by decide
  have hdescent : baseEnd_2941031 < baseStart_2941031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941046 : List Nat := [5, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2941046 : Nat := 118140960795 + 2941046 * 2 ^ 59
def prefixEnd_2941046 : Nat := 4983230072969 + 3 ^ 40 * 2941046 * 2
def baseEnd_2941046 : Nat := 111864461109867065014769

theorem tailTrace_2941046 : CollatzResearch.WordTrace tailWord_2941046 prefixEnd_2941046 111864461109867065014769 := by
  unfold tailWord_2941046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704297506443756719531687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71512506735400071675004661 6704297506443756719531687)
  ·
    refine ⟨10056446259665635079297531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6704297506443756719531687 10056446259665635079297531)
    ·
      refine ⟨15084669389498452618946297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10056446259665635079297531 15084669389498452618946297)
      ·
        refine ⟨11313502042123839464209723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15084669389498452618946297 11313502042123839464209723)
        ·
          refine ⟨16970253063185759196314585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11313502042123839464209723 16970253063185759196314585)
          ·
            refine ⟨12727689797389319397235939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16970253063185759196314585 12727689797389319397235939)
            ·
              refine ⟨19091534696083979095853909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12727689797389319397235939 19091534696083979095853909)
              ·
                refine ⟨111864461109867065014769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19091534696083979095853909 111864461109867065014769)
                ·
                  rfl

theorem cell22_2941046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2941046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941046 prefixEnd_2941046 := by exact prefixLift 2941046
  have htrace : WordTrace (prefixWord ++ tailWord_2941046) baseStart_2941046 baseEnd_2941046 := by
    simpa [prefixWord, tailWord_2941046, baseEnd_2941046] using wordTrace_append hprefix tailTrace_2941046
  have hstable : (prefixWord ++ tailWord_2941046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941046).length < 2 ^ (prefixWord ++ tailWord_2941046).sum := by decide
  have hdescent : baseEnd_2941046 < baseStart_2941046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941104 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_2941104 : Nat := 118140960795 + 2941104 * 2 ^ 59
def prefixEnd_2941104 : Nat := 4983230072969 + 3 ^ 40 * 2941104 * 2
def baseEnd_2941104 : Nat := 1006800004574110767182743

theorem tailTrace_2941104 : CollatzResearch.WordTrace tailWord_2941104 prefixEnd_2941104 1006800004574110767182743 := by
  unfold tailWord_2941104
  simp only [CollatzResearch.WordTrace]
  refine ⟨53635437768444991709059183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71513917024593322278745577 53635437768444991709059183)
  ·
    refine ⟨80453156652667487563588775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53635437768444991709059183 80453156652667487563588775)
    ·
      refine ⟨120679734979001231345383163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80453156652667487563588775 120679734979001231345383163)
      ·
        refine ⟨181019602468501847018074745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120679734979001231345383163 181019602468501847018074745)
        ·
          refine ⟨135764701851376385263556059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181019602468501847018074745 135764701851376385263556059)
          ·
            refine ⟨203647052777064577895334089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135764701851376385263556059 203647052777064577895334089)
            ·
              refine ⟨152735289582798433421500567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203647052777064577895334089 152735289582798433421500567)
              ·
                refine ⟨229102934374197650132250851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152735289582798433421500567 229102934374197650132250851)
                ·
                  refine ⟨343654401561296475198376277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229102934374197650132250851 343654401561296475198376277)
                  ·
                    refine ⟨1006800004574110767182743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 343654401561296475198376277 1006800004574110767182743)
                    ·
                      rfl

theorem cell22_2941104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_2941104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941104 prefixEnd_2941104 := by exact prefixLift 2941104
  have htrace : WordTrace (prefixWord ++ tailWord_2941104) baseStart_2941104 baseEnd_2941104 := by
    simpa [prefixWord, tailWord_2941104, baseEnd_2941104] using wordTrace_append hprefix tailTrace_2941104
  have hstable : (prefixWord ++ tailWord_2941104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941104).length < 2 ^ (prefixWord ++ tailWord_2941104).sum := by decide
  have hdescent : baseEnd_2941104 < baseStart_2941104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941106 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_2941106 : Nat := 118140960795 + 2941106 * 2 ^ 59
def prefixEnd_2941106 : Nat := 4983230072969 + 3 ^ 40 * 2941106 * 2
def baseEnd_2941106 : Nat := 1006800689214983428632737

theorem tailTrace_2941106 : CollatzResearch.WordTrace tailWord_2941106 prefixEnd_2941106 1006800689214983428632737 := by
  unfold tailWord_2941106
  simp only [CollatzResearch.WordTrace]
  refine ⟨26817737120720684439922793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71513965655255158506460781 26817737120720684439922793)
  ·
    refine ⟨20113302840540513329942095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26817737120720684439922793 20113302840540513329942095)
    ·
      refine ⟨30169954260810769994913143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20113302840540513329942095 30169954260810769994913143)
      ·
        refine ⟨45254931391216154992369715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30169954260810769994913143 45254931391216154992369715)
        ·
          refine ⟨67882397086824232488554573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45254931391216154992369715 67882397086824232488554573)
          ·
            refine ⟨25455898907559087183207965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67882397086824232488554573 25455898907559087183207965)
            ·
              refine ⟨9545962090334657693702987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25455898907559087183207965 9545962090334657693702987)
              ·
                refine ⟨14318943135501986540554481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9545962090334657693702987 14318943135501986540554481)
                ·
                  refine ⟨10739207351626489905415861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14318943135501986540554481 10739207351626489905415861)
                  ·
                    refine ⟨1006800689214983428632737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10739207351626489905415861 1006800689214983428632737)
                    ·
                      rfl

theorem cell22_2941106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_2941106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941106 prefixEnd_2941106 := by exact prefixLift 2941106
  have htrace : WordTrace (prefixWord ++ tailWord_2941106) baseStart_2941106 baseEnd_2941106 := by
    simpa [prefixWord, tailWord_2941106, baseEnd_2941106] using wordTrace_append hprefix tailTrace_2941106
  have hstable : (prefixWord ++ tailWord_2941106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941106).length < 2 ^ (prefixWord ++ tailWord_2941106).sum := by decide
  have hdescent : baseEnd_2941106 < baseStart_2941106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941142 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2941142 : Nat := 118140960795 + 2941142 * 2 ^ 59
def prefixEnd_2941142 : Nat := 4983230072969 + 3 ^ 40 * 2941142 * 2
def baseEnd_2941142 : Nat := 335604337583563778244209

theorem tailTrace_2941142 : CollatzResearch.WordTrace tailWord_2941142 prefixEnd_2941142 335604337583563778244209 := by
  unfold tailWord_2941142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704516344422019744250105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71514841007168210605334453 6704516344422019744250105)
  ·
    refine ⟨5028387258316514808187579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6704516344422019744250105 5028387258316514808187579)
    ·
      refine ⟨7542580887474772212281369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5028387258316514808187579 7542580887474772212281369)
      ·
        refine ⟨5656935665606079159211027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7542580887474772212281369 5656935665606079159211027)
        ·
          refine ⟨8485403498409118738816541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5656935665606079159211027 8485403498409118738816541)
          ·
            refine ⟨3182026311903419527056203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8485403498409118738816541 3182026311903419527056203)
            ·
              refine ⟨4773039467855129290584305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182026311903419527056203 4773039467855129290584305)
              ·
                refine ⟨3579779600891346967938229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4773039467855129290584305 3579779600891346967938229)
                ·
                  refine ⟨335604337583563778244209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3579779600891346967938229 335604337583563778244209)
                  ·
                    rfl

theorem cell22_2941142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2941142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941142 prefixEnd_2941142 := by exact prefixLift 2941142
  have htrace : WordTrace (prefixWord ++ tailWord_2941142) baseStart_2941142 baseEnd_2941142 := by
    simpa [prefixWord, tailWord_2941142, baseEnd_2941142] using wordTrace_append hprefix tailTrace_2941142
  have hstable : (prefixWord ++ tailWord_2941142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941142).length < 2 ^ (prefixWord ++ tailWord_2941142).sum := by decide
  have hdescent : baseEnd_2941142 < baseStart_2941142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941153 : List Nat := [1, 2, 3, 1, 3, 1, 1, 6, 4]
def baseStart_2941153 : Nat := 118140960795 + 2941153 * 2 ^ 59
def prefixEnd_2941153 : Nat := 4983230072969 + 3 ^ 40 * 2941153 * 2
def baseEnd_2941153 : Nat := 335605592758496990902531

theorem tailTrace_2941153 : CollatzResearch.WordTrace tailWord_2941153 prefixEnd_2941153 335605592758496990902531 := by
  unfold tailWord_2941153
  simp only [CollatzResearch.WordTrace]
  refine ⟨107272662713712464786652113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71515108475808309857768075 107272662713712464786652113)
  ·
    refine ⟨80454497035284348589989085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107272662713712464786652113 80454497035284348589989085)
    ·
      refine ⟨30170436388231630721245907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80454497035284348589989085 30170436388231630721245907)
      ·
        refine ⟨45255654582347446081868861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30170436388231630721245907 45255654582347446081868861)
        ·
          refine ⟨16970870468380292280700823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45255654582347446081868861 16970870468380292280700823)
          ·
            refine ⟨25456305702570438421051235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16970870468380292280700823 25456305702570438421051235)
            ·
              refine ⟨38184458553855657631576853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25456305702570438421051235 38184458553855657631576853)
              ·
                refine ⟨1789896494711983951480165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38184458553855657631576853 1789896494711983951480165)
                ·
                  refine ⟨335605592758496990902531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789896494711983951480165 335605592758496990902531)
                  ·
                    rfl

theorem cell22_2941153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 4].length) (baseStart_2941153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941153 prefixEnd_2941153 := by exact prefixLift 2941153
  have htrace : WordTrace (prefixWord ++ tailWord_2941153) baseStart_2941153 baseEnd_2941153 := by
    simpa [prefixWord, tailWord_2941153, baseEnd_2941153] using wordTrace_append hprefix tailTrace_2941153
  have hstable : (prefixWord ++ tailWord_2941153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941153).length < 2 ^ (prefixWord ++ tailWord_2941153).sum := by decide
  have hdescent : baseEnd_2941153 < baseStart_2941153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941168 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 2, 3]
def baseStart_2941168 : Nat := 118140960795 + 2941168 * 2 ^ 59
def prefixEnd_2941168 : Nat := 4983230072969 + 3 ^ 40 * 2941168 * 2
def baseEnd_2941168 : Nat := 1006821913082035933582547

theorem tailTrace_2941168 : CollatzResearch.WordTrace tailWord_2941168 prefixEnd_2941168 1006821913082035933582547 := by
  unfold tailWord_2941168
  simp only [CollatzResearch.WordTrace]
  refine ⟨53636604904329061174224079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71515473205772081565632105 53636604904329061174224079)
  ·
    refine ⟨80454907356493591761336119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53636604904329061174224079 80454907356493591761336119)
    ·
      refine ⟨120682361034740387642004179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80454907356493591761336119 120682361034740387642004179)
      ·
        refine ⟨181023541552110581463006269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120682361034740387642004179 181023541552110581463006269)
        ·
          refine ⟨67883828082041468048627351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181023541552110581463006269 67883828082041468048627351)
          ·
            refine ⟨101825742123062202072941027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67883828082041468048627351 101825742123062202072941027)
            ·
              refine ⟨152738613184593303109411541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101825742123062202072941027 152738613184593303109411541)
              ·
                refine ⟨3579811246513905541626833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 152738613184593303109411541 3579811246513905541626833)
                ·
                  refine ⟨2684858434885429156220125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3579811246513905541626833 2684858434885429156220125)
                  ·
                    refine ⟨1006821913082035933582547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2684858434885429156220125 1006821913082035933582547)
                    ·
                      rfl

theorem cell22_2941168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_2941168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941168 prefixEnd_2941168 := by exact prefixLift 2941168
  have htrace : WordTrace (prefixWord ++ tailWord_2941168) baseStart_2941168 baseEnd_2941168 := by
    simpa [prefixWord, tailWord_2941168, baseEnd_2941168] using wordTrace_append hprefix tailTrace_2941168
  have hstable : (prefixWord ++ tailWord_2941168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941168).length < 2 ^ (prefixWord ++ tailWord_2941168).sum := by decide
  have hdescent : baseEnd_2941168 < baseStart_2941168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941264 : List Nat := [2, 1, 1, 1, 1, 8, 2, 2, 1, 3]
def baseStart_2941264 : Nat := 118140960795 + 2941264 * 2 ^ 59
def prefixEnd_2941264 : Nat := 4983230072969 + 3 ^ 40 * 2941264 * 2
def baseEnd_2941264 : Nat := 1006854775843923683182253

theorem tailTrace_2941264 : CollatzResearch.WordTrace tailWord_2941264 prefixEnd_2941264 1006854775843923683182253 := by
  unfold tailWord_2941264
  simp only [CollatzResearch.WordTrace]
  refine ⟨53638355608155165371971423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71517807477540220495961897 53638355608155165371971423)
  ·
    refine ⟨80457533412232748057957135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53638355608155165371971423 80457533412232748057957135)
    ·
      refine ⟨120686300118349122086935703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80457533412232748057957135 120686300118349122086935703)
      ·
        refine ⟨181029450177523683130403555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120686300118349122086935703 181029450177523683130403555)
        ·
          refine ⟨271544175266285524695605333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181029450177523683130403555 271544175266285524695605333)
          ·
            refine ⟨3182158303901783492526625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 271544175266285524695605333 3182158303901783492526625)
            ·
              refine ⟨2386618727926337619394969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3182158303901783492526625 2386618727926337619394969)
              ·
                refine ⟨1789964045944753214546227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386618727926337619394969 1789964045944753214546227)
                ·
                  refine ⟨2684946068917129821819341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789964045944753214546227 2684946068917129821819341)
                  ·
                    refine ⟨1006854775843923683182253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2684946068917129821819341 1006854775843923683182253)
                    ·
                      rfl

theorem cell22_2941264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 3].length) (baseStart_2941264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941264 prefixEnd_2941264 := by exact prefixLift 2941264
  have htrace : WordTrace (prefixWord ++ tailWord_2941264) baseStart_2941264 baseEnd_2941264 := by
    simpa [prefixWord, tailWord_2941264, baseEnd_2941264] using wordTrace_append hprefix tailTrace_2941264
  have hstable : (prefixWord ++ tailWord_2941264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941264).length < 2 ^ (prefixWord ++ tailWord_2941264).sum := by decide
  have hdescent : baseEnd_2941264 < baseStart_2941264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941288 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 8]
def baseStart_2941288 : Nat := 118140960795 + 2941288 * 2 ^ 59
def prefixEnd_2941288 : Nat := 4983230072969 + 3 ^ 40 * 2941288 * 2
def baseEnd_2941288 : Nat := 335620997178131873527393

theorem tailTrace_2941288 : CollatzResearch.WordTrace tailWord_2941288 prefixEnd_2941288 335620997178131873527393 := by
  unfold tailWord_2941288
  simp only [CollatzResearch.WordTrace]
  refine ⟨53638793284111691421408259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71518391045482255228544345 53638793284111691421408259)
  ·
    refine ⟨80458189926167537132112389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53638793284111691421408259 80458189926167537132112389)
    ·
      refine ⟨15085910611156413212271073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80458189926167537132112389 15085910611156413212271073)
      ·
        refine ⟨11314432958367309909203305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15085910611156413212271073 11314432958367309909203305)
        ·
          refine ⟨8485824718775482431902479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11314432958367309909203305 8485824718775482431902479)
          ·
            refine ⟨12728737078163223647853719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8485824718775482431902479 12728737078163223647853719)
            ·
              refine ⟨19093105617244835471780579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12728737078163223647853719 19093105617244835471780579)
              ·
                refine ⟨28639658425867253207670869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19093105617244835471780579 28639658425867253207670869)
                ·
                  refine ⟨335620997178131873527393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28639658425867253207670869 335620997178131873527393)
                  ·
                    rfl

theorem cell22_2941288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_2941288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941288 prefixEnd_2941288 := by exact prefixLift 2941288
  have htrace : WordTrace (prefixWord ++ tailWord_2941288) baseStart_2941288 baseEnd_2941288 := by
    simpa [prefixWord, tailWord_2941288, baseEnd_2941288] using wordTrace_append hprefix tailTrace_2941288
  have hstable : (prefixWord ++ tailWord_2941288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941288).length < 2 ^ (prefixWord ++ tailWord_2941288).sum := by decide
  have hdescent : baseEnd_2941288 < baseStart_2941288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941290 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 3, 4]
def baseStart_2941290 : Nat := 118140960795 + 2941290 * 2 ^ 59
def prefixEnd_2941290 : Nat := 4983230072969 + 3 ^ 40 * 2941290 * 2
def baseEnd_2941290 : Nat := 1006863676175268282032173

theorem tailTrace_2941290 : CollatzResearch.WordTrace tailWord_2941290 prefixEnd_2941290 1006863676175268282032173 := by
  unfold tailWord_2941290
  simp only [CollatzResearch.WordTrace]
  refine ⟨26819414878554034296097331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71518439676144091456259549 26819414878554034296097331)
  ·
    refine ⟨40229122317831051444145997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26819414878554034296097331 40229122317831051444145997)
    ·
      refine ⟨15085920869186644291554749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40229122317831051444145997 15085920869186644291554749)
      ·
        refine ⟨5657220325944991609333031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15085920869186644291554749 5657220325944991609333031)
        ·
          refine ⟨8485830488917487413999547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657220325944991609333031 8485830488917487413999547)
          ·
            refine ⟨12728745733376231120999321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8485830488917487413999547 12728745733376231120999321)
            ·
              refine ⟨9546559300032173340749491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12728745733376231120999321 9546559300032173340749491)
              ·
                refine ⟨14319838950048260011124237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9546559300032173340749491 14319838950048260011124237)
                ·
                  refine ⟨5369939606268097504171589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14319838950048260011124237 5369939606268097504171589)
                  ·
                    refine ⟨1006863676175268282032173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369939606268097504171589 1006863676175268282032173)
                    ·
                      rfl

theorem cell22_2941290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_2941290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941290 prefixEnd_2941290 := by exact prefixLift 2941290
  have htrace : WordTrace (prefixWord ++ tailWord_2941290) baseStart_2941290 baseEnd_2941290 := by
    simpa [prefixWord, tailWord_2941290, baseEnd_2941290] using wordTrace_append hprefix tailTrace_2941290
  have hstable : (prefixWord ++ tailWord_2941290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941290).length < 2 ^ (prefixWord ++ tailWord_2941290).sum := by decide
  have hdescent : baseEnd_2941290 < baseStart_2941290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941307 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 1, 4]
def baseStart_2941307 : Nat := 118140960795 + 2941307 * 2 ^ 59
def prefixEnd_2941307 : Nat := 4983230072969 + 3 ^ 40 * 2941307 * 2
def baseEnd_2941307 : Nat := 1006869495622685904357121

theorem tailTrace_2941307 : CollatzResearch.WordTrace tailWord_2941307 prefixEnd_2941307 1006869495622685904357121 := by
  unfold tailWord_2941307
  simp only [CollatzResearch.WordTrace]
  refine ⟨107278279555154549087758175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71518853036769699391838783 107278279555154549087758175)
  ·
    refine ⟨160917419332731823631637263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107278279555154549087758175 160917419332731823631637263)
    ·
      refine ⟨241376128999097735447455895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160917419332731823631637263 241376128999097735447455895)
      ·
        refine ⟨362064193498646603171183843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241376128999097735447455895 362064193498646603171183843)
        ·
          refine ⟨543096290247969904756775765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362064193498646603171183843 543096290247969904756775765)
          ·
            refine ⟨3182204825671698660684233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 543096290247969904756775765 3182204825671698660684233)
            ·
              refine ⟨2386653619253773995513175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3182204825671698660684233 2386653619253773995513175)
              ·
                refine ⟨3579980428880660993269763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386653619253773995513175 3579980428880660993269763)
                ·
                  refine ⟨5369970643320991489904645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579980428880660993269763 5369970643320991489904645)
                  ·
                    refine ⟨1006869495622685904357121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369970643320991489904645 1006869495622685904357121)
                    ·
                      rfl

theorem cell22_2941307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 4].length) (baseStart_2941307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941307 prefixEnd_2941307 := by exact prefixLift 2941307
  have htrace : WordTrace (prefixWord ++ tailWord_2941307) baseStart_2941307 baseEnd_2941307 := by
    simpa [prefixWord, tailWord_2941307, baseEnd_2941307] using wordTrace_append hprefix tailTrace_2941307
  have hstable : (prefixWord ++ tailWord_2941307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941307).length < 2 ^ (prefixWord ++ tailWord_2941307).sum := by decide
  have hdescent : baseEnd_2941307 < baseStart_2941307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941320 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 4, 3]
def baseStart_2941320 : Nat := 118140960795 + 2941320 * 2 ^ 59
def prefixEnd_2941320 : Nat := 4983230072969 + 3 ^ 40 * 2941320 * 2
def baseEnd_2941320 : Nat := 1006873945788358203782081

theorem tailTrace_2941320 : CollatzResearch.WordTrace tailWord_2941320 prefixEnd_2941320 1006873945788358203782081 := by
  unfold tailWord_2941320
  simp only [CollatzResearch.WordTrace]
  refine ⟨53639376852053726153990707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71519169136071634871987609 53639376852053726153990707)
  ·
    refine ⟨80459065278080589230986061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53639376852053726153990707 80459065278080589230986061)
    ·
      refine ⟨30172149479280220961619773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80459065278080589230986061 30172149479280220961619773)
      ·
        refine ⟨11314556054730082860607415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30172149479280220961619773 11314556054730082860607415)
        ·
          refine ⟨16971834082095124290911123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11314556054730082860607415 16971834082095124290911123)
          ·
            refine ⟨25457751123142686436366685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16971834082095124290911123 25457751123142686436366685)
            ·
              refine ⟨9546656671178507413637507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25457751123142686436366685 9546656671178507413637507)
              ·
                refine ⟨14319985006767761120456261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9546656671178507413637507 14319985006767761120456261)
                ·
                  refine ⟨2684997188768955210085549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14319985006767761120456261 2684997188768955210085549)
                  ·
                    refine ⟨1006873945788358203782081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2684997188768955210085549 1006873945788358203782081)
                    ·
                      rfl

theorem cell22_2941320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_2941320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941320 prefixEnd_2941320 := by exact prefixLift 2941320
  have htrace : WordTrace (prefixWord ++ tailWord_2941320) baseStart_2941320 baseEnd_2941320 := by
    simpa [prefixWord, tailWord_2941320, baseEnd_2941320] using wordTrace_append hprefix tailTrace_2941320
  have hstable : (prefixWord ++ tailWord_2941320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941320).length < 2 ^ (prefixWord ++ tailWord_2941320).sum := by decide
  have hdescent : baseEnd_2941320 < baseStart_2941320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941322 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_2941322 : Nat := 118140960795 + 2941322 * 2 ^ 59
def prefixEnd_2941322 : Nat := 4983230072969 + 3 ^ 40 * 2941322 * 2
def baseEnd_2941322 : Nat := 335624876809743621744025

theorem tailTrace_2941322 : CollatzResearch.WordTrace tailWord_2941322 prefixEnd_2941322 335624876809743621744025 := by
  unfold tailWord_2941322
  simp only [CollatzResearch.WordTrace]
  refine ⟨26819706662525051662388555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71519217766733471099702813 26819706662525051662388555)
  ·
    refine ⟨40229559993787577493582833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26819706662525051662388555 40229559993787577493582833)
    ·
      refine ⟨30172169995340683120187125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40229559993787577493582833 30172169995340683120187125)
      ·
        refine ⟨2828640937063189042517543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30172169995340683120187125 2828640937063189042517543)
        ·
          refine ⟨4242961405594783563776315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828640937063189042517543 4242961405594783563776315)
          ·
            refine ⟨6364442108392175345664473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242961405594783563776315 6364442108392175345664473)
            ·
              refine ⟨4773331581294131509248355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6364442108392175345664473 4773331581294131509248355)
              ·
                refine ⟨7159997371941197263872533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773331581294131509248355 7159997371941197263872533)
                ·
                  refine ⟨335624876809743621744025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7159997371941197263872533 335624876809743621744025)
                  ·
                    rfl

theorem cell22_2941322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_2941322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941322 prefixEnd_2941322 := by exact prefixLift 2941322
  have htrace : WordTrace (prefixWord ++ tailWord_2941322) baseStart_2941322 baseEnd_2941322 := by
    simpa [prefixWord, tailWord_2941322, baseEnd_2941322] using wordTrace_append hprefix tailTrace_2941322
  have hstable : (prefixWord ++ tailWord_2941322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941322).length < 2 ^ (prefixWord ++ tailWord_2941322).sum := by decide
  have hdescent : baseEnd_2941322 < baseStart_2941322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941337 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 2, 3]
def baseStart_2941337 : Nat := 118140960795 + 2941337 * 2 ^ 59
def prefixEnd_2941337 : Nat := 4983230072969 + 3 ^ 40 * 2941337 * 2
def baseEnd_2941337 : Nat := 1006879765235775826107029

theorem tailTrace_2941337 : CollatzResearch.WordTrace tailWord_2941337 prefixEnd_2941337 1006879765235775826107029 := by
  unfold tailWord_2941337
  simp only [CollatzResearch.WordTrace]
  refine ⟨107279373745045864211350265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71519582496697242807566843 107279373745045864211350265)
  ·
    refine ⟨80459530308784398158512699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107279373745045864211350265 80459530308784398158512699)
    ·
      refine ⟨120689295463176597237769049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80459530308784398158512699 120689295463176597237769049)
      ·
        refine ⟨90516971597382447928326787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120689295463176597237769049 90516971597382447928326787)
        ·
          refine ⟨135775457396073671892490181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90516971597382447928326787 135775457396073671892490181)
          ·
            refine ⟨25457898261763813479841909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135775457396073671892490181 25457898261763813479841909)
            ·
              refine ⟨2386677962040357513735179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25457898261763813479841909 2386677962040357513735179)
              ·
                refine ⟨3580016943060536270602769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386677962040357513735179 3580016943060536270602769)
                ·
                  refine ⟨2685012707295402202952077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3580016943060536270602769 2685012707295402202952077)
                  ·
                    refine ⟨1006879765235775826107029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2685012707295402202952077 1006879765235775826107029)
                    ·
                      rfl

theorem cell22_2941337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 3].length) (baseStart_2941337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941337 prefixEnd_2941337 := by exact prefixLift 2941337
  have htrace : WordTrace (prefixWord ++ tailWord_2941337) baseStart_2941337 baseEnd_2941337 := by
    simpa [prefixWord, tailWord_2941337, baseEnd_2941337] using wordTrace_append hprefix tailTrace_2941337
  have hstable : (prefixWord ++ tailWord_2941337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941337).length < 2 ^ (prefixWord ++ tailWord_2941337).sum := by decide
  have hdescent : baseEnd_2941337 < baseStart_2941337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941393 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_2941393 : Nat := 118140960795 + 2941393 * 2 ^ 59
def prefixEnd_2941393 : Nat := 4983230072969 + 3 ^ 40 * 2941393 * 2
def baseEnd_2941393 : Nat := 1006898935180210346706857

theorem tailTrace_2941393 : CollatzResearch.WordTrace tailWord_2941393 prefixEnd_2941393 1006898935180210346706857 := by
  unfold tailWord_2941393
  simp only [CollatzResearch.WordTrace]
  refine ⟨107281416232842985775388833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71520944155228657183592555 107281416232842985775388833)
  ·
    refine ⟨80461062174632239331541625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107281416232842985775388833 80461062174632239331541625)
    ·
      refine ⟨60345796630974179498656219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80461062174632239331541625 60345796630974179498656219)
      ·
        refine ⟨90518694946461269247984329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60345796630974179498656219 90518694946461269247984329)
        ·
          refine ⟨67889021209845951935988247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90518694946461269247984329 67889021209845951935988247)
          ·
            refine ⟨101833531814768927903982371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67889021209845951935988247 101833531814768927903982371)
            ·
              refine ⟨152750297722153391855973557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101833531814768927903982371 152750297722153391855973557)
              ·
                refine ⟨14320340411451880486497521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152750297722153391855973557 14320340411451880486497521)
                ·
                  refine ⟨10740255308588910364873141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14320340411451880486497521 10740255308588910364873141)
                  ·
                    refine ⟨1006898935180210346706857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10740255308588910364873141 1006898935180210346706857)
                    ·
                      rfl

theorem cell22_2941393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_2941393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941393 prefixEnd_2941393 := by exact prefixLift 2941393
  have htrace : WordTrace (prefixWord ++ tailWord_2941393) baseStart_2941393 baseEnd_2941393 := by
    simpa [prefixWord, tailWord_2941393, baseEnd_2941393] using wordTrace_append hprefix tailTrace_2941393
  have hstable : (prefixWord ++ tailWord_2941393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941393).length < 2 ^ (prefixWord ++ tailWord_2941393).sum := by decide
  have hdescent : baseEnd_2941393 < baseStart_2941393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941429 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 5]
def baseStart_2941429 : Nat := 118140960795 + 2941429 * 2 ^ 59
def prefixEnd_2941429 : Nat := 4983230072969 + 3 ^ 40 * 2941429 * 2
def baseEnd_2941429 : Nat := 335637086238639417602249

theorem tailTrace_2941429 : CollatzResearch.WordTrace tailWord_2941429 prefixEnd_2941429 335637086238639417602249 := by
  unfold tailWord_2941429
  simp only [CollatzResearch.WordTrace]
  refine ⟨107282729260712563923699341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71521819507141709282466227 107282729260712563923699341)
  ·
    refine ⟨40231023472767211471387253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107282729260712563923699341 40231023472767211471387253)
    ·
      refine ⟨3771658450571926075442555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40231023472767211471387253 3771658450571926075442555)
      ·
        refine ⟨5657487675857889113163833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771658450571926075442555 5657487675857889113163833)
        ·
          refine ⟨4243115756893416834872875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5657487675857889113163833 4243115756893416834872875)
          ·
            refine ⟨6364673635340125252309313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243115756893416834872875 6364673635340125252309313)
            ·
              refine ⟨4773505226505093939231985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6364673635340125252309313 4773505226505093939231985)
              ·
                refine ⟨3580128919878820454423989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4773505226505093939231985 3580128919878820454423989)
                ·
                  refine ⟨335637086238639417602249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3580128919878820454423989 335637086238639417602249)
                  ·
                    rfl

theorem cell22_2941429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_2941429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941429 prefixEnd_2941429 := by exact prefixLift 2941429
  have htrace : WordTrace (prefixWord ++ tailWord_2941429) baseStart_2941429 baseEnd_2941429 := by
    simpa [prefixWord, tailWord_2941429, baseEnd_2941429] using wordTrace_append hprefix tailTrace_2941429
  have hstable : (prefixWord ++ tailWord_2941429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941429).length < 2 ^ (prefixWord ++ tailWord_2941429).sum := by decide
  have hdescent : baseEnd_2941429 < baseStart_2941429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941446 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2941446 : Nat := 118140960795 + 2941446 * 2 ^ 59
def prefixEnd_2941446 : Nat := 4983230072969 + 3 ^ 40 * 2941446 * 2
def baseEnd_2941446 : Nat := 335639026054445291710565

theorem tailTrace_2941446 : CollatzResearch.WordTrace tailWord_2941446 prefixEnd_2941446 335639026054445291710565 := by
  unfold tailWord_2941446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352604665676592994595881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71522232867767317218045461 3352604665676592994595881)
  ·
    refine ⟨2514453499257444745946911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3352604665676592994595881 2514453499257444745946911)
    ·
      refine ⟨3771680248886167118920367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2514453499257444745946911 3771680248886167118920367)
      ·
        refine ⟨5657520373329250678380551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771680248886167118920367 5657520373329250678380551)
        ·
          refine ⟨8486280559993876017570827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657520373329250678380551 8486280559993876017570827)
          ·
            refine ⟨12729420839990814026356241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8486280559993876017570827 12729420839990814026356241)
            ·
              refine ⟨9547065629993110519767181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12729420839990814026356241 9547065629993110519767181)
              ·
                refine ⟨3580149611247416444912693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9547065629993110519767181 3580149611247416444912693)
                ·
                  refine ⟨335639026054445291710565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3580149611247416444912693 335639026054445291710565)
                  ·
                    rfl

theorem cell22_2941446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2941446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941446 prefixEnd_2941446 := by exact prefixLift 2941446
  have htrace : WordTrace (prefixWord ++ tailWord_2941446) baseStart_2941446 baseEnd_2941446 := by
    simpa [prefixWord, tailWord_2941446, baseEnd_2941446] using wordTrace_append hprefix tailTrace_2941446
  have hstable : (prefixWord ++ tailWord_2941446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941446).length < 2 ^ (prefixWord ++ tailWord_2941446).sum := by decide
  have hdescent : baseEnd_2941446 < baseStart_2941446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941483 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 1, 9]
def baseStart_2941483 : Nat := 118140960795 + 2941483 * 2 ^ 59
def prefixEnd_2941483 : Nat := 4983230072969 + 3 ^ 40 * 2941483 * 2
def baseEnd_2941483 : Nat := 1006929744019480111956581

theorem tailTrace_2941483 : CollatzResearch.WordTrace tailWord_2941483 prefixEnd_2941483 1006929744019480111956581 := by
  unfold tailWord_2941483
  simp only [CollatzResearch.WordTrace]
  refine ⟨107284698802516931146165103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71523132535011287430776735 107284698802516931146165103)
  ·
    refine ⟨160927048203775396719247655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107284698802516931146165103 160927048203775396719247655)
    ·
      refine ⟨241390572305663095078871483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160927048203775396719247655 241390572305663095078871483)
      ·
        refine ⟨362085858458494642618307225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241390572305663095078871483 362085858458494642618307225)
        ·
          refine ⟨271564393843870981963730419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362085858458494642618307225 271564393843870981963730419)
          ·
            refine ⟨407346590765806472945595629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271564393843870981963730419 407346590765806472945595629)
            ·
              refine ⟨152754971537177427354598361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407346590765806472945595629 152754971537177427354598361)
              ·
                refine ⟨114566228652883070515948771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152754971537177427354598361 114566228652883070515948771)
                ·
                  refine ⟨171849342979324605773923157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114566228652883070515948771 171849342979324605773923157)
                  ·
                    refine ⟨1006929744019480111956581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 171849342979324605773923157 1006929744019480111956581)
                    ·
                      rfl

theorem cell22_2941483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_2941483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941483 prefixEnd_2941483 := by exact prefixLift 2941483
  have htrace : WordTrace (prefixWord ++ tailWord_2941483) baseStart_2941483 baseEnd_2941483 := by
    simpa [prefixWord, tailWord_2941483, baseEnd_2941483] using wordTrace_append hprefix tailTrace_2941483
  have hstable : (prefixWord ++ tailWord_2941483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941483).length < 2 ^ (prefixWord ++ tailWord_2941483).sum := by decide
  have hdescent : baseEnd_2941483 < baseStart_2941483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941560 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_2941560 : Nat := 118140960795 + 2941560 * 2 ^ 59
def prefixEnd_2941560 : Nat := 4983230072969 + 3 ^ 40 * 2941560 * 2
def baseEnd_2941560 : Nat := 1006956102693077577781345

theorem tailTrace_2941560 : CollatzResearch.WordTrace tailWord_2941560 prefixEnd_2941560 1006956102693077577781345 := by
  unfold tailWord_2941560
  simp only [CollatzResearch.WordTrace]
  refine ⟨53643753611618986648359067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71525004815491982197812089 53643753611618986648359067)
  ·
    refine ⟨80465630417428479972538601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53643753611618986648359067 80465630417428479972538601)
    ·
      refine ⟨60349222813071359979403951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80465630417428479972538601 60349222813071359979403951)
      ·
        refine ⟨90523834219607039969105927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60349222813071359979403951 90523834219607039969105927)
        ·
          refine ⟨135785751329410559953658891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90523834219607039969105927 135785751329410559953658891)
          ·
            refine ⟨203678626994115839930488337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135785751329410559953658891 203678626994115839930488337)
            ·
              refine ⟨152758970245586879947866253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203678626994115839930488337 152758970245586879947866253)
              ·
                refine ⟨57284613842095079980449845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152758970245586879947866253 57284613842095079980449845)
                ·
                  refine ⟨5370432547696413748167173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57284613842095079980449845 5370432547696413748167173)
                  ·
                    refine ⟨1006956102693077577781345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5370432547696413748167173 1006956102693077577781345)
                    ·
                      rfl

theorem cell22_2941560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_2941560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941560 prefixEnd_2941560 := by exact prefixLift 2941560
  have htrace : WordTrace (prefixWord ++ tailWord_2941560) baseStart_2941560 baseEnd_2941560 := by
    simpa [prefixWord, tailWord_2941560, baseEnd_2941560] using wordTrace_append hprefix tailTrace_2941560
  have hstable : (prefixWord ++ tailWord_2941560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941560).length < 2 ^ (prefixWord ++ tailWord_2941560).sum := by decide
  have hdescent : baseEnd_2941560 < baseStart_2941560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941575 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 8]
def baseStart_2941575 : Nat := 118140960795 + 2941575 * 2 ^ 59
def prefixEnd_2941575 : Nat := 4983230072969 + 3 ^ 40 * 2941575 * 2
def baseEnd_2941575 : Nat := 335653745833207512885433

theorem tailTrace_2941575 : CollatzResearch.WordTrace tailWord_2941575 prefixEnd_2941575 335653745833207512885433 := by
  unfold tailWord_2941575
  simp only [CollatzResearch.WordTrace]
  refine ⟨107288054318183630858514179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71525369545455753905676119 107288054318183630858514179)
  ·
    refine ⟨160932081477275446287771269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107288054318183630858514179 160932081477275446287771269)
    ·
      refine ⟨30174765276989146178957113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160932081477275446287771269 30174765276989146178957113)
      ·
        refine ⟨22631073957741859634217835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30174765276989146178957113 22631073957741859634217835)
        ·
          refine ⟨33946610936612789451326753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22631073957741859634217835 33946610936612789451326753)
          ·
            refine ⟨25459958202459592088495065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33946610936612789451326753 25459958202459592088495065)
            ·
              refine ⟨19094968651844694066371299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25459958202459592088495065 19094968651844694066371299)
              ·
                refine ⟨28642452977767041099556949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19094968651844694066371299 28642452977767041099556949)
                ·
                  refine ⟨335653745833207512885433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28642452977767041099556949 335653745833207512885433)
                  ·
                    rfl

theorem cell22_2941575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 8].length) (baseStart_2941575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941575 prefixEnd_2941575 := by exact prefixLift 2941575
  have htrace : WordTrace (prefixWord ++ tailWord_2941575) baseStart_2941575 baseEnd_2941575 := by
    simpa [prefixWord, tailWord_2941575, baseEnd_2941575] using wordTrace_append hprefix tailTrace_2941575
  have hstable : (prefixWord ++ tailWord_2941575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941575).length < 2 ^ (prefixWord ++ tailWord_2941575).sum := by decide
  have hdescent : baseEnd_2941575 < baseStart_2941575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941605 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_2941605 : Nat := 118140960795 + 2941605 * 2 ^ 59
def prefixEnd_2941605 : Nat := 4983230072969 + 3 ^ 40 * 2941605 * 2
def baseEnd_2941605 : Nat := 1006971507112712460406207

theorem tailTrace_2941605 : CollatzResearch.WordTrace tailWord_2941605 prefixEnd_2941605 1006971507112712460406207 := by
  unfold tailWord_2941605
  simp only [CollatzResearch.WordTrace]
  refine ⟨107289148508074945982106269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71526099005383297321404179 107289148508074945982106269)
  ·
    refine ⟨40233430690528104743289851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107289148508074945982106269 40233430690528104743289851)
    ·
      refine ⟨60350146035792157114934777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40233430690528104743289851 60350146035792157114934777)
      ·
        refine ⟨45262609526844117836201083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60350146035792157114934777 45262609526844117836201083)
        ·
          refine ⟨67893914290266176754301625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45262609526844117836201083 67893914290266176754301625)
          ·
            refine ⟨50920435717699632565726219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67893914290266176754301625 50920435717699632565726219)
            ·
              refine ⟨76380653576549448848589329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50920435717699632565726219 76380653576549448848589329)
              ·
                refine ⟨57285490182412086636441997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76380653576549448848589329 57285490182412086636441997)
                ·
                  refine ⟨21482058818404532488665749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57285490182412086636441997 21482058818404532488665749)
                  ·
                    refine ⟨1006971507112712460406207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21482058818404532488665749 1006971507112712460406207)
                    ·
                      rfl

theorem cell22_2941605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_2941605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941605 prefixEnd_2941605 := by exact prefixLift 2941605
  have htrace : WordTrace (prefixWord ++ tailWord_2941605) baseStart_2941605 baseEnd_2941605 := by
    simpa [prefixWord, tailWord_2941605, baseEnd_2941605] using wordTrace_append hprefix tailTrace_2941605
  have hstable : (prefixWord ++ tailWord_2941605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941605).length < 2 ^ (prefixWord ++ tailWord_2941605).sum := by decide
  have hdescent : baseEnd_2941605 < baseStart_2941605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941645 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2941645 : Nat := 118140960795 + 2941645 * 2 ^ 59
def prefixEnd_2941645 : Nat := 4983230072969 + 3 ^ 40 * 2941645 * 2
def baseEnd_2941645 : Nat := 1006985199930165689406085

theorem tailTrace_2941645 : CollatzResearch.WordTrace tailWord_2941645 prefixEnd_2941645 1006985199930165689406085 := by
  unfold tailWord_2941645
  simp only [CollatzResearch.WordTrace]
  refine ⟨107290607427930032813562389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71527071618620021875708259 107290607427930032813562389)
  ·
    refine ⟨5029247223184220288135737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107290607427930032813562389 5029247223184220288135737)
    ·
      refine ⟨3771935417388165216101803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5029247223184220288135737 3771935417388165216101803)
      ·
        refine ⟨5657903126082247824152705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771935417388165216101803 5657903126082247824152705)
        ·
          refine ⟨4243427344561685868114529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5657903126082247824152705 4243427344561685868114529)
          ·
            refine ⟨3182570508421264401085897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4243427344561685868114529 3182570508421264401085897)
            ·
              refine ⟨2386927881315948300814423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3182570508421264401085897 2386927881315948300814423)
              ·
                refine ⟨3580391821973922451221635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386927881315948300814423 3580391821973922451221635)
                ·
                  refine ⟨5370587732960883676832453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3580391821973922451221635 5370587732960883676832453)
                  ·
                    refine ⟨1006985199930165689406085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5370587732960883676832453 1006985199930165689406085)
                    ·
                      rfl

theorem cell22_2941645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2941645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941645 prefixEnd_2941645 := by exact prefixLift 2941645
  have htrace : WordTrace (prefixWord ++ tailWord_2941645) baseStart_2941645 baseEnd_2941645 := by
    simpa [prefixWord, tailWord_2941645, baseEnd_2941645] using wordTrace_append hprefix tailTrace_2941645
  have hstable : (prefixWord ++ tailWord_2941645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941645).length < 2 ^ (prefixWord ++ tailWord_2941645).sum := by decide
  have hdescent : baseEnd_2941645 < baseStart_2941645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941669 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_2941669 : Nat := 118140960795 + 2941669 * 2 ^ 59
def prefixEnd_2941669 : Nat := 4983230072969 + 3 ^ 40 * 2941669 * 2
def baseEnd_2941669 : Nat := 1006993415620637626806011

theorem tailTrace_2941669 : CollatzResearch.WordTrace tailWord_2941669 prefixEnd_2941669 1006993415620637626806011 := by
  unfold tailWord_2941669
  simp only [CollatzResearch.WordTrace]
  refine ⟨107291482779843084912436061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71527655186562056608290707 107291482779843084912436061)
  ·
    refine ⟨40234306042441156842163523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107291482779843084912436061 40234306042441156842163523)
    ·
      refine ⟨60351459063661735263245285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40234306042441156842163523 60351459063661735263245285)
      ·
        refine ⟨11315898574436575361858491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60351459063661735263245285 11315898574436575361858491)
        ·
          refine ⟨16973847861654863042787737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11315898574436575361858491 16973847861654863042787737)
          ·
            refine ⟨12730385896241147282090803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16973847861654863042787737 12730385896241147282090803)
            ·
              refine ⟨19095578844361720923136205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12730385896241147282090803 19095578844361720923136205)
              ·
                refine ⟨7160842066635645346176077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19095578844361720923136205 7160842066635645346176077)
                ·
                  refine ⟨2685315774988367004816029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7160842066635645346176077 2685315774988367004816029)
                  ·
                    refine ⟨1006993415620637626806011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2685315774988367004816029 1006993415620637626806011)
                    ·
                      rfl

theorem cell22_2941669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_2941669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941669 prefixEnd_2941669 := by exact prefixLift 2941669
  have htrace : WordTrace (prefixWord ++ tailWord_2941669) baseStart_2941669 baseEnd_2941669 := by
    simpa [prefixWord, tailWord_2941669, baseEnd_2941669] using wordTrace_append hprefix tailTrace_2941669
  have hstable : (prefixWord ++ tailWord_2941669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941669).length < 2 ^ (prefixWord ++ tailWord_2941669).sum := by decide
  have hdescent : baseEnd_2941669 < baseStart_2941669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941703 : List Nat := [1, 1, 4, 4, 1, 1, 3, 3, 1, 3]
def baseStart_2941703 : Nat := 118140960795 + 2941703 * 2 ^ 59
def prefixEnd_2941703 : Nat := 4983230072969 + 3 ^ 40 * 2941703 * 2
def baseEnd_2941703 : Nat := 1007005054515472871455907

theorem tailTrace_2941703 : CollatzResearch.WordTrace tailWord_2941703 prefixEnd_2941703 1007005054515472871455907 := by
  unfold tailWord_2941703
  simp only [CollatzResearch.WordTrace]
  refine ⟨107292722861719908719173763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71528481907813272479449175 107292722861719908719173763)
  ·
    refine ⟨160939084292579863078760645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107292722861719908719173763 160939084292579863078760645)
    ·
      refine ⟨30176078304858724327267621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160939084292579863078760645 30176078304858724327267621)
      ·
        refine ⟨5658014682161010811362679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30176078304858724327267621 5658014682161010811362679)
        ·
          refine ⟨8487022023241516217044019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658014682161010811362679 8487022023241516217044019)
          ·
            refine ⟨12730533034862274325566029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487022023241516217044019 12730533034862274325566029)
            ·
              refine ⟨4773949888073352872087261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12730533034862274325566029 4773949888073352872087261)
              ·
                refine ⟨1790231208027507327032723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4773949888073352872087261 1790231208027507327032723)
                ·
                  refine ⟨2685346812041260990549085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1790231208027507327032723 2685346812041260990549085)
                  ·
                    refine ⟨1007005054515472871455907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2685346812041260990549085 1007005054515472871455907)
                    ·
                      rfl

theorem cell22_2941703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_2941703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941703 prefixEnd_2941703 := by exact prefixLift 2941703
  have htrace : WordTrace (prefixWord ++ tailWord_2941703) baseStart_2941703 baseEnd_2941703 := by
    simpa [prefixWord, tailWord_2941703, baseEnd_2941703] using wordTrace_append hprefix tailTrace_2941703
  have hstable : (prefixWord ++ tailWord_2941703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941703).length < 2 ^ (prefixWord ++ tailWord_2941703).sum := by decide
  have hdescent : baseEnd_2941703 < baseStart_2941703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941759 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 1, 5]
def baseStart_2941759 : Nat := 118140960795 + 2941759 * 2 ^ 59
def prefixEnd_2941759 : Nat := 4983230072969 + 3 ^ 40 * 2941759 * 2
def baseEnd_2941759 : Nat := 1007024224459907392055735

theorem tailTrace_2941759 : CollatzResearch.WordTrace tailWord_2941759 prefixEnd_2941759 1007024224459907392055735 := by
  unfold tailWord_2941759
  simp only [CollatzResearch.WordTrace]
  refine ⟨107294765349517030283212331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71529843566344686855474887 107294765349517030283212331)
  ·
    refine ⟨160942148024275545424818497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107294765349517030283212331 160942148024275545424818497)
    ·
      refine ⟨120706611018206659068613873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160942148024275545424818497 120706611018206659068613873)
      ·
        refine ⟨90529958263654994301460405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120706611018206659068613873 90529958263654994301460405)
        ·
          refine ⟨8487183587217655715761913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90529958263654994301460405 8487183587217655715761913)
          ·
            refine ⟨6365387690413241786821435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8487183587217655715761913 6365387690413241786821435)
            ·
              refine ⟨9548081535619862680232153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365387690413241786821435 9548081535619862680232153)
              ·
                refine ⟨7161061151714897010174115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9548081535619862680232153 7161061151714897010174115)
                ·
                  refine ⟨10741591727572345515261173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7161061151714897010174115 10741591727572345515261173)
                  ·
                    refine ⟨1007024224459907392055735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10741591727572345515261173 1007024224459907392055735)
                    ·
                      rfl

theorem cell22_2941759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_2941759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941759 prefixEnd_2941759 := by exact prefixLift 2941759
  have htrace : WordTrace (prefixWord ++ tailWord_2941759) baseStart_2941759 baseEnd_2941759 := by
    simpa [prefixWord, tailWord_2941759, baseEnd_2941759] using wordTrace_append hprefix tailTrace_2941759
  have hstable : (prefixWord ++ tailWord_2941759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941759).length < 2 ^ (prefixWord ++ tailWord_2941759).sum := by decide
  have hdescent : baseEnd_2941759 < baseStart_2941759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941772 : List Nat := [2, 2, 1, 3, 3, 11]
def baseStart_2941772 : Nat := 118140960795 + 2941772 * 2 ^ 59
def prefixEnd_2941772 : Nat := 4983230072969 + 3 ^ 40 * 2941772 * 2
def baseEnd_2941772 : Nat := 12432452773155304833095

theorem tailTrace_2941772 : CollatzResearch.WordTrace tailWord_2941772 prefixEnd_2941772 12432452773155304833095 := by
  unfold tailWord_2941772
  simp only [CollatzResearch.WordTrace]
  refine ⟨53647619749234966751717785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71530159665646622335623713 53647619749234966751717785)
  ·
    refine ⟨40235714811926225063788339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53647619749234966751717785 40235714811926225063788339)
    ·
      refine ⟨60353572217889337595682509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40235714811926225063788339 60353572217889337595682509)
      ·
        refine ⟨22632589581708501598380941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60353572217889337595682509 22632589581708501598380941)
        ·
          refine ⟨8487221093140688099392853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22632589581708501598380941 8487221093140688099392853)
          ·
            refine ⟨12432452773155304833095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8487221093140688099392853 12432452773155304833095)
            ·
              rfl

theorem cell22_2941772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 11].length) (baseStart_2941772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941772 prefixEnd_2941772 := by exact prefixLift 2941772
  have htrace : WordTrace (prefixWord ++ tailWord_2941772) baseStart_2941772 baseEnd_2941772 := by
    simpa [prefixWord, tailWord_2941772, baseEnd_2941772] using wordTrace_append hprefix tailTrace_2941772
  have hstable : (prefixWord ++ tailWord_2941772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941772).length < 2 ^ (prefixWord ++ tailWord_2941772).sum := by decide
  have hdescent : baseEnd_2941772 < baseStart_2941772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941881 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_2941881 : Nat := 118140960795 + 2941881 * 2 ^ 59
def prefixEnd_2941881 : Nat := 4983230072969 + 3 ^ 40 * 2941881 * 2
def baseEnd_2941881 : Nat := 1007065987553139740505361

theorem tailTrace_2941881 : CollatzResearch.WordTrace tailWord_2941881 prefixEnd_2941881 1007065987553139740505361 := by
  unfold tailWord_2941881
  simp only [CollatzResearch.WordTrace]
  refine ⟨107299215055075045119153497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71532810036716696746102331 107299215055075045119153497)
  ·
    refine ⟨80474411291306283839365123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107299215055075045119153497 80474411291306283839365123)
    ·
      refine ⟨120711616936959425759047685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80474411291306283839365123 120711616936959425759047685)
      ·
        refine ⟨22633428175679892329821441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120711616936959425759047685 22633428175679892329821441)
        ·
          refine ⟨16975071131759919247366081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22633428175679892329821441 16975071131759919247366081)
          ·
            refine ⟨12731303348819939435524561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16975071131759919247366081 12731303348819939435524561)
            ·
              refine ⟨9548477511614954576643421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12731303348819939435524561 9548477511614954576643421)
              ·
                refine ⟨3580679066855607966241283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9548477511614954576643421 3580679066855607966241283)
                ·
                  refine ⟨5371018600283411949361925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3580679066855607966241283 5371018600283411949361925)
                  ·
                    refine ⟨1007065987553139740505361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5371018600283411949361925 1007065987553139740505361)
                    ·
                      rfl

theorem cell22_2941881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_2941881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941881 prefixEnd_2941881 := by exact prefixLift 2941881
  have htrace : WordTrace (prefixWord ++ tailWord_2941881) baseStart_2941881 baseEnd_2941881 := by
    simpa [prefixWord, tailWord_2941881, baseEnd_2941881] using wordTrace_append hprefix tailTrace_2941881
  have hstable : (prefixWord ++ tailWord_2941881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941881).length < 2 ^ (prefixWord ++ tailWord_2941881).sum := by decide
  have hdescent : baseEnd_2941881 < baseStart_2941881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941940 : List Nat := [2, 6, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2941940 : Nat := 118140960795 + 2941940 * 2 ^ 59
def prefixEnd_2941940 : Nat := 4983230072969 + 3 ^ 40 * 2941940 * 2
def baseEnd_2941940 : Nat := 1007086184458883253280181

theorem tailTrace_2941940 : CollatzResearch.WordTrace tailWord_2941940 prefixEnd_2941940 1007086184458883253280181 := by
  unfold tailWord_2941940
  simp only [CollatzResearch.WordTrace]
  refine ⟨53650683480930649097775637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71534244641240865463700849 53650683480930649097775637)
  ·
    refine ⟨2514875788168624176458233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53650683480930649097775637 2514875788168624176458233)
    ·
      refine ⟨1886156841126468132343675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2514875788168624176458233 1886156841126468132343675)
      ·
        refine ⟨2829235261689702198515513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886156841126468132343675 2829235261689702198515513)
        ·
          refine ⟨2121926446267276648886635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2829235261689702198515513 2121926446267276648886635)
          ·
            refine ⟨3182889669400914973329953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121926446267276648886635 3182889669400914973329953)
            ·
              refine ⟨2387167252050686229997465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3182889669400914973329953 2387167252050686229997465)
              ·
                refine ⟨1790375439038014672498099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2387167252050686229997465 1790375439038014672498099)
                ·
                  refine ⟨2685563158557022008747149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1790375439038014672498099 2685563158557022008747149)
                  ·
                    refine ⟨1007086184458883253280181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2685563158557022008747149 1007086184458883253280181)
                    ·
                      rfl

theorem cell22_2941940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2941940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941940 prefixEnd_2941940 := by exact prefixLift 2941940
  have htrace : WordTrace (prefixWord ++ tailWord_2941940) baseStart_2941940 baseEnd_2941940 := by
    simpa [prefixWord, tailWord_2941940, baseEnd_2941940] using wordTrace_append hprefix tailTrace_2941940
  have hstable : (prefixWord ++ tailWord_2941940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941940).length < 2 ^ (prefixWord ++ tailWord_2941940).sum := by decide
  have hdescent : baseEnd_2941940 < baseStart_2941940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941941 : List Nat := [1, 3, 5, 2, 11]
def baseStart_2941941 : Nat := 118140960795 + 2941941 * 2 ^ 59
def prefixEnd_2941941 : Nat := 4983230072969 + 3 ^ 40 * 2941941 * 2
def baseEnd_2941941 : Nat := 4144388999091850139939

theorem tailTrace_2941941 : CollatzResearch.WordTrace tailWord_2941941 prefixEnd_2941941 4144388999091850139939 := by
  unfold tailWord_2941941
  simp only [CollatzResearch.WordTrace]
  refine ⟨107301403434857675366337677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71534268956571783577558451 107301403434857675366337677)
  ·
    refine ⟨40238026288071628262376629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107301403434857675366337677 40238026288071628262376629)
    ·
      refine ⟨3772314964506715149597809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40238026288071628262376629 3772314964506715149597809)
      ·
        refine ⟨2829236223380036362198357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3772314964506715149597809 2829236223380036362198357)
        ·
          refine ⟨4144388999091850139939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2829236223380036362198357 4144388999091850139939)
          ·
            rfl

theorem cell22_2941941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 11].length) (baseStart_2941941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941941 prefixEnd_2941941 := by exact prefixLift 2941941
  have htrace : WordTrace (prefixWord ++ tailWord_2941941) baseStart_2941941 baseEnd_2941941 := by
    simpa [prefixWord, tailWord_2941941, baseEnd_2941941] using wordTrace_append hprefix tailTrace_2941941
  have hstable : (prefixWord ++ tailWord_2941941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941941).length < 2 ^ (prefixWord ++ tailWord_2941941).sum := by decide
  have hdescent : baseEnd_2941941 < baseStart_2941941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2941973 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_2941973 : Nat := 118140960795 + 2941973 * 2 ^ 59
def prefixEnd_2941973 : Nat := 4983230072969 + 3 ^ 40 * 2941973 * 2
def baseEnd_2941973 : Nat := 1007097481033282167205079

theorem tailTrace_2941973 : CollatzResearch.WordTrace tailWord_2941973 prefixEnd_2941973 1007097481033282167205079 := by
  unfold tailWord_2941973
  simp only [CollatzResearch.WordTrace]
  refine ⟨107302570570741744831502573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71535047047161163221001715 107302570570741744831502573)
  ·
    refine ⟨40238463964028154311813465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107302570570741744831502573 40238463964028154311813465)
    ·
      refine ⟨30178847973021115733860099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40238463964028154311813465 30178847973021115733860099)
      ·
        refine ⟨45268271959531673600790149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30178847973021115733860099 45268271959531673600790149)
        ·
          refine ⟨8487800992412188800148153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45268271959531673600790149 8487800992412188800148153)
          ·
            refine ⟨6365850744309141600111115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8487800992412188800148153 6365850744309141600111115)
            ·
              refine ⟨9548776116463712400166673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6365850744309141600111115 9548776116463712400166673)
              ·
                refine ⟨7161582087347784300125005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9548776116463712400166673 7161582087347784300125005)
                ·
                  refine ⟨2685593282755419112546877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7161582087347784300125005 2685593282755419112546877)
                  ·
                    refine ⟨1007097481033282167205079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2685593282755419112546877 1007097481033282167205079)
                    ·
                      rfl

theorem cell22_2941973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_2941973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2941973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2941973 prefixEnd_2941973 := by exact prefixLift 2941973
  have htrace : WordTrace (prefixWord ++ tailWord_2941973) baseStart_2941973 baseEnd_2941973 := by
    simpa [prefixWord, tailWord_2941973, baseEnd_2941973] using wordTrace_append hprefix tailTrace_2941973
  have hstable : (prefixWord ++ tailWord_2941973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2941973).length < 2 ^ (prefixWord ++ tailWord_2941973).sum := by decide
  have hdescent : baseEnd_2941973 < baseStart_2941973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2941973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942050 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2942050 : Nat := 118140960795 + 2942050 * 2 ^ 59
def prefixEnd_2942050 : Nat := 4983230072969 + 3 ^ 40 * 2942050 * 2
def baseEnd_2942050 : Nat := 1007123839706879633029843

theorem tailTrace_2942050 : CollatzResearch.WordTrace tailWord_2942050 prefixEnd_2942050 1007123839706879633029843 := by
  unfold tailWord_2942050
  simp only [CollatzResearch.WordTrace]
  refine ⟨26826344747865696745513901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71536919327641857988037069 26826344747865696745513901)
  ·
    refine ⟨10059879280449636279567713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26826344747865696745513901 10059879280449636279567713)
    ·
      refine ⟨7544909460337227209675785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10059879280449636279567713 7544909460337227209675785)
      ·
        refine ⟨5658682095252920407256839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7544909460337227209675785 5658682095252920407256839)
        ·
          refine ⟨8488023142879380610885259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658682095252920407256839 8488023142879380610885259)
          ·
            refine ⟨12732034714319070916327889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488023142879380610885259 12732034714319070916327889)
            ·
              refine ⟨9549026035739303187245917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12732034714319070916327889 9549026035739303187245917)
              ·
                refine ⟨3580884763402238695217219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9549026035739303187245917 3580884763402238695217219)
                ·
                  refine ⟨5371327145103358042825829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3580884763402238695217219 5371327145103358042825829)
                  ·
                    refine ⟨1007123839706879633029843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5371327145103358042825829 1007123839706879633029843)
                    ·
                      rfl

theorem cell22_2942050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2942050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942050 prefixEnd_2942050 := by exact prefixLift 2942050
  have htrace : WordTrace (prefixWord ++ tailWord_2942050) baseStart_2942050 baseEnd_2942050 := by
    simpa [prefixWord, tailWord_2942050, baseEnd_2942050] using wordTrace_append hprefix tailTrace_2942050
  have hstable : (prefixWord ++ tailWord_2942050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942050).length < 2 ^ (prefixWord ++ tailWord_2942050).sum := by decide
  have hdescent : baseEnd_2942050 < baseStart_2942050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942063 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 2, 3]
def baseStart_2942063 : Nat := 118140960795 + 2942063 * 2 ^ 59
def prefixEnd_2942063 : Nat := 4983230072969 + 3 ^ 40 * 2942063 * 2
def baseEnd_2942063 : Nat := 1007128289872551932454803

theorem tailTrace_2942063 : CollatzResearch.WordTrace tailWord_2942063 prefixEnd_2942063 1007128289872551932454803 := by
  unfold tailWord_2942063
  simp only [CollatzResearch.WordTrace]
  refine ⟨107305853140415690202278843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71537235426943793468185895 107305853140415690202278843)
  ·
    refine ⟨160958779710623535303418265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107305853140415690202278843 160958779710623535303418265)
    ·
      refine ⟨120719084782967651477563699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160958779710623535303418265 120719084782967651477563699)
      ·
        refine ⟨181078627174451477216345549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120719084782967651477563699 181078627174451477216345549)
        ·
          refine ⟨67904485190419303956129581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 181078627174451477216345549 67904485190419303956129581)
          ·
            refine ⟨25464181946407238983548593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67904485190419303956129581 25464181946407238983548593)
            ·
              refine ⟨19098136459805429237661445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25464181946407238983548593 19098136459805429237661445)
              ·
                refine ⟨3580900586213517982061521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19098136459805429237661445 3580900586213517982061521)
                ·
                  refine ⟨2685675439660138486546141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3580900586213517982061521 2685675439660138486546141)
                  ·
                    refine ⟨1007128289872551932454803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2685675439660138486546141 1007128289872551932454803)
                    ·
                      rfl

theorem cell22_2942063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_2942063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942063 prefixEnd_2942063 := by exact prefixLift 2942063
  have htrace : WordTrace (prefixWord ++ tailWord_2942063) baseStart_2942063 baseEnd_2942063 := by
    simpa [prefixWord, tailWord_2942063, baseEnd_2942063] using wordTrace_append hprefix tailTrace_2942063
  have hstable : (prefixWord ++ tailWord_2942063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942063).length < 2 ^ (prefixWord ++ tailWord_2942063).sum := by decide
  have hdescent : baseEnd_2942063 < baseStart_2942063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942076 : List Nat := [2, 2, 2, 1, 1, 3, 4, 7]
def baseStart_2942076 : Nat := 118140960795 + 2942076 * 2 ^ 59
def prefixEnd_2942076 : Nat := 4983230072969 + 3 ^ 40 * 2942076 * 2
def baseEnd_2942076 : Nat := 111903637782024914653307

theorem tailTrace_2942076 : CollatzResearch.WordTrace tailWord_2942076 prefixEnd_2942076 111903637782024914653307 := by
  unfold tailWord_2942076
  simp only [CollatzResearch.WordTrace]
  refine ⟨53653163644684296711251041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71537551526245728948334721 53653163644684296711251041)
  ·
    refine ⟨40239872733513222533438281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53653163644684296711251041 40239872733513222533438281)
    ·
      refine ⟨30179904550134916900078711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40239872733513222533438281 30179904550134916900078711)
      ·
        refine ⟨45269856825202375350118067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30179904550134916900078711 45269856825202375350118067)
        ·
          refine ⟨67904785237803563025177101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45269856825202375350118067 67904785237803563025177101)
          ·
            refine ⟨25464294464176336134441413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67904785237803563025177101 25464294464176336134441413)
            ·
              refine ⟨4774555212033063025207765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25464294464176336134441413 4774555212033063025207765)
              ·
                refine ⟨111903637782024914653307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4774555212033063025207765 111903637782024914653307)
                ·
                  rfl

theorem cell22_2942076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 7].length) (baseStart_2942076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942076 prefixEnd_2942076 := by exact prefixLift 2942076
  have htrace : WordTrace (prefixWord ++ tailWord_2942076) baseStart_2942076 baseEnd_2942076 := by
    simpa [prefixWord, tailWord_2942076, baseEnd_2942076] using wordTrace_append hprefix tailTrace_2942076
  have hstable : (prefixWord ++ tailWord_2942076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942076).length < 2 ^ (prefixWord ++ tailWord_2942076).sum := by decide
  have hdescent : baseEnd_2942076 < baseStart_2942076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942080 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 2, 3]
def baseStart_2942080 : Nat := 118140960795 + 2942080 * 2 ^ 59
def prefixEnd_2942080 : Nat := 4983230072969 + 3 ^ 40 * 2942080 * 2
def baseEnd_2942080 : Nat := 1007134109319969554779751

theorem tailTrace_2942080 : CollatzResearch.WordTrace tailWord_2942080 prefixEnd_2942080 1007134109319969554779751 := by
  unfold tailWord_2942080
  simp only [CollatzResearch.WordTrace]
  refine ⟨53653236590677051052823847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71537648787569401403765129 53653236590677051052823847)
  ·
    refine ⟨80479854886015576579235771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53653236590677051052823847 80479854886015576579235771)
    ·
      refine ⟨120719782329023364868853657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80479854886015576579235771 120719782329023364868853657)
      ·
        refine ⟨90539836746767523651640243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120719782329023364868853657 90539836746767523651640243)
        ·
          refine ⟨135809755120151285477460365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90539836746767523651640243 135809755120151285477460365)
          ·
            refine ⟨50928658170056732054047637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135809755120151285477460365 50928658170056732054047637)
            ·
              refine ⟨2387280851721409315033483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50928658170056732054047637 2387280851721409315033483)
              ·
                refine ⟨3580921277582113972550225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387280851721409315033483 3580921277582113972550225)
                ·
                  refine ⟨2685690958186585479412669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3580921277582113972550225 2685690958186585479412669)
                  ·
                    refine ⟨1007134109319969554779751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2685690958186585479412669 1007134109319969554779751)
                    ·
                      rfl

theorem cell22_2942080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 3].length) (baseStart_2942080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942080 prefixEnd_2942080 := by exact prefixLift 2942080
  have htrace : WordTrace (prefixWord ++ tailWord_2942080) baseStart_2942080 baseEnd_2942080 := by
    simpa [prefixWord, tailWord_2942080, baseEnd_2942080] using wordTrace_append hprefix tailTrace_2942080
  have hstable : (prefixWord ++ tailWord_2942080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942080).length < 2 ^ (prefixWord ++ tailWord_2942080).sum := by decide
  have hdescent : baseEnd_2942080 < baseStart_2942080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942146 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2942146 : Nat := 118140960795 + 2942146 * 2 ^ 59
def prefixEnd_2942146 : Nat := 4983230072969 + 3 ^ 40 * 2942146 * 2
def baseEnd_2942146 : Nat := 1007156702468767382629549

theorem tailTrace_2942146 : CollatzResearch.WordTrace tailWord_2942146 prefixEnd_2942146 1007156702468767382629549 := by
  unfold tailWord_2942146
  simp only [CollatzResearch.WordTrace]
  refine ⟨26827220099778748844387573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71539253599409996918366861 26827220099778748844387573)
  ·
    refine ⟨2515051884354257704161335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26827220099778748844387573 2515051884354257704161335)
    ·
      refine ⟨3772577826531386556242003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2515051884354257704161335 3772577826531386556242003)
      ·
        refine ⟨5658866739797079834363005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3772577826531386556242003 5658866739797079834363005)
        ·
          refine ⟨2122075027423904937886127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5658866739797079834363005 2122075027423904937886127)
          ·
            refine ⟨3183112541135857406829191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122075027423904937886127 3183112541135857406829191)
            ·
              refine ⟨4774668811703786110243787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183112541135857406829191 4774668811703786110243787)
              ·
                refine ⟨7162003217555679165365681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4774668811703786110243787 7162003217555679165365681)
                ·
                  refine ⟨5371502413166759374024261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162003217555679165365681 5371502413166759374024261)
                  ·
                    refine ⟨1007156702468767382629549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5371502413166759374024261 1007156702468767382629549)
                    ·
                      rfl

theorem cell22_2942146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2942146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942146 prefixEnd_2942146 := by exact prefixLift 2942146
  have htrace : WordTrace (prefixWord ++ tailWord_2942146) baseStart_2942146 baseEnd_2942146 := by
    simpa [prefixWord, tailWord_2942146, baseEnd_2942146] using wordTrace_append hprefix tailTrace_2942146
  have hstable : (prefixWord ++ tailWord_2942146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942146).length < 2 ^ (prefixWord ++ tailWord_2942146).sum := by decide
  have hdescent : baseEnd_2942146 < baseStart_2942146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942213 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_2942213 : Nat := 118140960795 + 2942213 * 2 ^ 59
def prefixEnd_2942213 : Nat := 4983230072969 + 3 ^ 40 * 2942213 * 2
def baseEnd_2942213 : Nat := 1007179637938001541204343

theorem tailTrace_2942213 : CollatzResearch.WordTrace tailWord_2942213 prefixEnd_2942213 1007179637938001541204343 := by
  unfold tailWord_2942213
  simp only [CollatzResearch.WordTrace]
  refine ⟨107311324089872265820239293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71540882726581510546826195 107311324089872265820239293)
  ·
    refine ⟨40241746533702099682589735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107311324089872265820239293 40241746533702099682589735)
    ·
      refine ⟨60362619800553149523884603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40241746533702099682589735 60362619800553149523884603)
      ·
        refine ⟨90543929700829724285826905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60362619800553149523884603 90543929700829724285826905)
        ·
          refine ⟨67907947275622293214370179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90543929700829724285826905 67907947275622293214370179)
          ·
            refine ⟨101861920913433439821555269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67907947275622293214370179 101861920913433439821555269)
            ·
              refine ⟨19099110171268769966541613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101861920913433439821555269 19099110171268769966541613)
              ·
                refine ⟨7162166314225788737453105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19099110171268769966541613 7162166314225788737453105)
                ·
                  refine ⟨5371624735669341553089829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7162166314225788737453105 5371624735669341553089829)
                  ·
                    refine ⟨1007179637938001541204343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5371624735669341553089829 1007179637938001541204343)
                    ·
                      rfl

theorem cell22_2942213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_2942213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942213 prefixEnd_2942213 := by exact prefixLift 2942213
  have htrace : WordTrace (prefixWord ++ tailWord_2942213) baseStart_2942213 baseEnd_2942213 := by
    simpa [prefixWord, tailWord_2942213, baseEnd_2942213] using wordTrace_append hprefix tailTrace_2942213
  have hstable : (prefixWord ++ tailWord_2942213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942213).length < 2 ^ (prefixWord ++ tailWord_2942213).sum := by decide
  have hdescent : baseEnd_2942213 < baseStart_2942213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942288 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_2942288 : Nat := 118140960795 + 2942288 * 2 ^ 59
def prefixEnd_2942288 : Nat := 4983230072969 + 3 ^ 40 * 2942288 * 2
def baseEnd_2942288 : Nat := 1007205311970726345579113

theorem tailTrace_2942288 : CollatzResearch.WordTrace tailWord_2942288 prefixEnd_2942288 1007205311970726345579113 := by
  unfold tailWord_2942288
  simp only [CollatzResearch.WordTrace]
  refine ⟨53657029782300276814609759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71542706376400369086146345 53657029782300276814609759)
  ·
    refine ⟨80485544673450415221914639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53657029782300276814609759 80485544673450415221914639)
    ·
      refine ⟨120728317010175622832871959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80485544673450415221914639 120728317010175622832871959)
      ·
        refine ⟨181092475515263434249307939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120728317010175622832871959 181092475515263434249307939)
        ·
          refine ⟨271638713272895151373961909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181092475515263434249307939 271638713272895151373961909)
          ·
            refine ⟨25466129369333920441308929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 271638713272895151373961909 25466129369333920441308929)
            ·
              refine ⟨19099597027000440330981697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25466129369333920441308929 19099597027000440330981697)
              ·
                refine ⟨14324697770250330248236273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19099597027000440330981697 14324697770250330248236273)
                ·
                  refine ⟨10743523327687747686177205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14324697770250330248236273 10743523327687747686177205)
                  ·
                    refine ⟨1007205311970726345579113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10743523327687747686177205 1007205311970726345579113)
                    ·
                      rfl

theorem cell22_2942288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_2942288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942288 prefixEnd_2942288 := by exact prefixLift 2942288
  have htrace : WordTrace (prefixWord ++ tailWord_2942288) baseStart_2942288 baseEnd_2942288 := by
    simpa [prefixWord, tailWord_2942288, baseEnd_2942288] using wordTrace_append hprefix tailTrace_2942288
  have hstable : (prefixWord ++ tailWord_2942288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942288).length < 2 ^ (prefixWord ++ tailWord_2942288).sum := by decide
  have hdescent : baseEnd_2942288 < baseStart_2942288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942320 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_2942320 : Nat := 118140960795 + 2942320 * 2 ^ 59
def prefixEnd_2942320 : Nat := 4983230072969 + 3 ^ 40 * 2942320 * 2
def baseEnd_2942320 : Nat := 1007216266224688928779015

theorem tailTrace_2942320 : CollatzResearch.WordTrace tailWord_2942320 prefixEnd_2942320 1007216266224688928779015 := by
  unfold tailWord_2942320
  simp only [CollatzResearch.WordTrace]
  refine ⟨53657613350242311547192207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71543484466989748729589609 53657613350242311547192207)
  ·
    refine ⟨80486420025363467320788311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53657613350242311547192207 80486420025363467320788311)
    ·
      refine ⟨120729630038045200981182467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80486420025363467320788311 120729630038045200981182467)
      ·
        refine ⟨181094445057067801471773701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120729630038045200981182467 181094445057067801471773701)
        ·
          refine ⟨33955208448200212775957569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181094445057067801471773701 33955208448200212775957569)
          ·
            refine ⟨25466406336150159581968177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33955208448200212775957569 25466406336150159581968177)
            ·
              refine ⟨19099804752112619686476133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25466406336150159581968177 19099804752112619686476133)
              ·
                refine ⟨3581213391021116191214275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19099804752112619686476133 3581213391021116191214275)
                ·
                  refine ⟨5371820086531674286821413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581213391021116191214275 5371820086531674286821413)
                  ·
                    refine ⟨1007216266224688928779015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5371820086531674286821413 1007216266224688928779015)
                    ·
                      rfl

theorem cell22_2942320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_2942320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942320 prefixEnd_2942320 := by exact prefixLift 2942320
  have htrace : WordTrace (prefixWord ++ tailWord_2942320) baseStart_2942320 baseEnd_2942320 := by
    simpa [prefixWord, tailWord_2942320, baseEnd_2942320] using wordTrace_append hprefix tailTrace_2942320
  have hstable : (prefixWord ++ tailWord_2942320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942320).length < 2 ^ (prefixWord ++ tailWord_2942320).sum := by decide
  have hdescent : baseEnd_2942320 < baseStart_2942320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942365 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2942365 : Nat := 118140960795 + 2942365 * 2 ^ 59
def prefixEnd_2942365 : Nat := 4983230072969 + 3 ^ 40 * 2942365 * 2
def baseEnd_2942365 : Nat := 1007231670644323811403877

theorem tailTrace_2942365 : CollatzResearch.WordTrace tailWord_2942365 prefixEnd_2942365 1007231670644323811403877 := by
  unfold tailWord_2942365
  simp only [CollatzResearch.WordTrace]
  refine ⟨107316867985321595779772549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71544578656881063853181699 107316867985321595779772549)
  ·
    refine ⟨20121912747247799208707353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107316867985321595779772549 20121912747247799208707353)
    ·
      refine ⟨15091434560435849406530515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20121912747247799208707353 15091434560435849406530515)
      ·
        refine ⟨22637151840653774109795773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15091434560435849406530515 22637151840653774109795773)
        ·
          refine ⟨8488931940245165291173415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22637151840653774109795773 8488931940245165291173415)
          ·
            refine ⟨12733397910367747936760123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8488931940245165291173415 12733397910367747936760123)
            ·
              refine ⟨19100096865551621905140185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12733397910367747936760123 19100096865551621905140185)
              ·
                refine ⟨14325072649163716428855139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19100096865551621905140185 14325072649163716428855139)
                ·
                  refine ⟨21487608973745574643282709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14325072649163716428855139 21487608973745574643282709)
                  ·
                    refine ⟨1007231670644323811403877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21487608973745574643282709 1007231670644323811403877)
                    ·
                      rfl

theorem cell22_2942365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2942365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942365 prefixEnd_2942365 := by exact prefixLift 2942365
  have htrace : WordTrace (prefixWord ++ tailWord_2942365) baseStart_2942365 baseEnd_2942365 := by
    simpa [prefixWord, tailWord_2942365, baseEnd_2942365] using wordTrace_append hprefix tailTrace_2942365
  have hstable : (prefixWord ++ tailWord_2942365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942365).length < 2 ^ (prefixWord ++ tailWord_2942365).sum := by decide
  have hdescent : baseEnd_2942365 < baseStart_2942365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942367 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 1, 5]
def baseStart_2942367 : Nat := 118140960795 + 2942367 * 2 ^ 59
def prefixEnd_2942367 : Nat := 4983230072969 + 3 ^ 40 * 2942367 * 2
def baseEnd_2942367 : Nat := 1007232355285196472853871

theorem tailTrace_2942367 : CollatzResearch.WordTrace tailWord_2942367 prefixEnd_2942367 1007232355285196472853871 := by
  unfold tailWord_2942367
  simp only [CollatzResearch.WordTrace]
  refine ⟨107316940931314350121345355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71544627287542900080896903 107316940931314350121345355)
  ·
    refine ⟨160975411396971525182018033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107316940931314350121345355 160975411396971525182018033)
    ·
      refine ⟨120731558547728643886513525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160975411396971525182018033 120731558547728643886513525)
      ·
        refine ⟨11318583613849560364360643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120731558547728643886513525 11318583613849560364360643)
        ·
          refine ⟨16977875420774340546540965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11318583613849560364360643 16977875420774340546540965)
          ·
            refine ⟨3183351641395188852476431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16977875420774340546540965 3183351641395188852476431)
            ·
              refine ⟨4775027462092783278714647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183351641395188852476431 4775027462092783278714647)
              ·
                refine ⟨7162541193139174918071971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775027462092783278714647 7162541193139174918071971)
                ·
                  refine ⟨10743811789708762377107957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7162541193139174918071971 10743811789708762377107957)
                  ·
                    refine ⟨1007232355285196472853871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10743811789708762377107957 1007232355285196472853871)
                    ·
                      rfl

theorem cell22_2942367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_2942367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942367 prefixEnd_2942367 := by exact prefixLift 2942367
  have htrace : WordTrace (prefixWord ++ tailWord_2942367) baseStart_2942367 baseEnd_2942367 := by
    simpa [prefixWord, tailWord_2942367, baseEnd_2942367] using wordTrace_append hprefix tailTrace_2942367
  have hstable : (prefixWord ++ tailWord_2942367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942367).length < 2 ^ (prefixWord ++ tailWord_2942367).sum := by decide
  have hdescent : baseEnd_2942367 < baseStart_2942367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942380 : List Nat := [2, 2, 1, 1, 1, 1, 8, 6]
def baseStart_2942380 : Nat := 118140960795 + 2942380 * 2 ^ 59
def prefixEnd_2942380 : Nat := 4983230072969 + 3 ^ 40 * 2942380 * 2
def baseEnd_2942380 : Nat := 111915200605652085808759

theorem tailTrace_2942380 : CollatzResearch.WordTrace tailWord_2942380 prefixEnd_2942380 111915200605652085808759 := by
  unfold tailWord_2942380
  simp only [CollatzResearch.WordTrace]
  refine ⟨53658707540133626670784297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71544943386844835561045729 53658707540133626670784297)
  ·
    refine ⟨40244030655100220003088223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53658707540133626670784297 40244030655100220003088223)
    ·
      refine ⟨60366045982650330004632335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40244030655100220003088223 60366045982650330004632335)
      ·
        refine ⟨90549068973975495006948503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60366045982650330004632335 90549068973975495006948503)
        ·
          refine ⟨135823603460963242510422755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90549068973975495006948503 135823603460963242510422755)
          ·
            refine ⟨203735405191444863765634133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135823603460963242510422755 203735405191444863765634133)
            ·
              refine ⟨2387524279587244497253525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 203735405191444863765634133 2387524279587244497253525)
              ·
                refine ⟨111915200605652085808759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2387524279587244497253525 111915200605652085808759)
                ·
                  rfl

theorem cell22_2942380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 6].length) (baseStart_2942380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942380 prefixEnd_2942380 := by exact prefixLift 2942380
  have htrace : WordTrace (prefixWord ++ tailWord_2942380) baseStart_2942380 baseEnd_2942380 := by
    simpa [prefixWord, tailWord_2942380, baseEnd_2942380] using wordTrace_append hprefix tailTrace_2942380
  have hstable : (prefixWord ++ tailWord_2942380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942380).length < 2 ^ (prefixWord ++ tailWord_2942380).sum := by decide
  have hdescent : baseEnd_2942380 < baseStart_2942380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942515 : List Nat := [1, 1, 1, 2, 4, 4, 9]
def baseStart_2942515 : Nat := 118140960795 + 2942515 * 2 ^ 59
def prefixEnd_2942515 : Nat := 4983230072969 + 3 ^ 40 * 2942515 * 2
def baseEnd_2942515 : Nat := 37306778470732348894571

theorem tailTrace_2942515 : CollatzResearch.WordTrace tailWord_2942515 prefixEnd_2942515 37306778470732348894571 := by
  unfold tailWord_2942515
  simp only [CollatzResearch.WordTrace]
  refine ⟨107322338934778171397732999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71548225956518780931821999 107322338934778171397732999)
  ·
    refine ⟨160983508402167257096599499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107322338934778171397732999 160983508402167257096599499)
    ·
      refine ⟨241475262603250885644899249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160983508402167257096599499 241475262603250885644899249)
      ·
        refine ⟨181106446952438164233674437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241475262603250885644899249 181106446952438164233674437)
        ·
          refine ⟨33957458803582155793813957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 181106446952438164233674437 33957458803582155793813957)
          ·
            refine ⟨6367023525671654211340117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33957458803582155793813957 6367023525671654211340117)
            ·
              refine ⟨37306778470732348894571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6367023525671654211340117 37306778470732348894571)
              ·
                rfl

theorem cell22_2942515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 9].length) (baseStart_2942515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942515 prefixEnd_2942515 := by exact prefixLift 2942515
  have htrace : WordTrace (prefixWord ++ tailWord_2942515) baseStart_2942515 baseEnd_2942515 := by
    simpa [prefixWord, tailWord_2942515, baseEnd_2942515] using wordTrace_append hprefix tailTrace_2942515
  have hstable : (prefixWord ++ tailWord_2942515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942515).length < 2 ^ (prefixWord ++ tailWord_2942515).sum := by decide
  have hdescent : baseEnd_2942515 < baseStart_2942515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942519 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 2, 3]
def baseStart_2942519 : Nat := 118140960795 + 2942519 * 2 ^ 59
def prefixEnd_2942519 : Nat := 4983230072969 + 3 ^ 40 * 2942519 * 2
def baseEnd_2942519 : Nat := 1007284387991518743053405

theorem tailTrace_2942519 : CollatzResearch.WordTrace tailWord_2942519 prefixEnd_2942519 1007284387991518743053405 := by
  unfold tailWord_2942519
  simp only [CollatzResearch.WordTrace]
  refine ⟨107322484826763680080878611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71548323217842453387252407 107322484826763680080878611)
  ·
    refine ⟨160983727240145520121317917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107322484826763680080878611 160983727240145520121317917)
    ·
      refine ⟨60368897715054570045494219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160983727240145520121317917 60368897715054570045494219)
      ·
        refine ⟨90553346572581855068241329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60368897715054570045494219 90553346572581855068241329)
        ·
          refine ⟨67915009929436391301180997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90553346572581855068241329 67915009929436391301180997)
          ·
            refine ⟨12734064361769323368971437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67915009929436391301180997 12734064361769323368971437)
            ·
              refine ⟨4775274135663496263364289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12734064361769323368971437 4775274135663496263364289)
              ·
                refine ⟨3581455601747622197523217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4775274135663496263364289 3581455601747622197523217)
                ·
                  refine ⟨2686091701310716648142413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3581455601747622197523217 2686091701310716648142413)
                  ·
                    refine ⟨1007284387991518743053405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2686091701310716648142413 1007284387991518743053405)
                    ·
                      rfl

theorem cell22_2942519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_2942519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942519 prefixEnd_2942519 := by exact prefixLift 2942519
  have htrace : WordTrace (prefixWord ++ tailWord_2942519) baseStart_2942519 baseEnd_2942519 := by
    simpa [prefixWord, tailWord_2942519, baseEnd_2942519] using wordTrace_append hprefix tailTrace_2942519
  have hstable : (prefixWord ++ tailWord_2942519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942519).length < 2 ^ (prefixWord ++ tailWord_2942519).sum := by decide
  have hdescent : baseEnd_2942519 < baseStart_2942519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942581 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_2942581 : Nat := 118140960795 + 2942581 * 2 ^ 59
def prefixEnd_2942581 : Nat := 4983230072969 + 3 ^ 40 * 2942581 * 2
def baseEnd_2942581 : Nat := 1007305611858571248003215

theorem tailTrace_2942581 : CollatzResearch.WordTrace tailWord_2942581 prefixEnd_2942581 1007305611858571248003215 := by
  unfold tailWord_2942581
  simp only [CollatzResearch.WordTrace]
  refine ⟨107324746152539064669635597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71549830768359376446423731 107324746152539064669635597)
  ·
    refine ⟨40246779807202149251113349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107324746152539064669635597 40246779807202149251113349)
    ·
      refine ⟨7546271213850402984583753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40246779807202149251113349 7546271213850402984583753)
      ·
        refine ⟨5659703410387802238437815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7546271213850402984583753 5659703410387802238437815)
        ·
          refine ⟨8489555115581703357656723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5659703410387802238437815 8489555115581703357656723)
          ·
            refine ⟨12734332673372555036485085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8489555115581703357656723 12734332673372555036485085)
            ·
              refine ⟨4775374752514708138681907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12734332673372555036485085 4775374752514708138681907)
              ·
                refine ⟨7163062128772062208022861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775374752514708138681907 7163062128772062208022861)
                ·
                  refine ⟨2686148298289523328008573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7163062128772062208022861 2686148298289523328008573)
                  ·
                    refine ⟨1007305611858571248003215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2686148298289523328008573 1007305611858571248003215)
                    ·
                      rfl

theorem cell22_2942581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_2942581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942581 prefixEnd_2942581 := by exact prefixLift 2942581
  have htrace : WordTrace (prefixWord ++ tailWord_2942581) baseStart_2942581 baseEnd_2942581 := by
    simpa [prefixWord, tailWord_2942581, baseEnd_2942581] using wordTrace_append hprefix tailTrace_2942581
  have hstable : (prefixWord ++ tailWord_2942581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942581).length < 2 ^ (prefixWord ++ tailWord_2942581).sum := by decide
  have hdescent : baseEnd_2942581 < baseStart_2942581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942632 : List Nat := [2, 1, 7, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2942632 : Nat := 118140960795 + 2942632 * 2 ^ 59
def prefixEnd_2942632 : Nat := 4983230072969 + 3 ^ 40 * 2942632 * 2
def baseEnd_2942632 : Nat := 1007323070200824114978059

theorem tailTrace_2942632 : CollatzResearch.WordTrace tailWord_2942632 prefixEnd_2942632 1007323070200824114978059 := by
  unfold tailWord_2942632
  simp only [CollatzResearch.WordTrace]
  refine ⟨53663303137677150189871075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71551070850236200253161433 53663303137677150189871075)
  ·
    refine ⟨80494954706515725284806613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53663303137677150189871075 80494954706515725284806613)
    ·
      refine ⟨1886600500933962311362655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 80494954706515725284806613 1886600500933962311362655)
      ·
        refine ⟨2829900751400943467043983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886600500933962311362655 2829900751400943467043983)
        ·
          refine ⟨4244851127101415200565975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829900751400943467043983 4244851127101415200565975)
          ·
            refine ⟨6367276690652122800848963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4244851127101415200565975 6367276690652122800848963)
            ·
              refine ⟨9550915035978184201273445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6367276690652122800848963 9550915035978184201273445)
              ·
                refine ⟨1790796569245909537738771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9550915035978184201273445 1790796569245909537738771)
                ·
                  refine ⟨2686194853868864306608157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1790796569245909537738771 2686194853868864306608157)
                  ·
                    refine ⟨1007323070200824114978059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2686194853868864306608157 1007323070200824114978059)
                    ·
                      rfl

theorem cell22_2942632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2942632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942632 prefixEnd_2942632 := by exact prefixLift 2942632
  have htrace : WordTrace (prefixWord ++ tailWord_2942632) baseStart_2942632 baseEnd_2942632 := by
    simpa [prefixWord, tailWord_2942632, baseEnd_2942632] using wordTrace_append hprefix tailTrace_2942632
  have hstable : (prefixWord ++ tailWord_2942632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942632).length < 2 ^ (prefixWord ++ tailWord_2942632).sum := by decide
  have hdescent : baseEnd_2942632 < baseStart_2942632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942639 : List Nat := [1, 1, 2, 1, 2, 4, 3, 4, 4]
def baseStart_2942639 : Nat := 118140960795 + 2942639 * 2 ^ 59
def prefixEnd_2942639 : Nat := 4983230072969 + 3 ^ 40 * 2942639 * 2
def baseEnd_2942639 : Nat := 335775155481292810017679

theorem tailTrace_2942639 : CollatzResearch.WordTrace tailWord_2942639 prefixEnd_2942639 335775155481292810017679 := by
  unfold tailWord_2942639
  simp only [CollatzResearch.WordTrace]
  refine ⟨107326861586328940575246971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71551241057552627050164647 107326861586328940575246971)
  ·
    refine ⟨160990292379493410862870457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107326861586328940575246971 160990292379493410862870457)
    ·
      refine ⟨120742719284620058147152843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160990292379493410862870457 120742719284620058147152843)
      ·
        refine ⟨181114078926930087220729265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120742719284620058147152843 181114078926930087220729265)
        ·
          refine ⟨135835559195197565415546949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181114078926930087220729265 135835559195197565415546949)
          ·
            refine ⟨25469167349099543515415053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135835559195197565415546949 25469167349099543515415053)
            ·
              refine ⟨9550937755912328818280645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25469167349099543515415053 9550937755912328818280645)
              ·
                refine ⟨1790800829233561653427621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9550937755912328818280645 1790800829233561653427621)
                ·
                  refine ⟨335775155481292810017679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1790800829233561653427621 335775155481292810017679)
                  ·
                    rfl

theorem cell22_2942639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 4].length) (baseStart_2942639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942639 prefixEnd_2942639 := by exact prefixLift 2942639
  have htrace : WordTrace (prefixWord ++ tailWord_2942639) baseStart_2942639 baseEnd_2942639 := by
    simpa [prefixWord, tailWord_2942639, baseEnd_2942639] using wordTrace_append hprefix tailTrace_2942639
  have hstable : (prefixWord ++ tailWord_2942639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942639).length < 2 ^ (prefixWord ++ tailWord_2942639).sum := by decide
  have hdescent : baseEnd_2942639 < baseStart_2942639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942654 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2942654 : Nat := 118140960795 + 2942654 * 2 ^ 59
def prefixEnd_2942654 : Nat := 4983230072969 + 3 ^ 40 * 2942654 * 2
def baseEnd_2942654 : Nat := 1007330601250423390927991

theorem tailTrace_2942654 : CollatzResearch.WordTrace tailWord_2942654 prefixEnd_2942654 1007330601250423390927991 := by
  unfold tailWord_2942654
  simp only [CollatzResearch.WordTrace]
  refine ⟨13415926085159324767130377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71551605787516398758028677 13415926085159324767130377)
  ·
    refine ⟨10061944563869493575347783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13415926085159324767130377 10061944563869493575347783)
    ·
      refine ⟨15092916845804240363021675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10061944563869493575347783 15092916845804240363021675)
      ·
        refine ⟨22639375268706360544532513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15092916845804240363021675 22639375268706360544532513)
        ·
          refine ⟨16979531451529770408399385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22639375268706360544532513 16979531451529770408399385)
          ·
            refine ⟨12734648588647327806299539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16979531451529770408399385 12734648588647327806299539)
            ·
              refine ⟨19101972882970991709449309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12734648588647327806299539 19101972882970991709449309)
              ·
                refine ⟨7163239831114121891043491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19101972882970991709449309 7163239831114121891043491)
                ·
                  refine ⟨10744859746671182836565237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7163239831114121891043491 10744859746671182836565237)
                  ·
                    refine ⟨1007330601250423390927991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10744859746671182836565237 1007330601250423390927991)
                    ·
                      rfl

theorem cell22_2942654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2942654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942654 prefixEnd_2942654 := by exact prefixLift 2942654
  have htrace : WordTrace (prefixWord ++ tailWord_2942654) baseStart_2942654 baseEnd_2942654 := by
    simpa [prefixWord, tailWord_2942654, baseEnd_2942654] using wordTrace_append hprefix tailTrace_2942654
  have hstable : (prefixWord ++ tailWord_2942654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942654).length < 2 ^ (prefixWord ++ tailWord_2942654).sum := by decide
  have hdescent : baseEnd_2942654 < baseStart_2942654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942699 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 3, 3]
def baseStart_2942699 : Nat := 118140960795 + 2942699 * 2 ^ 59
def prefixEnd_2942699 : Nat := 4983230072969 + 3 ^ 40 * 2942699 * 2
def baseEnd_2942699 : Nat := 1007346005670058273552853

theorem tailTrace_2942699 : CollatzResearch.WordTrace tailWord_2942699 prefixEnd_2942699 1007346005670058273552853 := by
  unfold tailWord_2942699
  simp only [CollatzResearch.WordTrace]
  refine ⟨107329049966111570822431151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71552699977407713881620767 107329049966111570822431151)
  ·
    refine ⟨160993574949167356233646727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107329049966111570822431151 160993574949167356233646727)
    ·
      refine ⟨241490362423751034350470091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160993574949167356233646727 241490362423751034350470091)
      ·
        refine ⟨362235543635626551525705137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241490362423751034350470091 362235543635626551525705137)
        ·
          refine ⟨271676657726719913644278853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 362235543635626551525705137 271676657726719913644278853)
          ·
            refine ⟨50939373323759983808302285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271676657726719913644278853 50939373323759983808302285)
            ·
              refine ⟨19102264996409993928113357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50939373323759983808302285 19102264996409993928113357)
              ·
                refine ⟨7163349373653747723042509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19102264996409993928113357 7163349373653747723042509)
                ·
                  refine ⟨2686256015120155396140941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7163349373653747723042509 2686256015120155396140941)
                  ·
                    refine ⟨1007346005670058273552853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2686256015120155396140941 1007346005670058273552853)
                    ·
                      rfl

theorem cell22_2942699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 3].length) (baseStart_2942699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942699 prefixEnd_2942699 := by exact prefixLift 2942699
  have htrace : WordTrace (prefixWord ++ tailWord_2942699) baseStart_2942699 baseEnd_2942699 := by
    simpa [prefixWord, tailWord_2942699, baseEnd_2942699] using wordTrace_append hprefix tailTrace_2942699
  have hstable : (prefixWord ++ tailWord_2942699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942699).length < 2 ^ (prefixWord ++ tailWord_2942699).sum := by decide
  have hdescent : baseEnd_2942699 < baseStart_2942699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942718 : List Nat := [4, 2, 2, 1, 3, 2, 2, 6]
def baseStart_2942718 : Nat := 118140960795 + 2942718 * 2 ^ 59
def prefixEnd_2942718 : Nat := 4983230072969 + 3 ^ 40 * 2942718 * 2
def baseEnd_2942718 : Nat := 111928056639816506369755

theorem tailTrace_2942718 : CollatzResearch.WordTrace tailWord_2942718 prefixEnd_2942718 111928056639816506369755 := by
  unfold tailWord_2942718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13416217869130342133421601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71553161968695158044915205 13416217869130342133421601)
  ·
    refine ⟨10062163401847756600066201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13416217869130342133421601 10062163401847756600066201)
    ·
      refine ⟨7546622551385817450049651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10062163401847756600066201 7546622551385817450049651)
      ·
        refine ⟨11319933827078726175074477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7546622551385817450049651 11319933827078726175074477)
        ·
          refine ⟨4244975185154522315652929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11319933827078726175074477 4244975185154522315652929)
          ·
            refine ⟨3183731388865891736739697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4244975185154522315652929 3183731388865891736739697)
            ·
              refine ⟨2387798541649418802554773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3183731388865891736739697 2387798541649418802554773)
              ·
                refine ⟨111928056639816506369755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2387798541649418802554773 111928056639816506369755)
                ·
                  rfl

theorem cell22_2942718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_2942718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942718 prefixEnd_2942718 := by exact prefixLift 2942718
  have htrace : WordTrace (prefixWord ++ tailWord_2942718) baseStart_2942718 baseEnd_2942718 := by
    simpa [prefixWord, tailWord_2942718, baseEnd_2942718] using wordTrace_append hprefix tailTrace_2942718
  have hstable : (prefixWord ++ tailWord_2942718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942718).length < 2 ^ (prefixWord ++ tailWord_2942718).sum := by decide
  have hdescent : baseEnd_2942718 < baseStart_2942718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942776 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_2942776 : Nat := 118140960795 + 2942776 * 2 ^ 59
def prefixEnd_2942776 : Nat := 4983230072969 + 3 ^ 40 * 2942776 * 2
def baseEnd_2942776 : Nat := 1007372364343655739377617

theorem tailTrace_2942776 : CollatzResearch.WordTrace tailWord_2942776 prefixEnd_2942776 1007372364343655739377617 := by
  unfold tailWord_2942776
  simp only [CollatzResearch.WordTrace]
  refine ⟨53665929193416306486492091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71554572257888408648656121 53665929193416306486492091)
  ·
    refine ⟨80498893790124459729738137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53665929193416306486492091 80498893790124459729738137)
    ·
      refine ⟨60374170342593344797303603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80498893790124459729738137 60374170342593344797303603)
      ·
        refine ⟨90561255513890017195955405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60374170342593344797303603 90561255513890017195955405)
        ·
          refine ⟨33960470817708756448483277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90561255513890017195955405 33960470817708756448483277)
          ·
            refine ⟨12735176556640783668181229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33960470817708756448483277 12735176556640783668181229)
            ·
              refine ⟨4775691208740293875567961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12735176556640783668181229 4775691208740293875567961)
              ·
                refine ⟨3581768406555220406675971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4775691208740293875567961 3581768406555220406675971)
                ·
                  refine ⟨5372652609832830610013957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581768406555220406675971 5372652609832830610013957)
                  ·
                    refine ⟨1007372364343655739377617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5372652609832830610013957 1007372364343655739377617)
                    ·
                      rfl

theorem cell22_2942776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_2942776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942776 prefixEnd_2942776 := by exact prefixLift 2942776
  have htrace : WordTrace (prefixWord ++ tailWord_2942776) baseStart_2942776 baseEnd_2942776 := by
    simpa [prefixWord, tailWord_2942776, baseEnd_2942776] using wordTrace_append hprefix tailTrace_2942776
  have hstable : (prefixWord ++ tailWord_2942776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942776).length < 2 ^ (prefixWord ++ tailWord_2942776).sum := by decide
  have hdescent : baseEnd_2942776 < baseStart_2942776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942789 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_2942789 : Nat := 118140960795 + 2942789 * 2 ^ 59
def prefixEnd_2942789 : Nat := 4983230072969 + 3 ^ 40 * 2942789 * 2
def baseEnd_2942789 : Nat := 1007376814509328038802577

theorem tailTrace_2942789 : CollatzResearch.WordTrace tailWord_2942789 prefixEnd_2942789 1007376814509328038802577 := by
  unfold tailWord_2942789
  simp only [CollatzResearch.WordTrace]
  refine ⟨107332332535785516193207421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71554888357190344128804947 107332332535785516193207421)
  ·
    refine ⟨40249624700919568572452783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107332332535785516193207421 40249624700919568572452783)
    ·
      refine ⟨60374437051379352858679175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40249624700919568572452783 60374437051379352858679175)
      ·
        refine ⟨90561655577069029288018763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60374437051379352858679175 90561655577069029288018763)
        ·
          refine ⟨135842483365603543932028145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90561655577069029288018763 135842483365603543932028145)
          ·
            refine ⟨101881862524202657949021109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135842483365603543932028145 101881862524202657949021109)
            ·
              refine ⟨9551424611643999182720729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101881862524202657949021109 9551424611643999182720729)
              ·
                refine ⟨7163568458732999387040547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9551424611643999182720729 7163568458732999387040547)
                ·
                  refine ⟨10745352688099499080560821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7163568458732999387040547 10745352688099499080560821)
                  ·
                    refine ⟨1007376814509328038802577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10745352688099499080560821 1007376814509328038802577)
                    ·
                      rfl

theorem cell22_2942789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_2942789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942789 prefixEnd_2942789 := by exact prefixLift 2942789
  have htrace : WordTrace (prefixWord ++ tailWord_2942789) baseStart_2942789 baseEnd_2942789 := by
    simpa [prefixWord, tailWord_2942789, baseEnd_2942789] using wordTrace_append hprefix tailTrace_2942789
  have hstable : (prefixWord ++ tailWord_2942789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942789).length < 2 ^ (prefixWord ++ tailWord_2942789).sum := by decide
  have hdescent : baseEnd_2942789 < baseStart_2942789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942838 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_2942838 : Nat := 118140960795 + 2942838 * 2 ^ 59
def prefixEnd_2942838 : Nat := 4983230072969 + 3 ^ 40 * 2942838 * 2
def baseEnd_2942838 : Nat := 1007393588210708244327427

theorem tailTrace_2942838 : CollatzResearch.WordTrace tailWord_2942838 prefixEnd_2942838 1007393588210708244327427 := by
  unfold tailWord_2942838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708382482037999847608823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71556079808405331707827445 6708382482037999847608823)
  ·
    refine ⟨10062573723056999771413235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6708382482037999847608823 10062573723056999771413235)
    ·
      refine ⟨15093860584585499657119853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10062573723056999771413235 15093860584585499657119853)
      ·
        refine ⟨5660197719219562371419945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15093860584585499657119853 5660197719219562371419945)
        ·
          refine ⟨4245148289414671778564959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5660197719219562371419945 4245148289414671778564959)
          ·
            refine ⟨6367722434122007667847439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245148289414671778564959 6367722434122007667847439)
            ·
              refine ⟨9551583651183011501771159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6367722434122007667847439 9551583651183011501771159)
              ·
                refine ⟨14327375476774517252656739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9551583651183011501771159 14327375476774517252656739)
                ·
                  refine ⟨21491063215161775878985109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14327375476774517252656739 21491063215161775878985109)
                  ·
                    refine ⟨1007393588210708244327427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21491063215161775878985109 1007393588210708244327427)
                    ·
                      rfl

theorem cell22_2942838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_2942838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942838 prefixEnd_2942838 := by exact prefixLift 2942838
  have htrace : WordTrace (prefixWord ++ tailWord_2942838) baseStart_2942838 baseEnd_2942838 := by
    simpa [prefixWord, tailWord_2942838, baseEnd_2942838] using wordTrace_append hprefix tailTrace_2942838
  have hstable : (prefixWord ++ tailWord_2942838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942838).length < 2 ^ (prefixWord ++ tailWord_2942838).sum := by decide
  have hdescent : baseEnd_2942838 < baseStart_2942838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942868 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2942868 : Nat := 118140960795 + 2942868 * 2 ^ 59
def prefixEnd_2942868 : Nat := 4983230072969 + 3 ^ 40 * 2942868 * 2
def baseEnd_2942868 : Nat := 1007403857823798166077335

theorem tailTrace_2942868 : CollatzResearch.WordTrace tailWord_2942868 prefixEnd_2942868 1007403857823798166077335 := by
  unfold tailWord_2942868
  simp only [CollatzResearch.WordTrace]
  refine ⟨53667606951249656342666629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71556809268332875123555505 53667606951249656342666629)
  ·
    refine ⟨10062676303359310564249993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53667606951249656342666629 10062676303359310564249993)
    ·
      refine ⟨7547007227519482923187495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10062676303359310564249993 7547007227519482923187495)
      ·
        refine ⟨11320510841279224384781243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7547007227519482923187495 11320510841279224384781243)
        ·
          refine ⟨16980766261918836577171865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11320510841279224384781243 16980766261918836577171865)
          ·
            refine ⟨12735574696439127432878899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16980766261918836577171865 12735574696439127432878899)
            ·
              refine ⟨19103362044658691149318349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12735574696439127432878899 19103362044658691149318349)
              ·
                refine ⟨7163760766747009180994381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19103362044658691149318349 7163760766747009180994381)
                ·
                  refine ⟨2686410287530128442872893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7163760766747009180994381 2686410287530128442872893)
                  ·
                    refine ⟨1007403857823798166077335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2686410287530128442872893 1007403857823798166077335)
                    ·
                      rfl

theorem cell22_2942868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2942868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942868 prefixEnd_2942868 := by exact prefixLift 2942868
  have htrace : WordTrace (prefixWord ++ tailWord_2942868) baseStart_2942868 baseEnd_2942868 := by
    simpa [prefixWord, tailWord_2942868, baseEnd_2942868] using wordTrace_append hprefix tailTrace_2942868
  have hstable : (prefixWord ++ tailWord_2942868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942868).length < 2 ^ (prefixWord ++ tailWord_2942868).sum := by decide
  have hdescent : baseEnd_2942868 < baseStart_2942868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942911 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 1, 4]
def baseStart_2942911 : Nat := 118140960795 + 2942911 * 2 ^ 59
def prefixEnd_2942911 : Nat := 4983230072969 + 3 ^ 40 * 2942911 * 2
def baseEnd_2942911 : Nat := 1007418577602560387252203

theorem tailTrace_2942911 : CollatzResearch.WordTrace tailWord_2942911 prefixEnd_2942911 1007418577602560387252203 := by
  unfold tailWord_2942911
  simp only [CollatzResearch.WordTrace]
  refine ⟨107336782241343531029148587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71557854827562354019432391 107336782241343531029148587)
  ·
    refine ⟨161005173362015296543722881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107336782241343531029148587 161005173362015296543722881)
    ·
      refine ⟨120753880021511472407792161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161005173362015296543722881 120753880021511472407792161)
      ·
        refine ⟨90565410016133604305844121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120753880021511472407792161 90565410016133604305844121)
        ·
          refine ⟨67924057512100203229383091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90565410016133604305844121 67924057512100203229383091)
          ·
            refine ⟨101886086268150304844074637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67924057512100203229383091 101886086268150304844074637)
            ·
              refine ⟨38207282350556364316527989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101886086268150304844074637 38207282350556364316527989)
              ·
                refine ⟨3581932720364659154674499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38207282350556364316527989 3581932720364659154674499)
                ·
                  refine ⟨5372899080546988732011749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3581932720364659154674499 5372899080546988732011749)
                  ·
                    refine ⟨1007418577602560387252203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5372899080546988732011749 1007418577602560387252203)
                    ·
                      rfl

theorem cell22_2942911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_2942911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942911 prefixEnd_2942911 := by exact prefixLift 2942911
  have htrace : WordTrace (prefixWord ++ tailWord_2942911) baseStart_2942911 baseEnd_2942911 := by
    simpa [prefixWord, tailWord_2942911, baseEnd_2942911] using wordTrace_append hprefix tailTrace_2942911
  have hstable : (prefixWord ++ tailWord_2942911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942911).length < 2 ^ (prefixWord ++ tailWord_2942911).sum := by decide
  have hdescent : baseEnd_2942911 < baseStart_2942911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2942958 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2942958 : Nat := 118140960795 + 2942958 * 2 ^ 59
def prefixEnd_2942958 : Nat := 4983230072969 + 3 ^ 40 * 2942958 * 2
def baseEnd_2942958 : Nat := 1007434666663067931327059

theorem tailTrace_2942958 : CollatzResearch.WordTrace tailWord_2942958 prefixEnd_2942958 1007434666663067931327059 := by
  unfold tailWord_2942958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13417312059021657257013691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71558997648115505370739685 13417312059021657257013691)
  ·
    refine ⟨20125968088532485885520537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13417312059021657257013691 20125968088532485885520537)
    ·
      refine ⟨15094476066399364414140403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20125968088532485885520537 15094476066399364414140403)
      ·
        refine ⟨22641714099599046621210605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15094476066399364414140403 22641714099599046621210605)
        ·
          refine ⟨8490642787349642482953977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22641714099599046621210605 8490642787349642482953977)
          ·
            refine ⟨6367982090512231862215483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8490642787349642482953977 6367982090512231862215483)
            ·
              refine ⟨9551973135768347793323225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6367982090512231862215483 9551973135768347793323225)
              ·
                refine ⟨7163979851826260844992419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9551973135768347793323225 7163979851826260844992419)
                ·
                  refine ⟨10745969777739391267488629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7163979851826260844992419 10745969777739391267488629)
                  ·
                    refine ⟨1007434666663067931327059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10745969777739391267488629 1007434666663067931327059)
                    ·
                      rfl

theorem cell22_2942958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2942958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2942958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2942958 prefixEnd_2942958 := by exact prefixLift 2942958
  have htrace : WordTrace (prefixWord ++ tailWord_2942958) baseStart_2942958 baseEnd_2942958 := by
    simpa [prefixWord, tailWord_2942958, baseEnd_2942958] using wordTrace_append hprefix tailTrace_2942958
  have hstable : (prefixWord ++ tailWord_2942958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2942958).length < 2 ^ (prefixWord ++ tailWord_2942958).sum := by decide
  have hdescent : baseEnd_2942958 < baseStart_2942958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2942958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943031 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 2, 5]
def baseStart_2943031 : Nat := 118140960795 + 2943031 * 2 ^ 59
def prefixEnd_2943031 : Nat := 4983230072969 + 3 ^ 40 * 2943031 * 2
def baseEnd_2943031 : Nat := 1007459656054920074251835

theorem tailTrace_2943031 : CollatzResearch.WordTrace tailWord_2943031 prefixEnd_2943031 1007459656054920074251835 := by
  unfold tailWord_2943031
  simp only [CollatzResearch.WordTrace]
  refine ⟨107341159000908791523516947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71560772667272527682344631 107341159000908791523516947)
  ·
    refine ⟨161011738501363187285275421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107341159000908791523516947 161011738501363187285275421)
    ·
      refine ⟨60379401938011195231978283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161011738501363187285275421 60379401938011195231978283)
      ·
        refine ⟨90569102907016792847967425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60379401938011195231978283 90569102907016792847967425)
        ·
          refine ⟨67926827180262594635975569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90569102907016792847967425 67926827180262594635975569)
          ·
            refine ⟨50945120385196945976981677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67926827180262594635975569 50945120385196945976981677)
            ·
              refine ⟨19104420144448854741368129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50945120385196945976981677 19104420144448854741368129)
              ·
                refine ⟨14328315108336641056026097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19104420144448854741368129 14328315108336641056026097)
                ·
                  refine ⟨10746236331252480792019573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14328315108336641056026097 10746236331252480792019573)
                  ·
                    refine ⟨1007459656054920074251835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10746236331252480792019573 1007459656054920074251835)
                    ·
                      rfl

theorem cell22_2943031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_2943031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943031 prefixEnd_2943031 := by exact prefixLift 2943031
  have htrace : WordTrace (prefixWord ++ tailWord_2943031) baseStart_2943031 baseEnd_2943031 := by
    simpa [prefixWord, tailWord_2943031, baseEnd_2943031] using wordTrace_append hprefix tailTrace_2943031
  have hstable : (prefixWord ++ tailWord_2943031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943031).length < 2 ^ (prefixWord ++ tailWord_2943031).sum := by decide
  have hdescent : baseEnd_2943031 < baseStart_2943031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943033 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 7]
def baseStart_2943033 : Nat := 118140960795 + 2943033 * 2 ^ 59
def prefixEnd_2943033 : Nat := 4983230072969 + 3 ^ 40 * 2943033 * 2
def baseEnd_2943033 : Nat := 335820113565264245233943

theorem tailTrace_2943033 : CollatzResearch.WordTrace tailWord_2943033 prefixEnd_2943033 335820113565264245233943 := by
  unfold tailWord_2943033
  simp only [CollatzResearch.WordTrace]
  refine ⟨107341231946901545865089753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71560821297934363910059835 107341231946901545865089753)
  ·
    refine ⟨80505923960176159398817315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107341231946901545865089753 80505923960176159398817315)
    ·
      refine ⟨120758885940264239098225973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80505923960176159398817315 120758885940264239098225973)
      ·
        refine ⟨11321145556899772415458685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120758885940264239098225973 11321145556899772415458685)
        ·
          refine ⟨4245429583837414655797007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11321145556899772415458685 4245429583837414655797007)
          ·
            refine ⟨6368144375756121983695511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245429583837414655797007 6368144375756121983695511)
            ·
              refine ⟨9552216563634182975543267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368144375756121983695511 9552216563634182975543267)
              ·
                refine ⟨14328324845451274463314901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9552216563634182975543267 14328324845451274463314901)
                ·
                  refine ⟨335820113565264245233943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14328324845451274463314901 335820113565264245233943)
                  ·
                    rfl

theorem cell22_2943033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_2943033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943033 prefixEnd_2943033 := by exact prefixLift 2943033
  have htrace : WordTrace (prefixWord ++ tailWord_2943033) baseStart_2943033 baseEnd_2943033 := by
    simpa [prefixWord, tailWord_2943033, baseEnd_2943033] using wordTrace_append hprefix tailTrace_2943033
  have hstable : (prefixWord ++ tailWord_2943033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943033).length < 2 ^ (prefixWord ++ tailWord_2943033).sum := by decide
  have hdescent : baseEnd_2943033 < baseStart_2943033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943063 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 1, 4]
def baseStart_2943063 : Nat := 118140960795 + 2943063 * 2 ^ 59
def prefixEnd_2943063 : Nat := 4983230072969 + 3 ^ 40 * 2943063 * 2
def baseEnd_2943063 : Nat := 1007470610308882657451737

theorem tailTrace_2943063 : CollatzResearch.WordTrace tailWord_2943063 prefixEnd_2943063 1007470610308882657451737 := by
  unfold tailWord_2943063
  simp only [CollatzResearch.WordTrace]
  refine ⟨107342326136792860988681843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71561550757861907325787895 107342326136792860988681843)
  ·
    refine ⟨161013489205189291483022765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107342326136792860988681843 161013489205189291483022765)
    ·
      refine ⟨60380058451945984306133537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161013489205189291483022765 60380058451945984306133537)
      ·
        refine ⟨45285043838959488229600153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60380058451945984306133537 45285043838959488229600153)
        ·
          refine ⟨33963782879219616172200115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45285043838959488229600153 33963782879219616172200115)
          ·
            refine ⟨50945674318829424258300173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33963782879219616172200115 50945674318829424258300173)
            ·
              refine ⟨19104627869561034096862565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50945674318829424258300173 19104627869561034096862565)
              ·
                refine ⟨3582117725542693893161731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19104627869561034096862565 3582117725542693893161731)
                ·
                  refine ⟨5373176588314040839742597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582117725542693893161731 5373176588314040839742597)
                  ·
                    refine ⟨1007470610308882657451737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373176588314040839742597 1007470610308882657451737)
                    ·
                      rfl

theorem cell22_2943063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_2943063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943063 prefixEnd_2943063 := by exact prefixLift 2943063
  have htrace : WordTrace (prefixWord ++ tailWord_2943063) baseStart_2943063 baseEnd_2943063 := by
    simpa [prefixWord, tailWord_2943063, baseEnd_2943063] using wordTrace_append hprefix tailTrace_2943063
  have hstable : (prefixWord ++ tailWord_2943063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943063).length < 2 ^ (prefixWord ++ tailWord_2943063).sum := by decide
  have hdescent : baseEnd_2943063 < baseStart_2943063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943108 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_2943108 : Nat := 118140960795 + 2943108 * 2 ^ 59
def prefixEnd_2943108 : Nat := 4983230072969 + 3 ^ 40 * 2943108 * 2
def baseEnd_2943108 : Nat := 1007486014728517540076599

theorem tailTrace_2943108 : CollatzResearch.WordTrace tailWord_2943108 prefixEnd_2943108 1007486014728517540076599 := by
  unfold tailWord_2943108
  simp only [CollatzResearch.WordTrace]
  refine ⟨53671983710814916837034989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71562644947753222449379985 53671983710814916837034989)
  ·
    refine ⟨20126993891555593813888121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53671983710814916837034989 20126993891555593813888121)
    ·
      refine ⟨15095245418666695360416091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20126993891555593813888121 15095245418666695360416091)
      ·
        refine ⟨22642868128000043040624137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15095245418666695360416091 22642868128000043040624137)
        ·
          refine ⟨16982151096000032280468103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22642868128000043040624137 16982151096000032280468103)
          ·
            refine ⟨25473226644000048420702155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16982151096000032280468103 25473226644000048420702155)
            ·
              refine ⟨38209839966000072631053233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25473226644000048420702155 38209839966000072631053233)
              ·
                refine ⟨28657379974500054473289925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38209839966000072631053233 28657379974500054473289925)
                ·
                  refine ⟨5373258745218760213741861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28657379974500054473289925 5373258745218760213741861)
                  ·
                    refine ⟨1007486014728517540076599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373258745218760213741861 1007486014728517540076599)
                    ·
                      rfl

theorem cell22_2943108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_2943108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943108 prefixEnd_2943108 := by exact prefixLift 2943108
  have htrace : WordTrace (prefixWord ++ tailWord_2943108) baseStart_2943108 baseEnd_2943108 := by
    simpa [prefixWord, tailWord_2943108, baseEnd_2943108] using wordTrace_append hprefix tailTrace_2943108
  have hstable : (prefixWord ++ tailWord_2943108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943108).length < 2 ^ (prefixWord ++ tailWord_2943108).sum := by decide
  have hdescent : baseEnd_2943108 < baseStart_2943108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943146 : List Nat := [3, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_2943146 : Nat := 118140960795 + 2943146 * 2 ^ 59
def prefixEnd_2943146 : Nat := 4983230072969 + 3 ^ 40 * 2943146 * 2
def baseEnd_2943146 : Nat := 335833007635032702542161

theorem tailTrace_2943146 : CollatzResearch.WordTrace tailWord_2943146 prefixEnd_2943146 335833007635032702542161 := by
  unfold tailWord_2943146
  simp only [CollatzResearch.WordTrace]
  refine ⟨26836338348873041540988323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71563568930328110775968861 26836338348873041540988323)
  ·
    refine ⟨40254507523309562311482485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26836338348873041540988323 40254507523309562311482485)
    ·
      refine ⟨3773860080310271466701483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40254507523309562311482485 3773860080310271466701483)
      ·
        refine ⟨5660790120465407200052225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773860080310271466701483 5660790120465407200052225)
        ·
          refine ⟨4245592590349055400039169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5660790120465407200052225 4245592590349055400039169)
          ·
            refine ⟨3184194442761791550029377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4245592590349055400039169 3184194442761791550029377)
            ·
              refine ⟨2388145832071343662522033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3184194442761791550029377 2388145832071343662522033)
              ·
                refine ⟨1791109374053507746891525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388145832071343662522033 1791109374053507746891525)
                ·
                  refine ⟨335833007635032702542161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1791109374053507746891525 335833007635032702542161)
                  ·
                    rfl

theorem cell22_2943146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_2943146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943146 prefixEnd_2943146 := by exact prefixLift 2943146
  have htrace : WordTrace (prefixWord ++ tailWord_2943146) baseStart_2943146 baseEnd_2943146 := by
    simpa [prefixWord, tailWord_2943146, baseEnd_2943146] using wordTrace_append hprefix tailTrace_2943146
  have hstable : (prefixWord ++ tailWord_2943146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943146).length < 2 ^ (prefixWord ++ tailWord_2943146).sum := by decide
  have hdescent : baseEnd_2943146 < baseStart_2943146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943157 : List Nat := [1, 3, 3, 4, 1, 2, 1, 7]
def baseStart_2943157 : Nat := 118140960795 + 2943157 * 2 ^ 59
def prefixEnd_2943157 : Nat := 4983230072969 + 3 ^ 40 * 2943157 * 2
def baseEnd_2943157 : Nat := 111944754269988638400161

theorem tailTrace_2943157 : CollatzResearch.WordTrace tailWord_2943157 prefixEnd_2943157 111944754269988638400161 := by
  unfold tailWord_2943157
  simp only [CollatzResearch.WordTrace]
  refine ⟨107345754598452315042603725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71563836398968210028402483 107345754598452315042603725)
  ·
    refine ⟨40254657974419618140976397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107345754598452315042603725 40254657974419618140976397)
    ·
      refine ⟨15095496740407356802866149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40254657974419618140976397 15095496740407356802866149)
      ·
        refine ⟨2830405638826379400537403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15095496740407356802866149 2830405638826379400537403)
        ·
          refine ⟨4245608458239569100806105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830405638826379400537403 4245608458239569100806105)
          ·
            refine ⟨3184206343679676825604579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4245608458239569100806105 3184206343679676825604579)
            ·
              refine ⟨4776309515519515238406869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184206343679676825604579 4776309515519515238406869)
              ·
                refine ⟨111944754269988638400161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4776309515519515238406869 111944754269988638400161)
                ·
                  rfl

theorem cell22_2943157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 7].length) (baseStart_2943157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943157 prefixEnd_2943157 := by exact prefixLift 2943157
  have htrace : WordTrace (prefixWord ++ tailWord_2943157) baseStart_2943157 baseEnd_2943157 := by
    simpa [prefixWord, tailWord_2943157, baseEnd_2943157] using wordTrace_append hprefix tailTrace_2943157
  have hstable : (prefixWord ++ tailWord_2943157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943157).length < 2 ^ (prefixWord ++ tailWord_2943157).sum := by decide
  have hdescent : baseEnd_2943157 < baseStart_2943157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943172 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2943172 : Nat := 118140960795 + 2943172 * 2 ^ 59
def prefixEnd_2943172 : Nat := 4983230072969 + 3 ^ 40 * 2943172 * 2
def baseEnd_2943172 : Nat := 1007507923236442706476403

theorem tailTrace_2943172 : CollatzResearch.WordTrace tailWord_2943172 prefixEnd_2943172 1007507923236442706476403 := by
  unfold tailWord_2943172
  simp only [CollatzResearch.WordTrace]
  refine ⟨53673150846698986302199885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71564201128931981736266513 53673150846698986302199885)
  ·
    refine ⟨20127431567512119863324957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53673150846698986302199885 20127431567512119863324957)
    ·
      refine ⟨7547786837817044948746859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20127431567512119863324957 7547786837817044948746859)
      ·
        refine ⟨11321680256725567423120289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7547786837817044948746859 11321680256725567423120289)
        ·
          refine ⟨8491260192544175567340217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11321680256725567423120289 8491260192544175567340217)
          ·
            refine ⟨6368445144408131675505163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8491260192544175567340217 6368445144408131675505163)
            ·
              refine ⟨9552667716612197513257745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368445144408131675505163 9552667716612197513257745)
              ·
                refine ⟨7164500787459148134943309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9552667716612197513257745 7164500787459148134943309)
                ·
                  refine ⟨2686687795297180550603741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7164500787459148134943309 2686687795297180550603741)
                  ·
                    refine ⟨1007507923236442706476403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2686687795297180550603741 1007507923236442706476403)
                    ·
                      rfl

theorem cell22_2943172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2943172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943172 prefixEnd_2943172 := by exact prefixLift 2943172
  have htrace : WordTrace (prefixWord ++ tailWord_2943172) baseStart_2943172 baseEnd_2943172 := by
    simpa [prefixWord, tailWord_2943172, baseEnd_2943172] using wordTrace_append hprefix tailTrace_2943172
  have hstable : (prefixWord ++ tailWord_2943172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943172).length < 2 ^ (prefixWord ++ tailWord_2943172).sum := by decide
  have hdescent : baseEnd_2943172 < baseStart_2943172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943230 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_2943230 : Nat := 118140960795 + 2943230 * 2 ^ 59
def prefixEnd_2943230 : Nat := 4983230072969 + 3 ^ 40 * 2943230 * 2
def baseEnd_2943230 : Nat := 335842592607249962842075

theorem tailTrace_2943230 : CollatzResearch.WordTrace tailWord_2943230 prefixEnd_2943230 335842592607249962842075 := by
  unfold tailWord_2943230
  simp only [CollatzResearch.WordTrace]
  refine ⟨13418552140898481063751393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71565611418125232340007429 13418552140898481063751393)
  ·
    refine ⟨10063914105673860797813545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13418552140898481063751393 10063914105673860797813545)
    ·
      refine ⟨7547935579255395598360159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10063914105673860797813545 7547935579255395598360159)
      ·
        refine ⟨11321903368883093397540239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7547935579255395598360159 11321903368883093397540239)
        ·
          refine ⟨16982855053324640096310359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11321903368883093397540239 16982855053324640096310359)
          ·
            refine ⟨25474282579986960144465539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16982855053324640096310359 25474282579986960144465539)
            ·
              refine ⟨38211423869980440216698309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25474282579986960144465539 38211423869980440216698309)
              ·
                refine ⟨7164641975621332540630933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38211423869980440216698309 7164641975621332540630933)
                ·
                  refine ⟨335842592607249962842075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7164641975621332540630933 335842592607249962842075)
                  ·
                    rfl

theorem cell22_2943230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_2943230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943230 prefixEnd_2943230 := by exact prefixLift 2943230
  have htrace : WordTrace (prefixWord ++ tailWord_2943230) baseStart_2943230 baseEnd_2943230 := by
    simpa [prefixWord, tailWord_2943230, baseEnd_2943230] using wordTrace_append hprefix tailTrace_2943230
  have hstable : (prefixWord ++ tailWord_2943230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943230).length < 2 ^ (prefixWord ++ tailWord_2943230).sum := by decide
  have hdescent : baseEnd_2943230 < baseStart_2943230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943243 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 1, 6]
def baseStart_2943243 : Nat := 118140960795 + 2943243 * 2 ^ 59
def prefixEnd_2943243 : Nat := 4983230072969 + 3 ^ 40 * 2943243 * 2
def baseEnd_2943243 : Nat := 1007532227987422187951185

theorem tailTrace_2943243 : CollatzResearch.WordTrace tailWord_2943243 prefixEnd_2943243 1007532227987422187951185 := by
  unfold tailWord_2943243
  simp only [CollatzResearch.WordTrace]
  refine ⟨107348891276140751730234383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71565927517427167820156255 107348891276140751730234383)
  ·
    refine ⟨161023336914211127595351575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107348891276140751730234383 161023336914211127595351575)
    ·
      refine ⟨241535005371316691393027363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161023336914211127595351575 241535005371316691393027363)
      ·
        refine ⟨362302508056975037089541045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241535005371316691393027363 362302508056975037089541045)
        ·
          refine ⟨33965860130341409727144473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 362302508056975037089541045 33965860130341409727144473)
          ·
            refine ⟨25474395097756057295358355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33965860130341409727144473 25474395097756057295358355)
            ·
              refine ⟨38211592646634085943037533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25474395097756057295358355 38211592646634085943037533)
              ·
                refine ⟨14329347242487782228639075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38211592646634085943037533 14329347242487782228639075)
                ·
                  refine ⟨21494020863731673342958613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14329347242487782228639075 21494020863731673342958613)
                  ·
                    refine ⟨1007532227987422187951185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21494020863731673342958613 1007532227987422187951185)
                    ·
                      rfl

theorem cell22_2943243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_2943243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943243 prefixEnd_2943243 := by exact prefixLift 2943243
  have htrace : WordTrace (prefixWord ++ tailWord_2943243) baseStart_2943243 baseEnd_2943243 := by
    simpa [prefixWord, tailWord_2943243, baseEnd_2943243] using wordTrace_append hprefix tailTrace_2943243
  have hstable : (prefixWord ++ tailWord_2943243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943243).length < 2 ^ (prefixWord ++ tailWord_2943243).sum := by decide
  have hdescent : baseEnd_2943243 < baseStart_2943243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943264 : List Nat := [2, 1, 1, 5, 2, 2, 3, 2, 4]
def baseStart_2943264 : Nat := 118140960795 + 2943264 * 2 ^ 59
def prefixEnd_2943264 : Nat := 4983230072969 + 3 ^ 40 * 2943264 * 2
def baseEnd_2943264 : Nat := 335846472238861711058707

theorem tailTrace_2943264 : CollatzResearch.WordTrace tailWord_2943264 prefixEnd_2943264 335846472238861711058707 := by
  unfold tailWord_2943264
  simp only [CollatzResearch.WordTrace]
  refine ⟨53674828604532336158374423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71566438139376448211165897 53674828604532336158374423)
  ·
    refine ⟨80512242906798504237561635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53674828604532336158374423 80512242906798504237561635)
    ·
      refine ⟨120768364360197756356342453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80512242906798504237561635 120768364360197756356342453)
      ·
        refine ⟨11322034158768539658407105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120768364360197756356342453 11322034158768539658407105)
        ·
          refine ⟨8491525619076404743805329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11322034158768539658407105 8491525619076404743805329)
          ·
            refine ⟨6368644214307303557853997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8491525619076404743805329 6368644214307303557853997)
            ·
              refine ⟨2388241580365238834195249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6368644214307303557853997 2388241580365238834195249)
              ·
                refine ⟨1791181185273929125646437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388241580365238834195249 1791181185273929125646437)
                ·
                  refine ⟨335846472238861711058707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1791181185273929125646437 335846472238861711058707)
                  ·
                    rfl

theorem cell22_2943264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 4].length) (baseStart_2943264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943264 prefixEnd_2943264 := by exact prefixLift 2943264
  have htrace : WordTrace (prefixWord ++ tailWord_2943264) baseStart_2943264 baseEnd_2943264 := by
    simpa [prefixWord, tailWord_2943264, baseEnd_2943264] using wordTrace_append hprefix tailTrace_2943264
  have hstable : (prefixWord ++ tailWord_2943264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943264).length < 2 ^ (prefixWord ++ tailWord_2943264).sum := by decide
  have hdescent : baseEnd_2943264 < baseStart_2943264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943335 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2943335 : Nat := 118140960795 + 2943335 * 2 ^ 59
def prefixEnd_2943335 : Nat := 4983230072969 + 3 ^ 40 * 2943335 * 2
def baseEnd_2943335 : Nat := 1007563721467564614650903

theorem tailTrace_2943335 : CollatzResearch.WordTrace tailWord_2943335 prefixEnd_2943335 1007563721467564614650903 := by
  unfold tailWord_2943335
  simp only [CollatzResearch.WordTrace]
  refine ⟨107352246791807451442583459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71568164527871634295055639 107352246791807451442583459)
  ·
    refine ⟨161028370187711177163875189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107352246791807451442583459 161028370187711177163875189)
    ·
      refine ⟨15096409705097922859113299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161028370187711177163875189 15096409705097922859113299)
      ·
        refine ⟨22644614557646884288669949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15096409705097922859113299 22644614557646884288669949)
        ·
          refine ⟨8491730459117581608251231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22644614557646884288669949 8491730459117581608251231)
          ·
            refine ⟨12737595688676372412376847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8491730459117581608251231 12737595688676372412376847)
            ·
              refine ⟨19106393533014558618565271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12737595688676372412376847 19106393533014558618565271)
              ·
                refine ⟨28659590299521837927847907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19106393533014558618565271 28659590299521837927847907)
                ·
                  refine ⟨42989385449282756891771861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28659590299521837927847907 42989385449282756891771861)
                  ·
                    refine ⟨1007563721467564614650903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42989385449282756891771861 1007563721467564614650903)
                    ·
                      rfl

theorem cell22_2943335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2943335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943335 prefixEnd_2943335 := by exact prefixLift 2943335
  have htrace : WordTrace (prefixWord ++ tailWord_2943335) baseStart_2943335 baseEnd_2943335 := by
    simpa [prefixWord, tailWord_2943335, baseEnd_2943335] using wordTrace_append hprefix tailTrace_2943335
  have hstable : (prefixWord ++ tailWord_2943335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943335).length < 2 ^ (prefixWord ++ tailWord_2943335).sum := by decide
  have hdescent : baseEnd_2943335 < baseStart_2943335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943367 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 1, 4]
def baseStart_2943367 : Nat := 118140960795 + 2943367 * 2 ^ 59
def prefixEnd_2943367 : Nat := 4983230072969 + 3 ^ 40 * 2943367 * 2
def baseEnd_2943367 : Nat := 1007574675721527197850805

theorem tailTrace_2943367 : CollatzResearch.WordTrace tailWord_2943367 prefixEnd_2943367 1007574675721527197850805 := by
  unfold tailWord_2943367
  simp only [CollatzResearch.WordTrace]
  refine ⟨107353413927691520907748355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71568942618461013938498903 107353413927691520907748355)
  ·
    refine ⟨161030120891537281361622533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107353413927691520907748355 161030120891537281361622533)
    ·
      refine ⟨30193147667163240255304225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161030120891537281361622533 30193147667163240255304225)
      ·
        refine ⟨22644860750372430191478169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30193147667163240255304225 22644860750372430191478169)
        ·
          refine ⟨16983645562779322643608627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22644860750372430191478169 16983645562779322643608627)
          ·
            refine ⟨25475468344168983965412941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16983645562779322643608627 25475468344168983965412941)
            ·
              refine ⟨9553300629063368987029853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25475468344168983965412941 9553300629063368987029853)
              ·
                refine ⟨3582487735898763370136195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9553300629063368987029853 3582487735898763370136195)
                ·
                  refine ⟨5373731603848145055204293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582487735898763370136195 5373731603848145055204293)
                  ·
                    refine ⟨1007574675721527197850805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373731603848145055204293 1007574675721527197850805)
                    ·
                      rfl

theorem cell22_2943367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_2943367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943367 prefixEnd_2943367 := by exact prefixLift 2943367
  have htrace : WordTrace (prefixWord ++ tailWord_2943367) baseStart_2943367 baseEnd_2943367 := by
    simpa [prefixWord, tailWord_2943367, baseEnd_2943367] using wordTrace_append hprefix tailTrace_2943367
  have hstable : (prefixWord ++ tailWord_2943367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943367).length < 2 ^ (prefixWord ++ tailWord_2943367).sum := by decide
  have hdescent : baseEnd_2943367 < baseStart_2943367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943395 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 1, 6]
def baseStart_2943395 : Nat := 118140960795 + 2943395 * 2 ^ 59
def prefixEnd_2943395 : Nat := 4983230072969 + 3 ^ 40 * 2943395 * 2
def baseEnd_2943395 : Nat := 1007584260693744458150719

theorem tailTrace_2943395 : CollatzResearch.WordTrace tailWord_2943395 prefixEnd_2943395 1007584260693744458150719 := by
  unfold tailWord_2943395
  simp only [CollatzResearch.WordTrace]
  refine ⟨107354435171590081689767639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71569623447726721126511759 107354435171590081689767639)
  ·
    refine ⟨161031652757385122534651459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107354435171590081689767639 161031652757385122534651459)
    ·
      refine ⟨241547479136077683801977189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161031652757385122534651459 241547479136077683801977189)
      ·
        refine ⟨45290152338014565712870723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241547479136077683801977189 45290152338014565712870723)
        ·
          refine ⟨67935228507021848569306085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45290152338014565712870723 67935228507021848569306085)
          ·
            refine ⟨12737855345066596606744891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67935228507021848569306085 12737855345066596606744891)
            ·
              refine ⟨19106783017599894910117337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12737855345066596606744891 19106783017599894910117337)
              ·
                refine ⟨14330087263199921182588003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19106783017599894910117337 14330087263199921182588003)
                ·
                  refine ⟨21495130894799881773882005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14330087263199921182588003 21495130894799881773882005)
                  ·
                    refine ⟨1007584260693744458150719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21495130894799881773882005 1007584260693744458150719)
                    ·
                      rfl

theorem cell22_2943395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_2943395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943395 prefixEnd_2943395 := by exact prefixLift 2943395
  have htrace : WordTrace (prefixWord ++ tailWord_2943395) baseStart_2943395 baseEnd_2943395 := by
    simpa [prefixWord, tailWord_2943395, baseEnd_2943395] using wordTrace_append hprefix tailTrace_2943395
  have hstable : (prefixWord ++ tailWord_2943395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943395).length < 2 ^ (prefixWord ++ tailWord_2943395).sum := by decide
  have hdescent : baseEnd_2943395 < baseStart_2943395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943410 : List Nat := [3, 2, 1, 1, 1, 1, 5, 8]
def baseStart_2943410 : Nat := 118140960795 + 2943410 * 2 ^ 59
def prefixEnd_2943410 : Nat := 4983230072969 + 3 ^ 40 * 2943410 * 2
def baseEnd_2943410 : Nat := 111954377277809935447297

theorem tailTrace_2943410 : CollatzResearch.WordTrace tailWord_2943410 prefixEnd_2943410 111954377277809935447297 := by
  unfold tailWord_2943410
  simp only [CollatzResearch.WordTrace]
  refine ⟨26838745566633934812890921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71569988177690492834375789 26838745566633934812890921)
  ·
    refine ⟨20129059174975451109668191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26838745566633934812890921 20129059174975451109668191)
    ·
      refine ⟨30193588762463176664502287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20129059174975451109668191 30193588762463176664502287)
      ·
        refine ⟨45290383143694764996753431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30193588762463176664502287 45290383143694764996753431)
        ·
          refine ⟨67935574715542147495130147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45290383143694764996753431 67935574715542147495130147)
          ·
            refine ⟨101903362073313221242695221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67935574715542147495130147 101903362073313221242695221)
            ·
              refine ⟨9553440194373114491502677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101903362073313221242695221 9553440194373114491502677)
              ·
                refine ⟨111954377277809935447297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9553440194373114491502677 111954377277809935447297)
                ·
                  rfl

theorem cell22_2943410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_2943410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943410 prefixEnd_2943410 := by exact prefixLift 2943410
  have htrace : WordTrace (prefixWord ++ tailWord_2943410) baseStart_2943410 baseEnd_2943410 := by
    simpa [prefixWord, tailWord_2943410, baseEnd_2943410] using wordTrace_append hprefix tailTrace_2943410
  have hstable : (prefixWord ++ tailWord_2943410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943410).length < 2 ^ (prefixWord ++ tailWord_2943410).sum := by decide
  have hdescent : baseEnd_2943410 < baseStart_2943410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943489 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 5]
def baseStart_2943489 : Nat := 118140960795 + 2943489 * 2 ^ 59
def prefixEnd_2943489 : Nat := 4983230072969 + 3 ^ 40 * 2943489 * 2
def baseEnd_2943489 : Nat := 335872146271586515433477

theorem tailTrace_2943489 : CollatzResearch.WordTrace tailWord_2943489 prefixEnd_2943489 335872146271586515433477 := by
  unfold tailWord_2943489
  simp only [CollatzResearch.WordTrace]
  refine ⟨107357863633249535743689521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71571909088833023829126347 107357863633249535743689521)
  ·
    refine ⟨80518397724937151807767141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107357863633249535743689521 80518397724937151807767141)
    ·
      refine ⟨15097199573425715963956339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80518397724937151807767141 15097199573425715963956339)
      ·
        refine ⟨22645799360138573945934509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15097199573425715963956339 22645799360138573945934509)
        ·
          refine ⟨8492174760051965229725441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22645799360138573945934509 8492174760051965229725441)
          ·
            refine ⟨6369131070038973922294081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8492174760051965229725441 6369131070038973922294081)
            ·
              refine ⟨4776848302529230441720561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6369131070038973922294081 4776848302529230441720561)
              ·
                refine ⟨3582636226896922831290421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4776848302529230441720561 3582636226896922831290421)
                ·
                  refine ⟨335872146271586515433477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3582636226896922831290421 335872146271586515433477)
                  ·
                    rfl

theorem cell22_2943489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_2943489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943489 prefixEnd_2943489 := by exact prefixLift 2943489
  have htrace : WordTrace (prefixWord ++ tailWord_2943489) baseStart_2943489 baseEnd_2943489 := by
    simpa [prefixWord, tailWord_2943489, baseEnd_2943489] using wordTrace_append hprefix tailTrace_2943489
  have hstable : (prefixWord ++ tailWord_2943489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943489).length < 2 ^ (prefixWord ++ tailWord_2943489).sum := by decide
  have hdescent : baseEnd_2943489 < baseStart_2943489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943517 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 8]
def baseStart_2943517 : Nat := 118140960795 + 2943517 * 2 ^ 59
def prefixEnd_2943517 : Nat := 4983230072969 + 3 ^ 40 * 2943517 * 2
def baseEnd_2943517 : Nat := 335875341262325602200115

theorem tailTrace_2943517 : CollatzResearch.WordTrace tailWord_2943517 prefixEnd_2943517 335875341262325602200115 := by
  unfold tailWord_2943517
  simp only [CollatzResearch.WordTrace]
  refine ⟨107358884877148096525708805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71572589918098731017139203 107358884877148096525708805)
  ·
    refine ⟨20129790914465268098570401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107358884877148096525708805 20129790914465268098570401)
    ·
      refine ⟨15097343185848951073927801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20129790914465268098570401 15097343185848951073927801)
      ·
        refine ⟨11323007389386713305445851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15097343185848951073927801 11323007389386713305445851)
        ·
          refine ⟨16984511084080069958168777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11323007389386713305445851 16984511084080069958168777)
          ·
            refine ⟨12738383313060052468626583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16984511084080069958168777 12738383313060052468626583)
            ·
              refine ⟨19107574969590078702939875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12738383313060052468626583 19107574969590078702939875)
              ·
                refine ⟨28661362454385118054409813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19107574969590078702939875 28661362454385118054409813)
                ·
                  refine ⟨335875341262325602200115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28661362454385118054409813 335875341262325602200115)
                  ·
                    rfl

theorem cell22_2943517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_2943517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943517 prefixEnd_2943517 := by exact prefixLift 2943517
  have htrace : WordTrace (prefixWord ++ tailWord_2943517) baseStart_2943517 baseEnd_2943517 := by
    simpa [prefixWord, tailWord_2943517, baseEnd_2943517] using wordTrace_append hprefix tailTrace_2943517
  have hstable : (prefixWord ++ tailWord_2943517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943517).length < 2 ^ (prefixWord ++ tailWord_2943517).sum := by decide
  have hdescent : baseEnd_2943517 < baseStart_2943517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943540 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2943540 : Nat := 118140960795 + 2943540 * 2 ^ 59
def prefixEnd_2943540 : Nat := 4983230072969 + 3 ^ 40 * 2943540 * 2
def baseEnd_2943540 : Nat := 335877965719004137758425

theorem tailTrace_2943540 : CollatzResearch.WordTrace tailWord_2943540 prefixEnd_2943540 335877965719004137758425 := by
  unfold tailWord_2943540
  simp only [CollatzResearch.WordTrace]
  refine ⟨53679861878032385726898037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71573149170709847635864049 53679861878032385726898037)
  ·
    refine ⟨5032487051065536161896691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53679861878032385726898037 5032487051065536161896691)
    ·
      refine ⟨7548730576598304242845037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5032487051065536161896691 7548730576598304242845037)
      ·
        refine ⟨2830773966224364091066889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7548730576598304242845037 2830773966224364091066889)
        ·
          refine ⟨2123080474668273068300167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2830773966224364091066889 2123080474668273068300167)
          ·
            refine ⟨3184620712002409602450251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123080474668273068300167 3184620712002409602450251)
            ·
              refine ⟨4776931068003614403675377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184620712002409602450251 4776931068003614403675377)
              ·
                refine ⟨3582698301002710802756533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4776931068003614403675377 3582698301002710802756533)
                ·
                  refine ⟨335877965719004137758425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3582698301002710802756533 335877965719004137758425)
                  ·
                    rfl

theorem cell22_2943540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2943540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943540 prefixEnd_2943540 := by exact prefixLift 2943540
  have htrace : WordTrace (prefixWord ++ tailWord_2943540) baseStart_2943540 baseEnd_2943540 := by
    simpa [prefixWord, tailWord_2943540, baseEnd_2943540] using wordTrace_append hprefix tailTrace_2943540
  have hstable : (prefixWord ++ tailWord_2943540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943540).length < 2 ^ (prefixWord ++ tailWord_2943540).sum := by decide
  have hdescent : baseEnd_2943540 < baseStart_2943540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943607 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 7]
def baseStart_2943607 : Nat := 118140960795 + 2943607 * 2 ^ 59
def prefixEnd_2943607 : Nat := 4983230072969 + 3 ^ 40 * 2943607 * 2
def baseEnd_2943607 : Nat := 335885610875415523950023

theorem tailTrace_2943607 : CollatzResearch.WordTrace tailWord_2943607 prefixEnd_2943607 335885610875415523950023 := by
  unfold tailWord_2943607
  simp only [CollatzResearch.WordTrace]
  refine ⟨107362167446822041896485075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71574778297881361264323383 107362167446822041896485075)
  ·
    refine ⟨161043251170233062844727613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107362167446822041896485075 161043251170233062844727613)
    ·
      refine ⟨60391219188837398566772855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161043251170233062844727613 60391219188837398566772855)
      ·
        refine ⟨90586828783256097850159283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60391219188837398566772855 90586828783256097850159283)
        ·
          refine ⟨135880243174884146775238925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90586828783256097850159283 135880243174884146775238925)
          ·
            refine ⟨50955091190581555040714597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135880243174884146775238925 50955091190581555040714597)
            ·
              refine ⟨9554079598234041570133987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50955091190581555040714597 9554079598234041570133987)
              ·
                refine ⟨14331119397351062355200981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9554079598234041570133987 14331119397351062355200981)
                ·
                  refine ⟨335885610875415523950023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14331119397351062355200981 335885610875415523950023)
                  ·
                    rfl

theorem cell22_2943607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 7].length) (baseStart_2943607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943607 prefixEnd_2943607 := by exact prefixLift 2943607
  have htrace : WordTrace (prefixWord ++ tailWord_2943607) baseStart_2943607 baseEnd_2943607 := by
    simpa [prefixWord, tailWord_2943607, baseEnd_2943607] using wordTrace_append hprefix tailTrace_2943607
  have hstable : (prefixWord ++ tailWord_2943607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943607).length < 2 ^ (prefixWord ++ tailWord_2943607).sum := by decide
  have hdescent : baseEnd_2943607 < baseStart_2943607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943662 : List Nat := [4, 1, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2943662 : Nat := 118140960795 + 2943662 * 2 ^ 59
def prefixEnd_2943662 : Nat := 4983230072969 + 3 ^ 40 * 2943662 * 2
def baseEnd_2943662 : Nat := 1007675660250244761724901

theorem tailTrace_2943662 : CollatzResearch.WordTrace tailWord_2943662 prefixEnd_2943662 1007675660250244761724901 := by
  unfold tailWord_2943662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13420521682702848286217155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71576115641081857526491493 13420521682702848286217155)
  ·
    refine ⟨20130782524054272429325733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13420521682702848286217155 20130782524054272429325733)
    ·
      refine ⟨3774521723260176080498575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20130782524054272429325733 3774521723260176080498575)
      ·
        refine ⟨5661782584890264120747863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3774521723260176080498575 5661782584890264120747863)
        ·
          refine ⟨8492673877335396181121795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5661782584890264120747863 8492673877335396181121795)
          ·
            refine ⟨12739010816003094271682693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492673877335396181121795 12739010816003094271682693)
            ·
              refine ⟨2388564528000580175940505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12739010816003094271682693 2388564528000580175940505)
              ·
                refine ⟨1791423396000435131955379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388564528000580175940505 1791423396000435131955379)
                ·
                  refine ⟨2687135094000652697933069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791423396000435131955379 2687135094000652697933069)
                  ·
                    refine ⟨1007675660250244761724901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687135094000652697933069 1007675660250244761724901)
                    ·
                      rfl

theorem cell22_2943662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2943662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943662 prefixEnd_2943662 := by exact prefixLift 2943662
  have htrace : WordTrace (prefixWord ++ tailWord_2943662) baseStart_2943662 baseEnd_2943662 := by
    simpa [prefixWord, tailWord_2943662, baseEnd_2943662] using wordTrace_append hprefix tailTrace_2943662
  have hstable : (prefixWord ++ tailWord_2943662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943662).length < 2 ^ (prefixWord ++ tailWord_2943662).sum := by decide
  have hdescent : baseEnd_2943662 < baseStart_2943662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943780 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_2943780 : Nat := 118140960795 + 2943780 * 2 ^ 59
def prefixEnd_2943780 : Nat := 4983230072969 + 3 ^ 40 * 2943780 * 2
def baseEnd_2943780 : Nat := 1007716054061731787274539

theorem tailTrace_2943780 : CollatzResearch.WordTrace tailWord_2943780 prefixEnd_2943780 1007716054061731787274539 := by
  unfold tailWord_2943780
  simp only [CollatzResearch.WordTrace]
  refine ⟨53684238637597646221266397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71578984850130194961688529 53684238637597646221266397)
  ·
    refine ⟨20131589489099117332974899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53684238637597646221266397 20131589489099117332974899)
    ·
      refine ⟨30197384233648675999462349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20131589489099117332974899 30197384233648675999462349)
      ·
        refine ⟨11324019087618253499798381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30197384233648675999462349 11324019087618253499798381)
        ·
          refine ⟨4246507157856845062424393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11324019087618253499798381 4246507157856845062424393)
          ·
            refine ⟨3184880368392633796818295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4246507157856845062424393 3184880368392633796818295)
            ·
              refine ⟨4777320552588950695227443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184880368392633796818295 4777320552588950695227443)
              ·
                refine ⟨7165980828883426042841165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4777320552588950695227443 7165980828883426042841165)
                ·
                  refine ⟨2687242810831284766065437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7165980828883426042841165 2687242810831284766065437)
                  ·
                    refine ⟨1007716054061731787274539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687242810831284766065437 1007716054061731787274539)
                    ·
                      rfl

theorem cell22_2943780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_2943780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943780 prefixEnd_2943780 := by exact prefixLift 2943780
  have htrace : WordTrace (prefixWord ++ tailWord_2943780) baseStart_2943780 baseEnd_2943780 := by
    simpa [prefixWord, tailWord_2943780, baseEnd_2943780] using wordTrace_append hprefix tailTrace_2943780
  have hstable : (prefixWord ++ tailWord_2943780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943780).length < 2 ^ (prefixWord ++ tailWord_2943780).sum := by decide
  have hdescent : baseEnd_2943780 < baseStart_2943780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943804 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 8]
def baseStart_2943804 : Nat := 118140960795 + 2943804 * 2 ^ 59
def prefixEnd_2943804 : Nat := 4983230072969 + 3 ^ 40 * 2943804 * 2
def baseEnd_2943804 : Nat := 335908089917401241558155

theorem tailTrace_2943804 : CollatzResearch.WordTrace tailWord_2943804 prefixEnd_2943804 335908089917401241558155 := by
  unfold tailWord_2943804
  simp only [CollatzResearch.WordTrace]
  refine ⟨53684676313554172270703233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71579568418072229694270977 53684676313554172270703233)
  ·
    refine ⟨40263507235165629203027425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53684676313554172270703233 40263507235165629203027425)
    ·
      refine ⟨30197630426374221902270569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40263507235165629203027425 30197630426374221902270569)
      ·
        refine ⟨22648222819780666426702927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30197630426374221902270569 22648222819780666426702927)
        ·
          refine ⟨33972334229670999640054391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22648222819780666426702927 33972334229670999640054391)
          ·
            refine ⟨50958501344506499460081587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33972334229670999640054391 50958501344506499460081587)
            ·
              refine ⟨76437752016759749190122381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50958501344506499460081587 76437752016759749190122381)
              ·
                refine ⟨28664157006284905946295893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76437752016759749190122381 28664157006284905946295893)
                ·
                  refine ⟨335908089917401241558155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28664157006284905946295893 335908089917401241558155)
                  ·
                    rfl

theorem cell22_2943804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_2943804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943804 prefixEnd_2943804 := by exact prefixLift 2943804
  have htrace : WordTrace (prefixWord ++ tailWord_2943804) baseStart_2943804 baseEnd_2943804 := by
    simpa [prefixWord, tailWord_2943804, baseEnd_2943804] using wordTrace_append hprefix tailTrace_2943804
  have hstable : (prefixWord ++ tailWord_2943804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943804).length < 2 ^ (prefixWord ++ tailWord_2943804).sum := by decide
  have hdescent : baseEnd_2943804 < baseStart_2943804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943864 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_2943864 : Nat := 118140960795 + 2943864 * 2 ^ 59
def prefixEnd_2943864 : Nat := 4983230072969 + 3 ^ 40 * 2943864 * 2
def baseEnd_2943864 : Nat := 1007744808978383568174281

theorem tailTrace_2943864 : CollatzResearch.WordTrace tailWord_2943864 prefixEnd_2943864 1007744808978383568174281 := by
  unfold tailWord_2943864
  simp only [CollatzResearch.WordTrace]
  refine ⟨53685770503445487394295323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71581027337927316525727097 53685770503445487394295323)
  ·
    refine ⟨80528655755168231091442985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53685770503445487394295323 80528655755168231091442985)
    ·
      refine ⟨60396491816376173318582239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80528655755168231091442985 60396491816376173318582239)
      ·
        refine ⟨90594737724564259977873359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60396491816376173318582239 90594737724564259977873359)
        ·
          refine ⟨135892106586846389966810039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90594737724564259977873359 135892106586846389966810039)
          ·
            refine ⟨203838159880269584950215059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135892106586846389966810039 203838159880269584950215059)
            ·
              refine ⟨305757239820404377425322589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203838159880269584950215059 305757239820404377425322589)
              ·
                refine ⟨114658964932651641534495971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305757239820404377425322589 114658964932651641534495971)
                ·
                  refine ⟨171988447398977462301743957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114658964932651641534495971 171988447398977462301743957)
                  ·
                    refine ⟨1007744808978383568174281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 171988447398977462301743957 1007744808978383568174281)
                    ·
                      rfl

theorem cell22_2943864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_2943864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943864 prefixEnd_2943864 := by exact prefixLift 2943864
  have htrace : WordTrace (prefixWord ++ tailWord_2943864) baseStart_2943864 baseEnd_2943864 := by
    simpa [prefixWord, tailWord_2943864, baseEnd_2943864] using wordTrace_append hprefix tailTrace_2943864
  have hstable : (prefixWord ++ tailWord_2943864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943864).length < 2 ^ (prefixWord ++ tailWord_2943864).sum := by decide
  have hdescent : baseEnd_2943864 < baseStart_2943864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943917 : List Nat := [1, 5, 2, 3, 1, 2, 2, 6]
def baseStart_2943917 : Nat := 118140960795 + 2943917 * 2 ^ 59
def prefixEnd_2943917 : Nat := 4983230072969 + 3 ^ 40 * 2943917 * 2
def baseEnd_2943917 : Nat := 111973661329056566288791

theorem tailTrace_2943917 : CollatzResearch.WordTrace tailWord_2943917 prefixEnd_2943917 111973661329056566288791 := by
  unfold tailWord_2943917
  simp only [CollatzResearch.WordTrace]
  refine ⟨107373474075698964840270005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71582316050465976560180003 107373474075698964840270005)
  ·
    refine ⟨10066263194596777953775313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107373474075698964840270005 10066263194596777953775313)
    ·
      refine ⟨7549697395947583465331485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10066263194596777953775313 7549697395947583465331485)
      ·
        refine ⟨2831136523480343799499307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7549697395947583465331485 2831136523480343799499307)
        ·
          refine ⟨4246704785220515699248961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831136523480343799499307 4246704785220515699248961)
          ·
            refine ⟨3185028588915386774436721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4246704785220515699248961 3185028588915386774436721)
            ·
              refine ⟨2388771441686540080827541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185028588915386774436721 2388771441686540080827541)
              ·
                refine ⟨111973661329056566288791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2388771441686540080827541 111973661329056566288791)
                ·
                  rfl

theorem cell22_2943917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 6].length) (baseStart_2943917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943917 prefixEnd_2943917 := by exact prefixLift 2943917
  have htrace : WordTrace (prefixWord ++ tailWord_2943917) baseStart_2943917 baseEnd_2943917 := by
    simpa [prefixWord, tailWord_2943917, baseEnd_2943917] using wordTrace_append hprefix tailTrace_2943917
  have hstable : (prefixWord ++ tailWord_2943917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943917).length < 2 ^ (prefixWord ++ tailWord_2943917).sum := by decide
  have hdescent : baseEnd_2943917 < baseStart_2943917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2943975 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 1, 4]
def baseStart_2943975 : Nat := 118140960795 + 2943975 * 2 ^ 59
def prefixEnd_2943975 : Nat := 4983230072969 + 3 ^ 40 * 2943975 * 2
def baseEnd_2943975 : Nat := 1007782806546816278648941

theorem tailTrace_2943975 : CollatzResearch.WordTrace tailWord_2943975 prefixEnd_2943975 1007782806546816278648941 := by
  unfold tailWord_2943975
  simp only [CollatzResearch.WordTrace]
  refine ⟨107375589509488840745881379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71583726339659227163920919 107375589509488840745881379)
  ·
    refine ⟨161063384264233261118822069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107375589509488840745881379 161063384264233261118822069)
    ·
      refine ⟨15099692274771868229889569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161063384264233261118822069 15099692274771868229889569)
      ·
        refine ⟨11324769206078901172417177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15099692274771868229889569 11324769206078901172417177)
        ·
          refine ⟨8493576904559175879312883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11324769206078901172417177 8493576904559175879312883)
          ·
            refine ⟨12740365356838763818969325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8493576904559175879312883 12740365356838763818969325)
            ·
              refine ⟨4777637008814536432113497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12740365356838763818969325 4777637008814536432113497)
              ·
                refine ⟨3583227756610902324085123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4777637008814536432113497 3583227756610902324085123)
                ·
                  refine ⟨5374841634916353486127685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583227756610902324085123 5374841634916353486127685)
                  ·
                    refine ⟨1007782806546816278648941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5374841634916353486127685 1007782806546816278648941)
                    ·
                      rfl

theorem cell22_2943975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_2943975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2943975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2943975 prefixEnd_2943975 := by exact prefixLift 2943975
  have htrace : WordTrace (prefixWord ++ tailWord_2943975) baseStart_2943975 baseEnd_2943975 := by
    simpa [prefixWord, tailWord_2943975, baseEnd_2943975] using wordTrace_append hprefix tailTrace_2943975
  have hstable : (prefixWord ++ tailWord_2943975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2943975).length < 2 ^ (prefixWord ++ tailWord_2943975).sum := by decide
  have hdescent : baseEnd_2943975 < baseStart_2943975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2943975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944001 : List Nat := [1, 2, 4, 1, 2, 12]
def baseStart_2944001 : Nat := 118140960795 + 2944001 * 2 ^ 59
def prefixEnd_2944001 : Nat := 4983230072969 + 3 ^ 40 * 2944001 * 2
def baseEnd_2944001 : Nat := 12441872924421739228381

theorem tailTrace_2944001 : CollatzResearch.WordTrace tailWord_2944001 prefixEnd_2944001 12441872924421739228381 := by
  unfold tailWord_2944001
  simp only [CollatzResearch.WordTrace]
  refine ⟨107376537807394647186327857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71584358538263098124218571 107376537807394647186327857)
  ·
    refine ⟨80532403355545985389745893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107376537807394647186327857 80532403355545985389745893)
    ·
      refine ⟨15099825629164872260577355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80532403355545985389745893 15099825629164872260577355)
      ·
        refine ⟨22649738443747308390866033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15099825629164872260577355 22649738443747308390866033)
        ·
          refine ⟨16987303832810481293149525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22649738443747308390866033 16987303832810481293149525)
          ·
            refine ⟨12441872924421739228381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16987303832810481293149525 12441872924421739228381)
            ·
              rfl

theorem cell22_2944001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 12].length) (baseStart_2944001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944001 prefixEnd_2944001 := by exact prefixLift 2944001
  have htrace : WordTrace (prefixWord ++ tailWord_2944001) baseStart_2944001 baseEnd_2944001 := by
    simpa [prefixWord, tailWord_2944001, baseEnd_2944001] using wordTrace_append hprefix tailTrace_2944001
  have hstable : (prefixWord ++ tailWord_2944001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944001).length < 2 ^ (prefixWord ++ tailWord_2944001).sum := by decide
  have hdescent : baseEnd_2944001 < baseStart_2944001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944005 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 2, 3]
def baseStart_2944005 : Nat := 118140960795 + 2944005 * 2 ^ 59
def prefixEnd_2944005 : Nat := 4983230072969 + 3 ^ 40 * 2944005 * 2
def baseEnd_2944005 : Nat := 1007793076159906200398849

theorem tailTrace_2944005 : CollatzResearch.WordTrace tailWord_2944005 prefixEnd_2944005 1007793076159906200398849 := by
  unfold tailWord_2944005
  simp only [CollatzResearch.WordTrace]
  refine ⟨107376683699380155869473469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71584455799586770579648979 107376683699380155869473469)
  ·
    refine ⟨40266256387267558451052551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107376683699380155869473469 40266256387267558451052551)
    ·
      refine ⟨60399384580901337676578827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40266256387267558451052551 60399384580901337676578827)
      ·
        refine ⟨90599076871352006514868241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60399384580901337676578827 90599076871352006514868241)
        ·
          refine ⟨67949307653514004886151181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90599076871352006514868241 67949307653514004886151181)
          ·
            refine ⟨25480990370067751832306693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67949307653514004886151181 25480990370067751832306693)
            ·
              refine ⟨4777685694387703468557505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25480990370067751832306693 4777685694387703468557505)
              ·
                refine ⟨3583264270790777601418129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4777685694387703468557505 3583264270790777601418129)
                ·
                  refine ⟨2687448203093083201063597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3583264270790777601418129 2687448203093083201063597)
                  ·
                    refine ⟨1007793076159906200398849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687448203093083201063597 1007793076159906200398849)
                    ·
                      rfl

theorem cell22_2944005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_2944005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944005 prefixEnd_2944005 := by exact prefixLift 2944005
  have htrace : WordTrace (prefixWord ++ tailWord_2944005) baseStart_2944005 baseEnd_2944005 := by
    simpa [prefixWord, tailWord_2944005, baseEnd_2944005] using wordTrace_append hprefix tailTrace_2944005
  have hstable : (prefixWord ++ tailWord_2944005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944005).length < 2 ^ (prefixWord ++ tailWord_2944005).sum := by decide
  have hdescent : baseEnd_2944005 < baseStart_2944005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2944078 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_2944078 : Nat := 118140960795 + 2944078 * 2 ^ 59
def prefixEnd_2944078 : Nat := 4983230072969 + 3 ^ 40 * 2944078 * 2
def baseEnd_2944078 : Nat := 1007818065551758343323625

theorem tailTrace_2944078 : CollatzResearch.WordTrace tailWord_2944078 prefixEnd_2944078 1007818065551758343323625 := by
  unfold tailWord_2944078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13422418278514461167110111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71586230818743792891253925 13422418278514461167110111)
  ·
    refine ⟨20133627417771691750665167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13422418278514461167110111 20133627417771691750665167)
    ·
      refine ⟨30200441126657537625997751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20133627417771691750665167 30200441126657537625997751)
      ·
        refine ⟨45300661689986306438996627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30200441126657537625997751 45300661689986306438996627)
        ·
          refine ⟨67950992534979459658494941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45300661689986306438996627 67950992534979459658494941)
          ·
            refine ⟨25481622200617297371935603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67950992534979459658494941 25481622200617297371935603)
            ·
              refine ⟨38222433300925946057903405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25481622200617297371935603 38222433300925946057903405)
              ·
                refine ⟨14333412487847229771713777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38222433300925946057903405 14333412487847229771713777)
                ·
                  refine ⟨10750059365885422328785333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14333412487847229771713777 10750059365885422328785333)
                  ·
                    refine ⟨1007818065551758343323625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10750059365885422328785333 1007818065551758343323625)
                    ·
                      rfl

theorem cell22_2944078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_2944078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2944078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2944078 prefixEnd_2944078 := by exact prefixLift 2944078
  have htrace : WordTrace (prefixWord ++ tailWord_2944078) baseStart_2944078 baseEnd_2944078 := by
    simpa [prefixWord, tailWord_2944078, baseEnd_2944078] using wordTrace_append hprefix tailTrace_2944078
  have hstable : (prefixWord ++ tailWord_2944078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2944078).length < 2 ^ (prefixWord ++ tailWord_2944078).sum := by decide
  have hdescent : baseEnd_2944078 < baseStart_2944078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2944078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
